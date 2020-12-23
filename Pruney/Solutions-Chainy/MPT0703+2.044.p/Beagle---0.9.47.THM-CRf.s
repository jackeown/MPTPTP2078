%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:14 EST 2020

% Result     : Theorem 3.17s
% Output     : CNFRefutation 3.17s
% Verified   : 
% Statistics : Number of formulae       :   44 (  53 expanded)
%              Number of leaves         :   21 (  28 expanded)
%              Depth                    :    7
%              Number of atoms          :   62 (  92 expanded)
%              Number of equality atoms :   23 (  26 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k6_subset_1 > k4_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_29,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_66,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( ( r1_tarski(k10_relat_1(C,A),k10_relat_1(C,B))
            & r1_tarski(A,k2_relat_1(C)) )
         => r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t158_funct_1)).

tff(f_39,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => k10_relat_1(C,k6_subset_1(A,B)) = k6_subset_1(k10_relat_1(C,A),k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_funct_1)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ~ ( A != k1_xboole_0
          & r1_tarski(A,k2_relat_1(B))
          & k10_relat_1(B,A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t174_relat_1)).

tff(c_36,plain,(
    ! [A_19,B_20] :
      ( r1_tarski(A_19,B_20)
      | k4_xboole_0(A_19,B_20) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_16,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_40,plain,(
    k4_xboole_0('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_36,c_16])).

tff(c_24,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_22,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_10,plain,(
    ! [A_8,B_9] : k6_subset_1(A_8,B_9) = k4_xboole_0(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_14,plain,(
    ! [C_14,A_12,B_13] :
      ( k6_subset_1(k10_relat_1(C_14,A_12),k10_relat_1(C_14,B_13)) = k10_relat_1(C_14,k6_subset_1(A_12,B_13))
      | ~ v1_funct_1(C_14)
      | ~ v1_relat_1(C_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_413,plain,(
    ! [C_43,A_44,B_45] :
      ( k4_xboole_0(k10_relat_1(C_43,A_44),k10_relat_1(C_43,B_45)) = k10_relat_1(C_43,k4_xboole_0(A_44,B_45))
      | ~ v1_funct_1(C_43)
      | ~ v1_relat_1(C_43) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_10,c_14])).

tff(c_20,plain,(
    r1_tarski(k10_relat_1('#skF_3','#skF_1'),k10_relat_1('#skF_3','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_41,plain,(
    ! [A_21,B_22] :
      ( k4_xboole_0(A_21,B_22) = k1_xboole_0
      | ~ r1_tarski(A_21,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_54,plain,(
    k4_xboole_0(k10_relat_1('#skF_3','#skF_1'),k10_relat_1('#skF_3','#skF_2')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_20,c_41])).

tff(c_422,plain,
    ( k10_relat_1('#skF_3',k4_xboole_0('#skF_1','#skF_2')) = k1_xboole_0
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_413,c_54])).

tff(c_439,plain,(
    k10_relat_1('#skF_3',k4_xboole_0('#skF_1','#skF_2')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_422])).

tff(c_8,plain,(
    ! [A_6,B_7] : r1_tarski(k4_xboole_0(A_6,B_7),A_6) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_18,plain,(
    r1_tarski('#skF_1',k2_relat_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_88,plain,(
    ! [A_23,C_24,B_25] :
      ( r1_tarski(A_23,C_24)
      | ~ r1_tarski(B_25,C_24)
      | ~ r1_tarski(A_23,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_106,plain,(
    ! [A_23] :
      ( r1_tarski(A_23,k2_relat_1('#skF_3'))
      | ~ r1_tarski(A_23,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_18,c_88])).

tff(c_264,plain,(
    ! [B_36,A_37] :
      ( k10_relat_1(B_36,A_37) != k1_xboole_0
      | ~ r1_tarski(A_37,k2_relat_1(B_36))
      | k1_xboole_0 = A_37
      | ~ v1_relat_1(B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_267,plain,(
    ! [A_23] :
      ( k10_relat_1('#skF_3',A_23) != k1_xboole_0
      | k1_xboole_0 = A_23
      | ~ v1_relat_1('#skF_3')
      | ~ r1_tarski(A_23,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_106,c_264])).

tff(c_957,plain,(
    ! [A_73] :
      ( k10_relat_1('#skF_3',A_73) != k1_xboole_0
      | k1_xboole_0 = A_73
      | ~ r1_tarski(A_73,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_267])).

tff(c_1437,plain,(
    ! [B_98] :
      ( k10_relat_1('#skF_3',k4_xboole_0('#skF_1',B_98)) != k1_xboole_0
      | k4_xboole_0('#skF_1',B_98) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_957])).

tff(c_1444,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_439,c_1437])).

tff(c_1453,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_1444])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n004.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 09:21:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.17/1.50  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.17/1.51  
% 3.17/1.51  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.17/1.51  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k6_subset_1 > k4_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.17/1.51  
% 3.17/1.51  %Foreground sorts:
% 3.17/1.51  
% 3.17/1.51  
% 3.17/1.51  %Background operators:
% 3.17/1.51  
% 3.17/1.51  
% 3.17/1.51  %Foreground operators:
% 3.17/1.51  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.17/1.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.17/1.51  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.17/1.51  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.17/1.51  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.17/1.51  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.17/1.51  tff('#skF_2', type, '#skF_2': $i).
% 3.17/1.51  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 3.17/1.51  tff('#skF_3', type, '#skF_3': $i).
% 3.17/1.51  tff('#skF_1', type, '#skF_1': $i).
% 3.17/1.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.17/1.51  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.17/1.51  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.17/1.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.17/1.51  
% 3.17/1.52  tff(f_29, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 3.17/1.52  tff(f_66, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r1_tarski(k10_relat_1(C, A), k10_relat_1(C, B)) & r1_tarski(A, k2_relat_1(C))) => r1_tarski(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t158_funct_1)).
% 3.17/1.52  tff(f_39, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 3.17/1.52  tff(f_55, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (k10_relat_1(C, k6_subset_1(A, B)) = k6_subset_1(k10_relat_1(C, A), k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t138_funct_1)).
% 3.17/1.52  tff(f_37, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 3.17/1.52  tff(f_35, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 3.17/1.52  tff(f_49, axiom, (![A, B]: (v1_relat_1(B) => ~((~(A = k1_xboole_0) & r1_tarski(A, k2_relat_1(B))) & (k10_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t174_relat_1)).
% 3.17/1.52  tff(c_36, plain, (![A_19, B_20]: (r1_tarski(A_19, B_20) | k4_xboole_0(A_19, B_20)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.17/1.52  tff(c_16, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.17/1.52  tff(c_40, plain, (k4_xboole_0('#skF_1', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_36, c_16])).
% 3.17/1.52  tff(c_24, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.17/1.52  tff(c_22, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.17/1.52  tff(c_10, plain, (![A_8, B_9]: (k6_subset_1(A_8, B_9)=k4_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.17/1.52  tff(c_14, plain, (![C_14, A_12, B_13]: (k6_subset_1(k10_relat_1(C_14, A_12), k10_relat_1(C_14, B_13))=k10_relat_1(C_14, k6_subset_1(A_12, B_13)) | ~v1_funct_1(C_14) | ~v1_relat_1(C_14))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.17/1.52  tff(c_413, plain, (![C_43, A_44, B_45]: (k4_xboole_0(k10_relat_1(C_43, A_44), k10_relat_1(C_43, B_45))=k10_relat_1(C_43, k4_xboole_0(A_44, B_45)) | ~v1_funct_1(C_43) | ~v1_relat_1(C_43))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_10, c_14])).
% 3.17/1.52  tff(c_20, plain, (r1_tarski(k10_relat_1('#skF_3', '#skF_1'), k10_relat_1('#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.17/1.52  tff(c_41, plain, (![A_21, B_22]: (k4_xboole_0(A_21, B_22)=k1_xboole_0 | ~r1_tarski(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.17/1.52  tff(c_54, plain, (k4_xboole_0(k10_relat_1('#skF_3', '#skF_1'), k10_relat_1('#skF_3', '#skF_2'))=k1_xboole_0), inference(resolution, [status(thm)], [c_20, c_41])).
% 3.17/1.52  tff(c_422, plain, (k10_relat_1('#skF_3', k4_xboole_0('#skF_1', '#skF_2'))=k1_xboole_0 | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_413, c_54])).
% 3.17/1.52  tff(c_439, plain, (k10_relat_1('#skF_3', k4_xboole_0('#skF_1', '#skF_2'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_422])).
% 3.17/1.52  tff(c_8, plain, (![A_6, B_7]: (r1_tarski(k4_xboole_0(A_6, B_7), A_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.17/1.52  tff(c_18, plain, (r1_tarski('#skF_1', k2_relat_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.17/1.52  tff(c_88, plain, (![A_23, C_24, B_25]: (r1_tarski(A_23, C_24) | ~r1_tarski(B_25, C_24) | ~r1_tarski(A_23, B_25))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.17/1.52  tff(c_106, plain, (![A_23]: (r1_tarski(A_23, k2_relat_1('#skF_3')) | ~r1_tarski(A_23, '#skF_1'))), inference(resolution, [status(thm)], [c_18, c_88])).
% 3.17/1.52  tff(c_264, plain, (![B_36, A_37]: (k10_relat_1(B_36, A_37)!=k1_xboole_0 | ~r1_tarski(A_37, k2_relat_1(B_36)) | k1_xboole_0=A_37 | ~v1_relat_1(B_36))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.17/1.52  tff(c_267, plain, (![A_23]: (k10_relat_1('#skF_3', A_23)!=k1_xboole_0 | k1_xboole_0=A_23 | ~v1_relat_1('#skF_3') | ~r1_tarski(A_23, '#skF_1'))), inference(resolution, [status(thm)], [c_106, c_264])).
% 3.17/1.52  tff(c_957, plain, (![A_73]: (k10_relat_1('#skF_3', A_73)!=k1_xboole_0 | k1_xboole_0=A_73 | ~r1_tarski(A_73, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_267])).
% 3.17/1.52  tff(c_1437, plain, (![B_98]: (k10_relat_1('#skF_3', k4_xboole_0('#skF_1', B_98))!=k1_xboole_0 | k4_xboole_0('#skF_1', B_98)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_957])).
% 3.17/1.52  tff(c_1444, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_439, c_1437])).
% 3.17/1.52  tff(c_1453, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_1444])).
% 3.17/1.52  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.17/1.52  
% 3.17/1.52  Inference rules
% 3.17/1.52  ----------------------
% 3.17/1.52  #Ref     : 0
% 3.17/1.52  #Sup     : 349
% 3.17/1.52  #Fact    : 0
% 3.17/1.52  #Define  : 0
% 3.17/1.52  #Split   : 2
% 3.17/1.52  #Chain   : 0
% 3.17/1.52  #Close   : 0
% 3.17/1.52  
% 3.17/1.52  Ordering : KBO
% 3.17/1.52  
% 3.17/1.52  Simplification rules
% 3.17/1.52  ----------------------
% 3.17/1.52  #Subsume      : 45
% 3.17/1.52  #Demod        : 230
% 3.17/1.52  #Tautology    : 184
% 3.17/1.52  #SimpNegUnit  : 3
% 3.17/1.52  #BackRed      : 1
% 3.17/1.52  
% 3.17/1.52  #Partial instantiations: 0
% 3.17/1.52  #Strategies tried      : 1
% 3.17/1.52  
% 3.17/1.52  Timing (in seconds)
% 3.17/1.52  ----------------------
% 3.31/1.52  Preprocessing        : 0.30
% 3.31/1.52  Parsing              : 0.16
% 3.31/1.52  CNF conversion       : 0.02
% 3.31/1.52  Main loop            : 0.44
% 3.31/1.52  Inferencing          : 0.16
% 3.31/1.52  Reduction            : 0.15
% 3.31/1.52  Demodulation         : 0.11
% 3.31/1.52  BG Simplification    : 0.02
% 3.31/1.52  Subsumption          : 0.08
% 3.31/1.52  Abstraction          : 0.02
% 3.31/1.52  MUC search           : 0.00
% 3.31/1.52  Cooper               : 0.00
% 3.31/1.52  Total                : 0.77
% 3.31/1.53  Index Insertion      : 0.00
% 3.31/1.53  Index Deletion       : 0.00
% 3.31/1.53  Index Matching       : 0.00
% 3.31/1.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------
