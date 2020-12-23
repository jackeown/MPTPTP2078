%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:08 EST 2020

% Result     : Theorem 3.10s
% Output     : CNFRefutation 3.10s
% Verified   : 
% Statistics : Number of formulae       :   50 (  62 expanded)
%              Number of leaves         :   22 (  32 expanded)
%              Depth                    :    8
%              Number of atoms          :   76 ( 121 expanded)
%              Number of equality atoms :   29 (  34 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k6_subset_1 > k4_xboole_0 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_29,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_70,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( ( r1_tarski(k9_relat_1(C,A),k9_relat_1(C,B))
            & r1_tarski(A,k1_relat_1(C))
            & v2_funct_1(C) )
         => r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t157_funct_1)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( v2_funct_1(C)
       => k9_relat_1(C,k6_subset_1(A,B)) = k6_subset_1(k9_relat_1(C,A),k9_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_funct_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ~ ( A != k1_xboole_0
          & r1_tarski(A,k1_relat_1(B))
          & k9_relat_1(B,A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_relat_1)).

tff(c_109,plain,(
    ! [A_23,B_24] :
      ( r1_tarski(A_23,B_24)
      | k4_xboole_0(A_23,B_24) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_16,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_117,plain,(
    k4_xboole_0('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_109,c_16])).

tff(c_8,plain,(
    ! [A_6,B_7] : r1_tarski(k4_xboole_0(A_6,B_7),A_6) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_38,plain,(
    ! [A_19,B_20] :
      ( k4_xboole_0(A_19,B_20) = k1_xboole_0
      | ~ r1_tarski(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_45,plain,(
    ! [A_6,B_7] : k4_xboole_0(k4_xboole_0(A_6,B_7),A_6) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_38])).

tff(c_26,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_24,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_18,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_10,plain,(
    ! [A_8,B_9] : k6_subset_1(A_8,B_9) = k4_xboole_0(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_14,plain,(
    ! [C_14,A_12,B_13] :
      ( k6_subset_1(k9_relat_1(C_14,A_12),k9_relat_1(C_14,B_13)) = k9_relat_1(C_14,k6_subset_1(A_12,B_13))
      | ~ v2_funct_1(C_14)
      | ~ v1_funct_1(C_14)
      | ~ v1_relat_1(C_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_593,plain,(
    ! [C_53,A_54,B_55] :
      ( k4_xboole_0(k9_relat_1(C_53,A_54),k9_relat_1(C_53,B_55)) = k9_relat_1(C_53,k4_xboole_0(A_54,B_55))
      | ~ v2_funct_1(C_53)
      | ~ v1_funct_1(C_53)
      | ~ v1_relat_1(C_53) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_10,c_14])).

tff(c_22,plain,(
    r1_tarski(k9_relat_1('#skF_3','#skF_1'),k9_relat_1('#skF_3','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( k4_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_57,plain,(
    k4_xboole_0(k9_relat_1('#skF_3','#skF_1'),k9_relat_1('#skF_3','#skF_2')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_22,c_4])).

tff(c_605,plain,
    ( k9_relat_1('#skF_3',k4_xboole_0('#skF_1','#skF_2')) = k1_xboole_0
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_593,c_57])).

tff(c_620,plain,(
    k9_relat_1('#skF_3',k4_xboole_0('#skF_1','#skF_2')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_18,c_605])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,B_2)
      | k4_xboole_0(A_1,B_2) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_20,plain,(
    r1_tarski('#skF_1',k1_relat_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_212,plain,(
    ! [A_29,C_30,B_31] :
      ( r1_tarski(A_29,C_30)
      | ~ r1_tarski(B_31,C_30)
      | ~ r1_tarski(A_29,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_236,plain,(
    ! [A_29] :
      ( r1_tarski(A_29,k1_relat_1('#skF_3'))
      | ~ r1_tarski(A_29,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_20,c_212])).

tff(c_425,plain,(
    ! [B_44,A_45] :
      ( k9_relat_1(B_44,A_45) != k1_xboole_0
      | ~ r1_tarski(A_45,k1_relat_1(B_44))
      | k1_xboole_0 = A_45
      | ~ v1_relat_1(B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_432,plain,(
    ! [A_29] :
      ( k9_relat_1('#skF_3',A_29) != k1_xboole_0
      | k1_xboole_0 = A_29
      | ~ v1_relat_1('#skF_3')
      | ~ r1_tarski(A_29,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_236,c_425])).

tff(c_953,plain,(
    ! [A_73] :
      ( k9_relat_1('#skF_3',A_73) != k1_xboole_0
      | k1_xboole_0 = A_73
      | ~ r1_tarski(A_73,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_432])).

tff(c_1268,plain,(
    ! [A_88] :
      ( k9_relat_1('#skF_3',A_88) != k1_xboole_0
      | k1_xboole_0 = A_88
      | k4_xboole_0(A_88,'#skF_1') != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_2,c_953])).

tff(c_1277,plain,
    ( k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0
    | k4_xboole_0(k4_xboole_0('#skF_1','#skF_2'),'#skF_1') != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_620,c_1268])).

tff(c_1287,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_45,c_1277])).

tff(c_1289,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_117,c_1287])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.31  % Computer   : n025.cluster.edu
% 0.12/0.31  % Model      : x86_64 x86_64
% 0.12/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.31  % Memory     : 8042.1875MB
% 0.12/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.31  % CPULimit   : 60
% 0.12/0.31  % DateTime   : Tue Dec  1 17:13:50 EST 2020
% 0.12/0.31  % CPUTime    : 
% 0.16/0.32  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.10/1.50  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.10/1.51  
% 3.10/1.51  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.10/1.51  %$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k6_subset_1 > k4_xboole_0 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.10/1.51  
% 3.10/1.51  %Foreground sorts:
% 3.10/1.51  
% 3.10/1.51  
% 3.10/1.51  %Background operators:
% 3.10/1.51  
% 3.10/1.51  
% 3.10/1.51  %Foreground operators:
% 3.10/1.51  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.10/1.51  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.10/1.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.10/1.51  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.10/1.51  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.10/1.51  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.10/1.51  tff('#skF_2', type, '#skF_2': $i).
% 3.10/1.51  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.10/1.51  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 3.10/1.51  tff('#skF_3', type, '#skF_3': $i).
% 3.10/1.51  tff('#skF_1', type, '#skF_1': $i).
% 3.10/1.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.10/1.51  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.10/1.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.10/1.51  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.10/1.51  
% 3.10/1.52  tff(f_29, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 3.10/1.52  tff(f_70, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (((r1_tarski(k9_relat_1(C, A), k9_relat_1(C, B)) & r1_tarski(A, k1_relat_1(C))) & v2_funct_1(C)) => r1_tarski(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t157_funct_1)).
% 3.10/1.52  tff(f_37, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 3.10/1.52  tff(f_39, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 3.10/1.52  tff(f_57, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (v2_funct_1(C) => (k9_relat_1(C, k6_subset_1(A, B)) = k6_subset_1(k9_relat_1(C, A), k9_relat_1(C, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t123_funct_1)).
% 3.10/1.52  tff(f_35, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 3.10/1.52  tff(f_49, axiom, (![A, B]: (v1_relat_1(B) => ~((~(A = k1_xboole_0) & r1_tarski(A, k1_relat_1(B))) & (k9_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_relat_1)).
% 3.10/1.52  tff(c_109, plain, (![A_23, B_24]: (r1_tarski(A_23, B_24) | k4_xboole_0(A_23, B_24)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.10/1.52  tff(c_16, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.10/1.52  tff(c_117, plain, (k4_xboole_0('#skF_1', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_109, c_16])).
% 3.10/1.52  tff(c_8, plain, (![A_6, B_7]: (r1_tarski(k4_xboole_0(A_6, B_7), A_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.10/1.52  tff(c_38, plain, (![A_19, B_20]: (k4_xboole_0(A_19, B_20)=k1_xboole_0 | ~r1_tarski(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.10/1.52  tff(c_45, plain, (![A_6, B_7]: (k4_xboole_0(k4_xboole_0(A_6, B_7), A_6)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_38])).
% 3.10/1.52  tff(c_26, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.10/1.52  tff(c_24, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.10/1.52  tff(c_18, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.10/1.52  tff(c_10, plain, (![A_8, B_9]: (k6_subset_1(A_8, B_9)=k4_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.10/1.52  tff(c_14, plain, (![C_14, A_12, B_13]: (k6_subset_1(k9_relat_1(C_14, A_12), k9_relat_1(C_14, B_13))=k9_relat_1(C_14, k6_subset_1(A_12, B_13)) | ~v2_funct_1(C_14) | ~v1_funct_1(C_14) | ~v1_relat_1(C_14))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.10/1.52  tff(c_593, plain, (![C_53, A_54, B_55]: (k4_xboole_0(k9_relat_1(C_53, A_54), k9_relat_1(C_53, B_55))=k9_relat_1(C_53, k4_xboole_0(A_54, B_55)) | ~v2_funct_1(C_53) | ~v1_funct_1(C_53) | ~v1_relat_1(C_53))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_10, c_14])).
% 3.10/1.52  tff(c_22, plain, (r1_tarski(k9_relat_1('#skF_3', '#skF_1'), k9_relat_1('#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.10/1.52  tff(c_4, plain, (![A_1, B_2]: (k4_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.10/1.52  tff(c_57, plain, (k4_xboole_0(k9_relat_1('#skF_3', '#skF_1'), k9_relat_1('#skF_3', '#skF_2'))=k1_xboole_0), inference(resolution, [status(thm)], [c_22, c_4])).
% 3.10/1.52  tff(c_605, plain, (k9_relat_1('#skF_3', k4_xboole_0('#skF_1', '#skF_2'))=k1_xboole_0 | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_593, c_57])).
% 3.10/1.52  tff(c_620, plain, (k9_relat_1('#skF_3', k4_xboole_0('#skF_1', '#skF_2'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_18, c_605])).
% 3.10/1.52  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(A_1, B_2) | k4_xboole_0(A_1, B_2)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.10/1.52  tff(c_20, plain, (r1_tarski('#skF_1', k1_relat_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.10/1.52  tff(c_212, plain, (![A_29, C_30, B_31]: (r1_tarski(A_29, C_30) | ~r1_tarski(B_31, C_30) | ~r1_tarski(A_29, B_31))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.10/1.52  tff(c_236, plain, (![A_29]: (r1_tarski(A_29, k1_relat_1('#skF_3')) | ~r1_tarski(A_29, '#skF_1'))), inference(resolution, [status(thm)], [c_20, c_212])).
% 3.10/1.52  tff(c_425, plain, (![B_44, A_45]: (k9_relat_1(B_44, A_45)!=k1_xboole_0 | ~r1_tarski(A_45, k1_relat_1(B_44)) | k1_xboole_0=A_45 | ~v1_relat_1(B_44))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.10/1.52  tff(c_432, plain, (![A_29]: (k9_relat_1('#skF_3', A_29)!=k1_xboole_0 | k1_xboole_0=A_29 | ~v1_relat_1('#skF_3') | ~r1_tarski(A_29, '#skF_1'))), inference(resolution, [status(thm)], [c_236, c_425])).
% 3.10/1.52  tff(c_953, plain, (![A_73]: (k9_relat_1('#skF_3', A_73)!=k1_xboole_0 | k1_xboole_0=A_73 | ~r1_tarski(A_73, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_432])).
% 3.10/1.52  tff(c_1268, plain, (![A_88]: (k9_relat_1('#skF_3', A_88)!=k1_xboole_0 | k1_xboole_0=A_88 | k4_xboole_0(A_88, '#skF_1')!=k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_953])).
% 3.10/1.52  tff(c_1277, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0 | k4_xboole_0(k4_xboole_0('#skF_1', '#skF_2'), '#skF_1')!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_620, c_1268])).
% 3.10/1.52  tff(c_1287, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_45, c_1277])).
% 3.10/1.52  tff(c_1289, plain, $false, inference(negUnitSimplification, [status(thm)], [c_117, c_1287])).
% 3.10/1.52  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.10/1.52  
% 3.10/1.52  Inference rules
% 3.10/1.52  ----------------------
% 3.10/1.52  #Ref     : 0
% 3.10/1.52  #Sup     : 309
% 3.10/1.52  #Fact    : 0
% 3.10/1.52  #Define  : 0
% 3.10/1.52  #Split   : 2
% 3.10/1.52  #Chain   : 0
% 3.10/1.52  #Close   : 0
% 3.10/1.52  
% 3.10/1.52  Ordering : KBO
% 3.10/1.52  
% 3.10/1.52  Simplification rules
% 3.10/1.52  ----------------------
% 3.10/1.52  #Subsume      : 33
% 3.10/1.52  #Demod        : 213
% 3.10/1.52  #Tautology    : 177
% 3.10/1.52  #SimpNegUnit  : 3
% 3.10/1.52  #BackRed      : 1
% 3.10/1.52  
% 3.10/1.52  #Partial instantiations: 0
% 3.10/1.52  #Strategies tried      : 1
% 3.10/1.52  
% 3.10/1.52  Timing (in seconds)
% 3.10/1.52  ----------------------
% 3.10/1.53  Preprocessing        : 0.30
% 3.10/1.53  Parsing              : 0.15
% 3.10/1.53  CNF conversion       : 0.02
% 3.10/1.53  Main loop            : 0.46
% 3.10/1.53  Inferencing          : 0.16
% 3.10/1.53  Reduction            : 0.16
% 3.10/1.53  Demodulation         : 0.12
% 3.10/1.53  BG Simplification    : 0.02
% 3.10/1.53  Subsumption          : 0.08
% 3.10/1.53  Abstraction          : 0.02
% 3.10/1.53  MUC search           : 0.00
% 3.10/1.53  Cooper               : 0.00
% 3.10/1.53  Total                : 0.80
% 3.10/1.53  Index Insertion      : 0.00
% 3.10/1.53  Index Deletion       : 0.00
% 3.10/1.53  Index Matching       : 0.00
% 3.10/1.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------
