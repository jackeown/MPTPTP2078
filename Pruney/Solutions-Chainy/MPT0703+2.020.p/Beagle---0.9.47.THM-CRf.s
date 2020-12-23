%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:11 EST 2020

% Result     : Theorem 3.25s
% Output     : CNFRefutation 3.25s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 105 expanded)
%              Number of leaves         :   24 (  48 expanded)
%              Depth                    :    9
%              Number of atoms          :   80 ( 204 expanded)
%              Number of equality atoms :   27 (  50 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k6_subset_1 > k4_xboole_0 > k2_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_35,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_76,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( ( r1_tarski(k10_relat_1(C,A),k10_relat_1(C,B))
            & r1_tarski(A,k2_relat_1(C)) )
         => r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t158_funct_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => k10_relat_1(C,k6_subset_1(A,B)) = k6_subset_1(k10_relat_1(C,A),k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_funct_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(A,k2_relat_1(B))
       => k9_relat_1(B,k10_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).

tff(c_49,plain,(
    ! [A_29,B_30] :
      ( r1_tarski(A_29,B_30)
      | k4_xboole_0(A_29,B_30) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_26,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_53,plain,(
    k4_xboole_0('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_49,c_26])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_54,plain,(
    ! [A_31,B_32] :
      ( k4_xboole_0(A_31,B_32) = k1_xboole_0
      | ~ r1_tarski(A_31,B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_79,plain,(
    ! [B_33] : k4_xboole_0(B_33,B_33) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_54])).

tff(c_14,plain,(
    ! [A_8,B_9] : r1_tarski(k4_xboole_0(A_8,B_9),A_8) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_84,plain,(
    ! [B_33] : r1_tarski(k1_xboole_0,B_33) ),
    inference(superposition,[status(thm),theory(equality)],[c_79,c_14])).

tff(c_34,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_32,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_20,plain,(
    ! [A_15,B_16] : k6_subset_1(A_15,B_16) = k4_xboole_0(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_22,plain,(
    ! [C_19,A_17,B_18] :
      ( k6_subset_1(k10_relat_1(C_19,A_17),k10_relat_1(C_19,B_18)) = k10_relat_1(C_19,k6_subset_1(A_17,B_18))
      | ~ v1_funct_1(C_19)
      | ~ v1_relat_1(C_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1366,plain,(
    ! [C_95,A_96,B_97] :
      ( k4_xboole_0(k10_relat_1(C_95,A_96),k10_relat_1(C_95,B_97)) = k10_relat_1(C_95,k4_xboole_0(A_96,B_97))
      | ~ v1_funct_1(C_95)
      | ~ v1_relat_1(C_95) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_20,c_22])).

tff(c_30,plain,(
    r1_tarski(k10_relat_1('#skF_3','#skF_1'),k10_relat_1('#skF_3','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_74,plain,(
    k4_xboole_0(k10_relat_1('#skF_3','#skF_1'),k10_relat_1('#skF_3','#skF_2')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_30,c_54])).

tff(c_1396,plain,
    ( k10_relat_1('#skF_3',k4_xboole_0('#skF_1','#skF_2')) = k1_xboole_0
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1366,c_74])).

tff(c_1421,plain,(
    k10_relat_1('#skF_3',k4_xboole_0('#skF_1','#skF_2')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_1396])).

tff(c_28,plain,(
    r1_tarski('#skF_1',k2_relat_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_260,plain,(
    ! [A_44,C_45,B_46] :
      ( r1_tarski(A_44,C_45)
      | ~ r1_tarski(B_46,C_45)
      | ~ r1_tarski(A_44,B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_280,plain,(
    ! [A_44] :
      ( r1_tarski(A_44,k2_relat_1('#skF_3'))
      | ~ r1_tarski(A_44,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_28,c_260])).

tff(c_1038,plain,(
    ! [B_85,A_86] :
      ( k9_relat_1(B_85,k10_relat_1(B_85,A_86)) = A_86
      | ~ r1_tarski(A_86,k2_relat_1(B_85))
      | ~ v1_funct_1(B_85)
      | ~ v1_relat_1(B_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1049,plain,(
    ! [A_44] :
      ( k9_relat_1('#skF_3',k10_relat_1('#skF_3',A_44)) = A_44
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3')
      | ~ r1_tarski(A_44,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_280,c_1038])).

tff(c_1069,plain,(
    ! [A_44] :
      ( k9_relat_1('#skF_3',k10_relat_1('#skF_3',A_44)) = A_44
      | ~ r1_tarski(A_44,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_1049])).

tff(c_1466,plain,
    ( k9_relat_1('#skF_3',k1_xboole_0) = k4_xboole_0('#skF_1','#skF_2')
    | ~ r1_tarski(k4_xboole_0('#skF_1','#skF_2'),'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1421,c_1069])).

tff(c_1474,plain,(
    k9_relat_1('#skF_3',k1_xboole_0) = k4_xboole_0('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_1466])).

tff(c_78,plain,(
    ! [B_2] : k4_xboole_0(B_2,B_2) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_54])).

tff(c_1416,plain,(
    ! [C_95,A_96] :
      ( k10_relat_1(C_95,k4_xboole_0(A_96,A_96)) = k1_xboole_0
      | ~ v1_funct_1(C_95)
      | ~ v1_relat_1(C_95) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_1366])).

tff(c_1565,plain,(
    ! [C_100] :
      ( k10_relat_1(C_100,k1_xboole_0) = k1_xboole_0
      | ~ v1_funct_1(C_100)
      | ~ v1_relat_1(C_100) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_1416])).

tff(c_1568,plain,
    ( k10_relat_1('#skF_3',k1_xboole_0) = k1_xboole_0
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_1565])).

tff(c_1571,plain,(
    k10_relat_1('#skF_3',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_1568])).

tff(c_1628,plain,
    ( k9_relat_1('#skF_3',k1_xboole_0) = k1_xboole_0
    | ~ r1_tarski(k1_xboole_0,'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1571,c_1069])).

tff(c_1636,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_1474,c_1628])).

tff(c_1638,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_53,c_1636])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n012.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 12:09:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.25/1.48  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.25/1.48  
% 3.25/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.25/1.48  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k6_subset_1 > k4_xboole_0 > k2_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.25/1.48  
% 3.25/1.48  %Foreground sorts:
% 3.25/1.48  
% 3.25/1.48  
% 3.25/1.48  %Background operators:
% 3.25/1.48  
% 3.25/1.48  
% 3.25/1.48  %Foreground operators:
% 3.25/1.48  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.25/1.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.25/1.48  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.25/1.48  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.25/1.48  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.25/1.48  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.25/1.48  tff('#skF_2', type, '#skF_2': $i).
% 3.25/1.48  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.25/1.48  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 3.25/1.48  tff('#skF_3', type, '#skF_3': $i).
% 3.25/1.48  tff('#skF_1', type, '#skF_1': $i).
% 3.25/1.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.25/1.48  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.25/1.48  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.25/1.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.25/1.48  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.25/1.48  
% 3.25/1.50  tff(f_35, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 3.25/1.50  tff(f_76, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r1_tarski(k10_relat_1(C, A), k10_relat_1(C, B)) & r1_tarski(A, k2_relat_1(C))) => r1_tarski(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t158_funct_1)).
% 3.25/1.50  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.25/1.50  tff(f_43, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 3.25/1.50  tff(f_51, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 3.25/1.50  tff(f_57, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (k10_relat_1(C, k6_subset_1(A, B)) = k6_subset_1(k10_relat_1(C, A), k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t138_funct_1)).
% 3.25/1.50  tff(f_41, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 3.25/1.50  tff(f_65, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(A, k2_relat_1(B)) => (k9_relat_1(B, k10_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t147_funct_1)).
% 3.25/1.50  tff(c_49, plain, (![A_29, B_30]: (r1_tarski(A_29, B_30) | k4_xboole_0(A_29, B_30)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.25/1.50  tff(c_26, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.25/1.50  tff(c_53, plain, (k4_xboole_0('#skF_1', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_49, c_26])).
% 3.25/1.50  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.25/1.50  tff(c_54, plain, (![A_31, B_32]: (k4_xboole_0(A_31, B_32)=k1_xboole_0 | ~r1_tarski(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.25/1.50  tff(c_79, plain, (![B_33]: (k4_xboole_0(B_33, B_33)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_54])).
% 3.25/1.50  tff(c_14, plain, (![A_8, B_9]: (r1_tarski(k4_xboole_0(A_8, B_9), A_8))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.25/1.50  tff(c_84, plain, (![B_33]: (r1_tarski(k1_xboole_0, B_33))), inference(superposition, [status(thm), theory('equality')], [c_79, c_14])).
% 3.25/1.50  tff(c_34, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.25/1.50  tff(c_32, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.25/1.50  tff(c_20, plain, (![A_15, B_16]: (k6_subset_1(A_15, B_16)=k4_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.25/1.50  tff(c_22, plain, (![C_19, A_17, B_18]: (k6_subset_1(k10_relat_1(C_19, A_17), k10_relat_1(C_19, B_18))=k10_relat_1(C_19, k6_subset_1(A_17, B_18)) | ~v1_funct_1(C_19) | ~v1_relat_1(C_19))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.25/1.50  tff(c_1366, plain, (![C_95, A_96, B_97]: (k4_xboole_0(k10_relat_1(C_95, A_96), k10_relat_1(C_95, B_97))=k10_relat_1(C_95, k4_xboole_0(A_96, B_97)) | ~v1_funct_1(C_95) | ~v1_relat_1(C_95))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_20, c_22])).
% 3.25/1.50  tff(c_30, plain, (r1_tarski(k10_relat_1('#skF_3', '#skF_1'), k10_relat_1('#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.25/1.50  tff(c_74, plain, (k4_xboole_0(k10_relat_1('#skF_3', '#skF_1'), k10_relat_1('#skF_3', '#skF_2'))=k1_xboole_0), inference(resolution, [status(thm)], [c_30, c_54])).
% 3.25/1.50  tff(c_1396, plain, (k10_relat_1('#skF_3', k4_xboole_0('#skF_1', '#skF_2'))=k1_xboole_0 | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1366, c_74])).
% 3.25/1.50  tff(c_1421, plain, (k10_relat_1('#skF_3', k4_xboole_0('#skF_1', '#skF_2'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_1396])).
% 3.25/1.50  tff(c_28, plain, (r1_tarski('#skF_1', k2_relat_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.25/1.50  tff(c_260, plain, (![A_44, C_45, B_46]: (r1_tarski(A_44, C_45) | ~r1_tarski(B_46, C_45) | ~r1_tarski(A_44, B_46))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.25/1.50  tff(c_280, plain, (![A_44]: (r1_tarski(A_44, k2_relat_1('#skF_3')) | ~r1_tarski(A_44, '#skF_1'))), inference(resolution, [status(thm)], [c_28, c_260])).
% 3.25/1.50  tff(c_1038, plain, (![B_85, A_86]: (k9_relat_1(B_85, k10_relat_1(B_85, A_86))=A_86 | ~r1_tarski(A_86, k2_relat_1(B_85)) | ~v1_funct_1(B_85) | ~v1_relat_1(B_85))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.25/1.50  tff(c_1049, plain, (![A_44]: (k9_relat_1('#skF_3', k10_relat_1('#skF_3', A_44))=A_44 | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~r1_tarski(A_44, '#skF_1'))), inference(resolution, [status(thm)], [c_280, c_1038])).
% 3.25/1.50  tff(c_1069, plain, (![A_44]: (k9_relat_1('#skF_3', k10_relat_1('#skF_3', A_44))=A_44 | ~r1_tarski(A_44, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_1049])).
% 3.25/1.50  tff(c_1466, plain, (k9_relat_1('#skF_3', k1_xboole_0)=k4_xboole_0('#skF_1', '#skF_2') | ~r1_tarski(k4_xboole_0('#skF_1', '#skF_2'), '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1421, c_1069])).
% 3.25/1.50  tff(c_1474, plain, (k9_relat_1('#skF_3', k1_xboole_0)=k4_xboole_0('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_1466])).
% 3.25/1.50  tff(c_78, plain, (![B_2]: (k4_xboole_0(B_2, B_2)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_54])).
% 3.25/1.50  tff(c_1416, plain, (![C_95, A_96]: (k10_relat_1(C_95, k4_xboole_0(A_96, A_96))=k1_xboole_0 | ~v1_funct_1(C_95) | ~v1_relat_1(C_95))), inference(superposition, [status(thm), theory('equality')], [c_78, c_1366])).
% 3.25/1.50  tff(c_1565, plain, (![C_100]: (k10_relat_1(C_100, k1_xboole_0)=k1_xboole_0 | ~v1_funct_1(C_100) | ~v1_relat_1(C_100))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_1416])).
% 3.25/1.50  tff(c_1568, plain, (k10_relat_1('#skF_3', k1_xboole_0)=k1_xboole_0 | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_34, c_1565])).
% 3.25/1.50  tff(c_1571, plain, (k10_relat_1('#skF_3', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_32, c_1568])).
% 3.25/1.50  tff(c_1628, plain, (k9_relat_1('#skF_3', k1_xboole_0)=k1_xboole_0 | ~r1_tarski(k1_xboole_0, '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1571, c_1069])).
% 3.25/1.50  tff(c_1636, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_84, c_1474, c_1628])).
% 3.25/1.50  tff(c_1638, plain, $false, inference(negUnitSimplification, [status(thm)], [c_53, c_1636])).
% 3.25/1.50  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.25/1.50  
% 3.25/1.50  Inference rules
% 3.25/1.50  ----------------------
% 3.25/1.50  #Ref     : 0
% 3.25/1.50  #Sup     : 381
% 3.25/1.50  #Fact    : 0
% 3.25/1.50  #Define  : 0
% 3.25/1.50  #Split   : 2
% 3.25/1.50  #Chain   : 0
% 3.25/1.50  #Close   : 0
% 3.25/1.50  
% 3.25/1.50  Ordering : KBO
% 3.25/1.50  
% 3.25/1.50  Simplification rules
% 3.25/1.50  ----------------------
% 3.25/1.50  #Subsume      : 42
% 3.25/1.50  #Demod        : 264
% 3.25/1.50  #Tautology    : 205
% 3.25/1.50  #SimpNegUnit  : 1
% 3.25/1.50  #BackRed      : 0
% 3.25/1.50  
% 3.25/1.50  #Partial instantiations: 0
% 3.25/1.50  #Strategies tried      : 1
% 3.25/1.50  
% 3.25/1.50  Timing (in seconds)
% 3.25/1.50  ----------------------
% 3.25/1.50  Preprocessing        : 0.30
% 3.25/1.50  Parsing              : 0.16
% 3.25/1.50  CNF conversion       : 0.02
% 3.25/1.50  Main loop            : 0.44
% 3.25/1.50  Inferencing          : 0.15
% 3.25/1.50  Reduction            : 0.15
% 3.25/1.50  Demodulation         : 0.11
% 3.25/1.50  BG Simplification    : 0.02
% 3.25/1.50  Subsumption          : 0.09
% 3.25/1.50  Abstraction          : 0.02
% 3.25/1.50  MUC search           : 0.00
% 3.25/1.50  Cooper               : 0.00
% 3.25/1.50  Total                : 0.77
% 3.25/1.50  Index Insertion      : 0.00
% 3.25/1.50  Index Deletion       : 0.00
% 3.25/1.50  Index Matching       : 0.00
% 3.25/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
