%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:10 EST 2020

% Result     : Theorem 4.08s
% Output     : CNFRefutation 4.08s
% Verified   : 
% Statistics : Number of formulae       :   62 (  99 expanded)
%              Number of leaves         :   25 (  46 expanded)
%              Depth                    :   12
%              Number of atoms          :   93 ( 191 expanded)
%              Number of equality atoms :   34 (  54 expanded)
%              Maximal formula depth    :    8 (   4 average)
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

tff(f_72,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( ( r1_tarski(k10_relat_1(C,A),k10_relat_1(C,B))
            & r1_tarski(A,k2_relat_1(C)) )
         => r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t158_funct_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_xboole_0(B,C))
     => r1_tarski(k4_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_47,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => k10_relat_1(C,k6_subset_1(A,B)) = k6_subset_1(k10_relat_1(C,A),k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_funct_1)).

tff(f_41,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(A,k2_relat_1(B))
       => k9_relat_1(B,k10_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).

tff(c_26,plain,(
    r1_tarski('#skF_1',k2_relat_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_12,plain,(
    ! [A_5,C_7,B_6] :
      ( r1_tarski(A_5,k2_xboole_0(C_7,B_6))
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_226,plain,(
    ! [A_41,B_42,C_43] :
      ( r1_tarski(k4_xboole_0(A_41,B_42),C_43)
      | ~ r1_tarski(A_41,k2_xboole_0(B_42,C_43)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( k4_xboole_0(A_3,B_4) = k1_xboole_0
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_513,plain,(
    ! [A_59,B_60,C_61] :
      ( k4_xboole_0(k4_xboole_0(A_59,B_60),C_61) = k1_xboole_0
      | ~ r1_tarski(A_59,k2_xboole_0(B_60,C_61)) ) ),
    inference(resolution,[status(thm)],[c_226,c_10])).

tff(c_537,plain,(
    ! [A_5,C_7,B_6] :
      ( k4_xboole_0(k4_xboole_0(A_5,C_7),B_6) = k1_xboole_0
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(resolution,[status(thm)],[c_12,c_513])).

tff(c_89,plain,(
    ! [A_27,B_28] :
      ( r1_tarski(A_27,B_28)
      | k4_xboole_0(A_27,B_28) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_24,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_97,plain,(
    k4_xboole_0('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_89,c_24])).

tff(c_32,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_30,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_46,plain,(
    ! [A_23,B_24] :
      ( k4_xboole_0(A_23,B_24) = k1_xboole_0
      | ~ r1_tarski(A_23,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_57,plain,(
    ! [B_2] : k4_xboole_0(B_2,B_2) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_46])).

tff(c_18,plain,(
    ! [A_12,B_13] : k6_subset_1(A_12,B_13) = k4_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_20,plain,(
    ! [C_16,A_14,B_15] :
      ( k6_subset_1(k10_relat_1(C_16,A_14),k10_relat_1(C_16,B_15)) = k10_relat_1(C_16,k6_subset_1(A_14,B_15))
      | ~ v1_funct_1(C_16)
      | ~ v1_relat_1(C_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_400,plain,(
    ! [C_53,A_54,B_55] :
      ( k4_xboole_0(k10_relat_1(C_53,A_54),k10_relat_1(C_53,B_55)) = k10_relat_1(C_53,k4_xboole_0(A_54,B_55))
      | ~ v1_funct_1(C_53)
      | ~ v1_relat_1(C_53) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_18,c_20])).

tff(c_416,plain,(
    ! [C_53,B_55] :
      ( k10_relat_1(C_53,k4_xboole_0(B_55,B_55)) = k1_xboole_0
      | ~ v1_funct_1(C_53)
      | ~ v1_relat_1(C_53) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_400,c_57])).

tff(c_452,plain,(
    ! [C_56] :
      ( k10_relat_1(C_56,k1_xboole_0) = k1_xboole_0
      | ~ v1_funct_1(C_56)
      | ~ v1_relat_1(C_56) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_416])).

tff(c_455,plain,
    ( k10_relat_1('#skF_3',k1_xboole_0) = k1_xboole_0
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_452])).

tff(c_458,plain,(
    k10_relat_1('#skF_3',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_455])).

tff(c_14,plain,(
    ! [A_8] : r1_tarski(k1_xboole_0,A_8) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_264,plain,(
    ! [B_44,A_45] :
      ( k9_relat_1(B_44,k10_relat_1(B_44,A_45)) = A_45
      | ~ r1_tarski(A_45,k2_relat_1(B_44))
      | ~ v1_funct_1(B_44)
      | ~ v1_relat_1(B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_499,plain,(
    ! [B_58] :
      ( k9_relat_1(B_58,k10_relat_1(B_58,k1_xboole_0)) = k1_xboole_0
      | ~ v1_funct_1(B_58)
      | ~ v1_relat_1(B_58) ) ),
    inference(resolution,[status(thm)],[c_14,c_264])).

tff(c_508,plain,
    ( k9_relat_1('#skF_3',k1_xboole_0) = k1_xboole_0
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_458,c_499])).

tff(c_512,plain,(
    k9_relat_1('#skF_3',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_508])).

tff(c_28,plain,(
    r1_tarski(k10_relat_1('#skF_3','#skF_1'),k10_relat_1('#skF_3','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_69,plain,(
    k4_xboole_0(k10_relat_1('#skF_3','#skF_1'),k10_relat_1('#skF_3','#skF_2')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_28,c_10])).

tff(c_412,plain,
    ( k10_relat_1('#skF_3',k4_xboole_0('#skF_1','#skF_2')) = k1_xboole_0
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_400,c_69])).

tff(c_431,plain,(
    k10_relat_1('#skF_3',k4_xboole_0('#skF_1','#skF_2')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_412])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | k4_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2576,plain,(
    ! [B_114,A_115] :
      ( k9_relat_1(B_114,k10_relat_1(B_114,A_115)) = A_115
      | ~ v1_funct_1(B_114)
      | ~ v1_relat_1(B_114)
      | k4_xboole_0(A_115,k2_relat_1(B_114)) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_264])).

tff(c_2626,plain,
    ( k9_relat_1('#skF_3',k1_xboole_0) = k4_xboole_0('#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | k4_xboole_0(k4_xboole_0('#skF_1','#skF_2'),k2_relat_1('#skF_3')) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_431,c_2576])).

tff(c_2664,plain,
    ( k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0
    | k4_xboole_0(k4_xboole_0('#skF_1','#skF_2'),k2_relat_1('#skF_3')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_512,c_2626])).

tff(c_2665,plain,(
    k4_xboole_0(k4_xboole_0('#skF_1','#skF_2'),k2_relat_1('#skF_3')) != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_97,c_2664])).

tff(c_2674,plain,(
    ~ r1_tarski('#skF_1',k2_relat_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_537,c_2665])).

tff(c_2679,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_2674])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:09:17 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.08/1.71  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.08/1.72  
% 4.08/1.72  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.08/1.72  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k6_subset_1 > k4_xboole_0 > k2_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 4.08/1.72  
% 4.08/1.72  %Foreground sorts:
% 4.08/1.72  
% 4.08/1.72  
% 4.08/1.72  %Background operators:
% 4.08/1.72  
% 4.08/1.72  
% 4.08/1.72  %Foreground operators:
% 4.08/1.72  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.08/1.72  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.08/1.72  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.08/1.72  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.08/1.72  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.08/1.72  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.08/1.72  tff('#skF_2', type, '#skF_2': $i).
% 4.08/1.72  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 4.08/1.72  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 4.08/1.72  tff('#skF_3', type, '#skF_3': $i).
% 4.08/1.72  tff('#skF_1', type, '#skF_1': $i).
% 4.08/1.72  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.08/1.72  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 4.08/1.72  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.08/1.72  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.08/1.72  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.08/1.72  
% 4.08/1.73  tff(f_72, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r1_tarski(k10_relat_1(C, A), k10_relat_1(C, B)) & r1_tarski(A, k2_relat_1(C))) => r1_tarski(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t158_funct_1)).
% 4.08/1.73  tff(f_39, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_xboole_1)).
% 4.08/1.73  tff(f_45, axiom, (![A, B, C]: (r1_tarski(A, k2_xboole_0(B, C)) => r1_tarski(k4_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_xboole_1)).
% 4.08/1.73  tff(f_35, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 4.08/1.73  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.08/1.73  tff(f_47, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 4.08/1.73  tff(f_53, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (k10_relat_1(C, k6_subset_1(A, B)) = k6_subset_1(k10_relat_1(C, A), k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t138_funct_1)).
% 4.08/1.73  tff(f_41, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 4.08/1.73  tff(f_61, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(A, k2_relat_1(B)) => (k9_relat_1(B, k10_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t147_funct_1)).
% 4.08/1.73  tff(c_26, plain, (r1_tarski('#skF_1', k2_relat_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.08/1.73  tff(c_12, plain, (![A_5, C_7, B_6]: (r1_tarski(A_5, k2_xboole_0(C_7, B_6)) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.08/1.73  tff(c_226, plain, (![A_41, B_42, C_43]: (r1_tarski(k4_xboole_0(A_41, B_42), C_43) | ~r1_tarski(A_41, k2_xboole_0(B_42, C_43)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.08/1.73  tff(c_10, plain, (![A_3, B_4]: (k4_xboole_0(A_3, B_4)=k1_xboole_0 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.08/1.73  tff(c_513, plain, (![A_59, B_60, C_61]: (k4_xboole_0(k4_xboole_0(A_59, B_60), C_61)=k1_xboole_0 | ~r1_tarski(A_59, k2_xboole_0(B_60, C_61)))), inference(resolution, [status(thm)], [c_226, c_10])).
% 4.08/1.73  tff(c_537, plain, (![A_5, C_7, B_6]: (k4_xboole_0(k4_xboole_0(A_5, C_7), B_6)=k1_xboole_0 | ~r1_tarski(A_5, B_6))), inference(resolution, [status(thm)], [c_12, c_513])).
% 4.08/1.73  tff(c_89, plain, (![A_27, B_28]: (r1_tarski(A_27, B_28) | k4_xboole_0(A_27, B_28)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.08/1.73  tff(c_24, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.08/1.73  tff(c_97, plain, (k4_xboole_0('#skF_1', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_89, c_24])).
% 4.08/1.73  tff(c_32, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.08/1.73  tff(c_30, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.08/1.73  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.08/1.73  tff(c_46, plain, (![A_23, B_24]: (k4_xboole_0(A_23, B_24)=k1_xboole_0 | ~r1_tarski(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.08/1.73  tff(c_57, plain, (![B_2]: (k4_xboole_0(B_2, B_2)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_46])).
% 4.08/1.73  tff(c_18, plain, (![A_12, B_13]: (k6_subset_1(A_12, B_13)=k4_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.08/1.73  tff(c_20, plain, (![C_16, A_14, B_15]: (k6_subset_1(k10_relat_1(C_16, A_14), k10_relat_1(C_16, B_15))=k10_relat_1(C_16, k6_subset_1(A_14, B_15)) | ~v1_funct_1(C_16) | ~v1_relat_1(C_16))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.08/1.73  tff(c_400, plain, (![C_53, A_54, B_55]: (k4_xboole_0(k10_relat_1(C_53, A_54), k10_relat_1(C_53, B_55))=k10_relat_1(C_53, k4_xboole_0(A_54, B_55)) | ~v1_funct_1(C_53) | ~v1_relat_1(C_53))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_18, c_20])).
% 4.08/1.73  tff(c_416, plain, (![C_53, B_55]: (k10_relat_1(C_53, k4_xboole_0(B_55, B_55))=k1_xboole_0 | ~v1_funct_1(C_53) | ~v1_relat_1(C_53))), inference(superposition, [status(thm), theory('equality')], [c_400, c_57])).
% 4.08/1.73  tff(c_452, plain, (![C_56]: (k10_relat_1(C_56, k1_xboole_0)=k1_xboole_0 | ~v1_funct_1(C_56) | ~v1_relat_1(C_56))), inference(demodulation, [status(thm), theory('equality')], [c_57, c_416])).
% 4.08/1.73  tff(c_455, plain, (k10_relat_1('#skF_3', k1_xboole_0)=k1_xboole_0 | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_32, c_452])).
% 4.08/1.73  tff(c_458, plain, (k10_relat_1('#skF_3', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_30, c_455])).
% 4.08/1.73  tff(c_14, plain, (![A_8]: (r1_tarski(k1_xboole_0, A_8))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.08/1.73  tff(c_264, plain, (![B_44, A_45]: (k9_relat_1(B_44, k10_relat_1(B_44, A_45))=A_45 | ~r1_tarski(A_45, k2_relat_1(B_44)) | ~v1_funct_1(B_44) | ~v1_relat_1(B_44))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.08/1.73  tff(c_499, plain, (![B_58]: (k9_relat_1(B_58, k10_relat_1(B_58, k1_xboole_0))=k1_xboole_0 | ~v1_funct_1(B_58) | ~v1_relat_1(B_58))), inference(resolution, [status(thm)], [c_14, c_264])).
% 4.08/1.73  tff(c_508, plain, (k9_relat_1('#skF_3', k1_xboole_0)=k1_xboole_0 | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_458, c_499])).
% 4.08/1.73  tff(c_512, plain, (k9_relat_1('#skF_3', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_508])).
% 4.08/1.73  tff(c_28, plain, (r1_tarski(k10_relat_1('#skF_3', '#skF_1'), k10_relat_1('#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.08/1.73  tff(c_69, plain, (k4_xboole_0(k10_relat_1('#skF_3', '#skF_1'), k10_relat_1('#skF_3', '#skF_2'))=k1_xboole_0), inference(resolution, [status(thm)], [c_28, c_10])).
% 4.08/1.73  tff(c_412, plain, (k10_relat_1('#skF_3', k4_xboole_0('#skF_1', '#skF_2'))=k1_xboole_0 | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_400, c_69])).
% 4.08/1.73  tff(c_431, plain, (k10_relat_1('#skF_3', k4_xboole_0('#skF_1', '#skF_2'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_412])).
% 4.08/1.73  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | k4_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.08/1.73  tff(c_2576, plain, (![B_114, A_115]: (k9_relat_1(B_114, k10_relat_1(B_114, A_115))=A_115 | ~v1_funct_1(B_114) | ~v1_relat_1(B_114) | k4_xboole_0(A_115, k2_relat_1(B_114))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_264])).
% 4.08/1.73  tff(c_2626, plain, (k9_relat_1('#skF_3', k1_xboole_0)=k4_xboole_0('#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | k4_xboole_0(k4_xboole_0('#skF_1', '#skF_2'), k2_relat_1('#skF_3'))!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_431, c_2576])).
% 4.08/1.73  tff(c_2664, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0 | k4_xboole_0(k4_xboole_0('#skF_1', '#skF_2'), k2_relat_1('#skF_3'))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_512, c_2626])).
% 4.08/1.73  tff(c_2665, plain, (k4_xboole_0(k4_xboole_0('#skF_1', '#skF_2'), k2_relat_1('#skF_3'))!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_97, c_2664])).
% 4.08/1.73  tff(c_2674, plain, (~r1_tarski('#skF_1', k2_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_537, c_2665])).
% 4.08/1.73  tff(c_2679, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_2674])).
% 4.08/1.73  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.08/1.73  
% 4.08/1.73  Inference rules
% 4.08/1.73  ----------------------
% 4.08/1.73  #Ref     : 0
% 4.08/1.73  #Sup     : 600
% 4.08/1.73  #Fact    : 0
% 4.08/1.73  #Define  : 0
% 4.08/1.73  #Split   : 2
% 4.08/1.73  #Chain   : 0
% 4.08/1.73  #Close   : 0
% 4.08/1.73  
% 4.08/1.73  Ordering : KBO
% 4.08/1.73  
% 4.08/1.73  Simplification rules
% 4.08/1.73  ----------------------
% 4.08/1.73  #Subsume      : 54
% 4.08/1.73  #Demod        : 522
% 4.08/1.73  #Tautology    : 384
% 4.08/1.73  #SimpNegUnit  : 1
% 4.08/1.73  #BackRed      : 0
% 4.08/1.73  
% 4.08/1.73  #Partial instantiations: 0
% 4.08/1.73  #Strategies tried      : 1
% 4.08/1.73  
% 4.08/1.73  Timing (in seconds)
% 4.08/1.73  ----------------------
% 4.08/1.74  Preprocessing        : 0.31
% 4.08/1.74  Parsing              : 0.17
% 4.08/1.74  CNF conversion       : 0.02
% 4.08/1.74  Main loop            : 0.65
% 4.08/1.74  Inferencing          : 0.21
% 4.08/1.74  Reduction            : 0.24
% 4.08/1.74  Demodulation         : 0.18
% 4.08/1.74  BG Simplification    : 0.03
% 4.08/1.74  Subsumption          : 0.14
% 4.08/1.74  Abstraction          : 0.03
% 4.08/1.74  MUC search           : 0.00
% 4.08/1.74  Cooper               : 0.00
% 4.08/1.74  Total                : 1.00
% 4.08/1.74  Index Insertion      : 0.00
% 4.08/1.74  Index Deletion       : 0.00
% 4.08/1.74  Index Matching       : 0.00
% 4.08/1.74  BG Taut test         : 0.00
%------------------------------------------------------------------------------
