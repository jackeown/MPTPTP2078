%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:11 EST 2020

% Result     : Theorem 4.31s
% Output     : CNFRefutation 4.31s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 110 expanded)
%              Number of leaves         :   26 (  50 expanded)
%              Depth                    :   10
%              Number of atoms          :   97 ( 205 expanded)
%              Number of equality atoms :   35 (  58 expanded)
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

tff(f_35,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_74,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( ( r1_tarski(k10_relat_1(C,A),k10_relat_1(C,B))
            & r1_tarski(A,k2_relat_1(C)) )
         => r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t158_funct_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => k10_relat_1(C,k6_subset_1(A,B)) = k6_subset_1(k10_relat_1(C,A),k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_funct_1)).

tff(f_45,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(A,k2_relat_1(B))
       => k9_relat_1(B,k10_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).

tff(c_111,plain,(
    ! [A_32,B_33] :
      ( r1_tarski(A_32,B_33)
      | k4_xboole_0(A_32,B_33) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_26,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_119,plain,(
    k4_xboole_0('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_111,c_26])).

tff(c_28,plain,(
    r1_tarski('#skF_1',k2_relat_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_49,plain,(
    ! [A_26,B_27] :
      ( k2_xboole_0(A_26,B_27) = B_27
      | ~ r1_tarski(A_26,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_63,plain,(
    k2_xboole_0('#skF_1',k2_relat_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_49])).

tff(c_18,plain,(
    ! [A_11,B_12] : r1_tarski(k4_xboole_0(A_11,B_12),A_11) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_62,plain,(
    ! [A_11,B_12] : k2_xboole_0(k4_xboole_0(A_11,B_12),A_11) = A_11 ),
    inference(resolution,[status(thm)],[c_18,c_49])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_230,plain,(
    ! [A_40,C_41,B_42] :
      ( r1_tarski(A_40,C_41)
      | ~ r1_tarski(k2_xboole_0(A_40,B_42),C_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_254,plain,(
    ! [A_43,B_44] : r1_tarski(A_43,k2_xboole_0(A_43,B_44)) ),
    inference(resolution,[status(thm)],[c_6,c_230])).

tff(c_12,plain,(
    ! [A_5,C_7,B_6] :
      ( r1_tarski(A_5,C_7)
      | ~ r1_tarski(k2_xboole_0(A_5,B_6),C_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_434,plain,(
    ! [A_53,B_54,B_55] : r1_tarski(A_53,k2_xboole_0(k2_xboole_0(A_53,B_54),B_55)) ),
    inference(resolution,[status(thm)],[c_254,c_12])).

tff(c_476,plain,(
    ! [A_56,B_57,B_58] : r1_tarski(k4_xboole_0(A_56,B_57),k2_xboole_0(A_56,B_58)) ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_434])).

tff(c_522,plain,(
    ! [B_59] : r1_tarski(k4_xboole_0('#skF_1',B_59),k2_relat_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_63,c_476])).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( k4_xboole_0(A_3,B_4) = k1_xboole_0
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_540,plain,(
    ! [B_59] : k4_xboole_0(k4_xboole_0('#skF_1',B_59),k2_relat_1('#skF_3')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_522,c_10])).

tff(c_34,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_32,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_120,plain,(
    ! [A_34,B_35] :
      ( k4_xboole_0(A_34,B_35) = k1_xboole_0
      | ~ r1_tarski(A_34,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_143,plain,(
    ! [B_2] : k4_xboole_0(B_2,B_2) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_120])).

tff(c_20,plain,(
    ! [A_13,B_14] : k6_subset_1(A_13,B_14) = k4_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_22,plain,(
    ! [C_17,A_15,B_16] :
      ( k6_subset_1(k10_relat_1(C_17,A_15),k10_relat_1(C_17,B_16)) = k10_relat_1(C_17,k6_subset_1(A_15,B_16))
      | ~ v1_funct_1(C_17)
      | ~ v1_relat_1(C_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_931,plain,(
    ! [C_76,A_77,B_78] :
      ( k4_xboole_0(k10_relat_1(C_76,A_77),k10_relat_1(C_76,B_78)) = k10_relat_1(C_76,k4_xboole_0(A_77,B_78))
      | ~ v1_funct_1(C_76)
      | ~ v1_relat_1(C_76) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_20,c_22])).

tff(c_956,plain,(
    ! [C_76,B_78] :
      ( k10_relat_1(C_76,k4_xboole_0(B_78,B_78)) = k1_xboole_0
      | ~ v1_funct_1(C_76)
      | ~ v1_relat_1(C_76) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_931,c_143])).

tff(c_996,plain,(
    ! [C_79] :
      ( k10_relat_1(C_79,k1_xboole_0) = k1_xboole_0
      | ~ v1_funct_1(C_79)
      | ~ v1_relat_1(C_79) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_143,c_956])).

tff(c_999,plain,
    ( k10_relat_1('#skF_3',k1_xboole_0) = k1_xboole_0
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_996])).

tff(c_1002,plain,(
    k10_relat_1('#skF_3',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_999])).

tff(c_16,plain,(
    ! [A_10] : r1_tarski(k1_xboole_0,A_10) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_545,plain,(
    ! [B_60,A_61] :
      ( k9_relat_1(B_60,k10_relat_1(B_60,A_61)) = A_61
      | ~ r1_tarski(A_61,k2_relat_1(B_60))
      | ~ v1_funct_1(B_60)
      | ~ v1_relat_1(B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_2895,plain,(
    ! [B_132] :
      ( k9_relat_1(B_132,k10_relat_1(B_132,k1_xboole_0)) = k1_xboole_0
      | ~ v1_funct_1(B_132)
      | ~ v1_relat_1(B_132) ) ),
    inference(resolution,[status(thm)],[c_16,c_545])).

tff(c_2904,plain,
    ( k9_relat_1('#skF_3',k1_xboole_0) = k1_xboole_0
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1002,c_2895])).

tff(c_2908,plain,(
    k9_relat_1('#skF_3',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_2904])).

tff(c_30,plain,(
    r1_tarski(k10_relat_1('#skF_3','#skF_1'),k10_relat_1('#skF_3','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_140,plain,(
    k4_xboole_0(k10_relat_1('#skF_3','#skF_1'),k10_relat_1('#skF_3','#skF_2')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_30,c_120])).

tff(c_943,plain,
    ( k10_relat_1('#skF_3',k4_xboole_0('#skF_1','#skF_2')) = k1_xboole_0
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_931,c_140])).

tff(c_975,plain,(
    k10_relat_1('#skF_3',k4_xboole_0('#skF_1','#skF_2')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_943])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | k4_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_4469,plain,(
    ! [B_170,A_171] :
      ( k9_relat_1(B_170,k10_relat_1(B_170,A_171)) = A_171
      | ~ v1_funct_1(B_170)
      | ~ v1_relat_1(B_170)
      | k4_xboole_0(A_171,k2_relat_1(B_170)) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_545])).

tff(c_4501,plain,
    ( k9_relat_1('#skF_3',k1_xboole_0) = k4_xboole_0('#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | k4_xboole_0(k4_xboole_0('#skF_1','#skF_2'),k2_relat_1('#skF_3')) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_975,c_4469])).

tff(c_4527,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_540,c_34,c_32,c_2908,c_4501])).

tff(c_4529,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_119,c_4527])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:26:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.31/1.78  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.31/1.78  
% 4.31/1.78  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.31/1.79  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k6_subset_1 > k4_xboole_0 > k2_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 4.31/1.79  
% 4.31/1.79  %Foreground sorts:
% 4.31/1.79  
% 4.31/1.79  
% 4.31/1.79  %Background operators:
% 4.31/1.79  
% 4.31/1.79  
% 4.31/1.79  %Foreground operators:
% 4.31/1.79  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.31/1.79  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.31/1.79  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.31/1.79  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.31/1.79  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.31/1.79  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.31/1.79  tff('#skF_2', type, '#skF_2': $i).
% 4.31/1.79  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 4.31/1.79  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 4.31/1.79  tff('#skF_3', type, '#skF_3': $i).
% 4.31/1.79  tff('#skF_1', type, '#skF_1': $i).
% 4.31/1.79  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.31/1.79  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 4.31/1.79  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.31/1.79  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.31/1.79  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.31/1.79  
% 4.31/1.80  tff(f_35, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 4.31/1.80  tff(f_74, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r1_tarski(k10_relat_1(C, A), k10_relat_1(C, B)) & r1_tarski(A, k2_relat_1(C))) => r1_tarski(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t158_funct_1)).
% 4.31/1.80  tff(f_43, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 4.31/1.80  tff(f_47, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 4.31/1.80  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.31/1.80  tff(f_39, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_xboole_1)).
% 4.31/1.80  tff(f_49, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 4.31/1.80  tff(f_55, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (k10_relat_1(C, k6_subset_1(A, B)) = k6_subset_1(k10_relat_1(C, A), k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t138_funct_1)).
% 4.31/1.80  tff(f_45, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 4.31/1.80  tff(f_63, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(A, k2_relat_1(B)) => (k9_relat_1(B, k10_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t147_funct_1)).
% 4.31/1.80  tff(c_111, plain, (![A_32, B_33]: (r1_tarski(A_32, B_33) | k4_xboole_0(A_32, B_33)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.31/1.80  tff(c_26, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.31/1.80  tff(c_119, plain, (k4_xboole_0('#skF_1', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_111, c_26])).
% 4.31/1.80  tff(c_28, plain, (r1_tarski('#skF_1', k2_relat_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.31/1.80  tff(c_49, plain, (![A_26, B_27]: (k2_xboole_0(A_26, B_27)=B_27 | ~r1_tarski(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.31/1.80  tff(c_63, plain, (k2_xboole_0('#skF_1', k2_relat_1('#skF_3'))=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_28, c_49])).
% 4.31/1.80  tff(c_18, plain, (![A_11, B_12]: (r1_tarski(k4_xboole_0(A_11, B_12), A_11))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.31/1.80  tff(c_62, plain, (![A_11, B_12]: (k2_xboole_0(k4_xboole_0(A_11, B_12), A_11)=A_11)), inference(resolution, [status(thm)], [c_18, c_49])).
% 4.31/1.80  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.31/1.80  tff(c_230, plain, (![A_40, C_41, B_42]: (r1_tarski(A_40, C_41) | ~r1_tarski(k2_xboole_0(A_40, B_42), C_41))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.31/1.80  tff(c_254, plain, (![A_43, B_44]: (r1_tarski(A_43, k2_xboole_0(A_43, B_44)))), inference(resolution, [status(thm)], [c_6, c_230])).
% 4.31/1.80  tff(c_12, plain, (![A_5, C_7, B_6]: (r1_tarski(A_5, C_7) | ~r1_tarski(k2_xboole_0(A_5, B_6), C_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.31/1.80  tff(c_434, plain, (![A_53, B_54, B_55]: (r1_tarski(A_53, k2_xboole_0(k2_xboole_0(A_53, B_54), B_55)))), inference(resolution, [status(thm)], [c_254, c_12])).
% 4.31/1.80  tff(c_476, plain, (![A_56, B_57, B_58]: (r1_tarski(k4_xboole_0(A_56, B_57), k2_xboole_0(A_56, B_58)))), inference(superposition, [status(thm), theory('equality')], [c_62, c_434])).
% 4.31/1.80  tff(c_522, plain, (![B_59]: (r1_tarski(k4_xboole_0('#skF_1', B_59), k2_relat_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_63, c_476])).
% 4.31/1.80  tff(c_10, plain, (![A_3, B_4]: (k4_xboole_0(A_3, B_4)=k1_xboole_0 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.31/1.80  tff(c_540, plain, (![B_59]: (k4_xboole_0(k4_xboole_0('#skF_1', B_59), k2_relat_1('#skF_3'))=k1_xboole_0)), inference(resolution, [status(thm)], [c_522, c_10])).
% 4.31/1.80  tff(c_34, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.31/1.80  tff(c_32, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.31/1.80  tff(c_120, plain, (![A_34, B_35]: (k4_xboole_0(A_34, B_35)=k1_xboole_0 | ~r1_tarski(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.31/1.80  tff(c_143, plain, (![B_2]: (k4_xboole_0(B_2, B_2)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_120])).
% 4.31/1.80  tff(c_20, plain, (![A_13, B_14]: (k6_subset_1(A_13, B_14)=k4_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.31/1.80  tff(c_22, plain, (![C_17, A_15, B_16]: (k6_subset_1(k10_relat_1(C_17, A_15), k10_relat_1(C_17, B_16))=k10_relat_1(C_17, k6_subset_1(A_15, B_16)) | ~v1_funct_1(C_17) | ~v1_relat_1(C_17))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.31/1.80  tff(c_931, plain, (![C_76, A_77, B_78]: (k4_xboole_0(k10_relat_1(C_76, A_77), k10_relat_1(C_76, B_78))=k10_relat_1(C_76, k4_xboole_0(A_77, B_78)) | ~v1_funct_1(C_76) | ~v1_relat_1(C_76))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_20, c_22])).
% 4.31/1.80  tff(c_956, plain, (![C_76, B_78]: (k10_relat_1(C_76, k4_xboole_0(B_78, B_78))=k1_xboole_0 | ~v1_funct_1(C_76) | ~v1_relat_1(C_76))), inference(superposition, [status(thm), theory('equality')], [c_931, c_143])).
% 4.31/1.80  tff(c_996, plain, (![C_79]: (k10_relat_1(C_79, k1_xboole_0)=k1_xboole_0 | ~v1_funct_1(C_79) | ~v1_relat_1(C_79))), inference(demodulation, [status(thm), theory('equality')], [c_143, c_956])).
% 4.31/1.80  tff(c_999, plain, (k10_relat_1('#skF_3', k1_xboole_0)=k1_xboole_0 | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_34, c_996])).
% 4.31/1.80  tff(c_1002, plain, (k10_relat_1('#skF_3', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_32, c_999])).
% 4.31/1.80  tff(c_16, plain, (![A_10]: (r1_tarski(k1_xboole_0, A_10))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.31/1.80  tff(c_545, plain, (![B_60, A_61]: (k9_relat_1(B_60, k10_relat_1(B_60, A_61))=A_61 | ~r1_tarski(A_61, k2_relat_1(B_60)) | ~v1_funct_1(B_60) | ~v1_relat_1(B_60))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.31/1.80  tff(c_2895, plain, (![B_132]: (k9_relat_1(B_132, k10_relat_1(B_132, k1_xboole_0))=k1_xboole_0 | ~v1_funct_1(B_132) | ~v1_relat_1(B_132))), inference(resolution, [status(thm)], [c_16, c_545])).
% 4.31/1.80  tff(c_2904, plain, (k9_relat_1('#skF_3', k1_xboole_0)=k1_xboole_0 | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1002, c_2895])).
% 4.31/1.80  tff(c_2908, plain, (k9_relat_1('#skF_3', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_2904])).
% 4.31/1.80  tff(c_30, plain, (r1_tarski(k10_relat_1('#skF_3', '#skF_1'), k10_relat_1('#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.31/1.80  tff(c_140, plain, (k4_xboole_0(k10_relat_1('#skF_3', '#skF_1'), k10_relat_1('#skF_3', '#skF_2'))=k1_xboole_0), inference(resolution, [status(thm)], [c_30, c_120])).
% 4.31/1.80  tff(c_943, plain, (k10_relat_1('#skF_3', k4_xboole_0('#skF_1', '#skF_2'))=k1_xboole_0 | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_931, c_140])).
% 4.31/1.80  tff(c_975, plain, (k10_relat_1('#skF_3', k4_xboole_0('#skF_1', '#skF_2'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_943])).
% 4.31/1.80  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | k4_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.31/1.80  tff(c_4469, plain, (![B_170, A_171]: (k9_relat_1(B_170, k10_relat_1(B_170, A_171))=A_171 | ~v1_funct_1(B_170) | ~v1_relat_1(B_170) | k4_xboole_0(A_171, k2_relat_1(B_170))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_545])).
% 4.31/1.80  tff(c_4501, plain, (k9_relat_1('#skF_3', k1_xboole_0)=k4_xboole_0('#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | k4_xboole_0(k4_xboole_0('#skF_1', '#skF_2'), k2_relat_1('#skF_3'))!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_975, c_4469])).
% 4.31/1.80  tff(c_4527, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_540, c_34, c_32, c_2908, c_4501])).
% 4.31/1.80  tff(c_4529, plain, $false, inference(negUnitSimplification, [status(thm)], [c_119, c_4527])).
% 4.31/1.80  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.31/1.80  
% 4.31/1.80  Inference rules
% 4.31/1.80  ----------------------
% 4.31/1.80  #Ref     : 0
% 4.31/1.80  #Sup     : 1102
% 4.31/1.80  #Fact    : 0
% 4.31/1.80  #Define  : 0
% 4.31/1.80  #Split   : 3
% 4.31/1.80  #Chain   : 0
% 4.31/1.80  #Close   : 0
% 4.31/1.80  
% 4.31/1.80  Ordering : KBO
% 4.31/1.80  
% 4.31/1.80  Simplification rules
% 4.31/1.80  ----------------------
% 4.31/1.80  #Subsume      : 67
% 4.31/1.80  #Demod        : 903
% 4.31/1.80  #Tautology    : 759
% 4.31/1.80  #SimpNegUnit  : 1
% 4.31/1.80  #BackRed      : 0
% 4.31/1.80  
% 4.31/1.80  #Partial instantiations: 0
% 4.31/1.80  #Strategies tried      : 1
% 4.31/1.80  
% 4.31/1.80  Timing (in seconds)
% 4.31/1.80  ----------------------
% 4.31/1.80  Preprocessing        : 0.29
% 4.31/1.80  Parsing              : 0.16
% 4.31/1.80  CNF conversion       : 0.02
% 4.31/1.80  Main loop            : 0.75
% 4.31/1.80  Inferencing          : 0.23
% 4.31/1.80  Reduction            : 0.31
% 4.31/1.80  Demodulation         : 0.24
% 4.31/1.80  BG Simplification    : 0.03
% 4.31/1.80  Subsumption          : 0.13
% 4.31/1.80  Abstraction          : 0.04
% 4.31/1.80  MUC search           : 0.00
% 4.31/1.81  Cooper               : 0.00
% 4.31/1.81  Total                : 1.07
% 4.31/1.81  Index Insertion      : 0.00
% 4.31/1.81  Index Deletion       : 0.00
% 4.31/1.81  Index Matching       : 0.00
% 4.31/1.81  BG Taut test         : 0.00
%------------------------------------------------------------------------------
