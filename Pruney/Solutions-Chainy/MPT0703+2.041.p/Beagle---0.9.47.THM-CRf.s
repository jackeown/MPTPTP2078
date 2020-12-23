%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:14 EST 2020

% Result     : Theorem 2.97s
% Output     : CNFRefutation 3.13s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 145 expanded)
%              Number of leaves         :   25 (  62 expanded)
%              Depth                    :   10
%              Number of atoms          :  111 ( 253 expanded)
%              Number of equality atoms :   47 (  85 expanded)
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

tff(f_29,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_68,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( ( r1_tarski(k10_relat_1(C,A),k10_relat_1(C,B))
            & r1_tarski(A,k2_relat_1(C)) )
         => r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t158_funct_1)).

tff(f_41,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_39,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => k10_relat_1(C,k6_subset_1(A,B)) = k6_subset_1(k10_relat_1(C,A),k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_funct_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(A,k2_relat_1(B))
       => k9_relat_1(B,k10_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).

tff(c_136,plain,(
    ! [A_32,B_33] :
      ( r1_tarski(A_32,B_33)
      | k4_xboole_0(A_32,B_33) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_20,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_148,plain,(
    k4_xboole_0('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_136,c_20])).

tff(c_12,plain,(
    ! [A_10] : k4_xboole_0(A_10,k1_xboole_0) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_39,plain,(
    ! [A_19,B_20] : r1_tarski(k4_xboole_0(A_19,B_20),A_19) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_42,plain,(
    ! [A_10] : r1_tarski(A_10,A_10) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_39])).

tff(c_96,plain,(
    ! [A_29,B_30] :
      ( k4_xboole_0(A_29,B_30) = k1_xboole_0
      | ~ r1_tarski(A_29,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_113,plain,(
    ! [A_31] : k4_xboole_0(A_31,A_31) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_42,c_96])).

tff(c_10,plain,(
    ! [A_8,B_9] : r1_tarski(k4_xboole_0(A_8,B_9),A_8) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_121,plain,(
    ! [A_31] : r1_tarski(k1_xboole_0,A_31) ),
    inference(superposition,[status(thm),theory(equality)],[c_113,c_10])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( k2_xboole_0(A_6,B_7) = B_7
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_785,plain,(
    ! [A_65,B_66] :
      ( k2_xboole_0(A_65,B_66) = B_66
      | k4_xboole_0(A_65,B_66) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_136,c_8])).

tff(c_830,plain,(
    ! [A_67] :
      ( k2_xboole_0(A_67,k1_xboole_0) = k1_xboole_0
      | k1_xboole_0 != A_67 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_785])).

tff(c_6,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(A_3,C_5)
      | ~ r1_tarski(k2_xboole_0(A_3,B_4),C_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_860,plain,(
    ! [A_67,C_5] :
      ( r1_tarski(A_67,C_5)
      | ~ r1_tarski(k1_xboole_0,C_5)
      | k1_xboole_0 != A_67 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_830,c_6])).

tff(c_932,plain,(
    ! [A_69,C_70] :
      ( r1_tarski(A_69,C_70)
      | k1_xboole_0 != A_69 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_860])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( k4_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_1088,plain,(
    ! [C_70] : k4_xboole_0(k1_xboole_0,C_70) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_932,c_4])).

tff(c_28,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_26,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_22,plain,(
    r1_tarski('#skF_1',k2_relat_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_53,plain,(
    ! [A_24,B_25] :
      ( k2_xboole_0(A_24,B_25) = B_25
      | ~ r1_tarski(A_24,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_65,plain,(
    k2_xboole_0('#skF_1',k2_relat_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_53])).

tff(c_64,plain,(
    ! [A_8,B_9] : k2_xboole_0(k4_xboole_0(A_8,B_9),A_8) = A_8 ),
    inference(resolution,[status(thm)],[c_10,c_53])).

tff(c_272,plain,(
    ! [A_39,C_40,B_41] :
      ( r1_tarski(A_39,C_40)
      | ~ r1_tarski(k2_xboole_0(A_39,B_41),C_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_296,plain,(
    ! [A_42,B_43] : r1_tarski(A_42,k2_xboole_0(A_42,B_43)) ),
    inference(resolution,[status(thm)],[c_42,c_272])).

tff(c_442,plain,(
    ! [A_50,B_51,B_52] : r1_tarski(A_50,k2_xboole_0(k2_xboole_0(A_50,B_51),B_52)) ),
    inference(resolution,[status(thm)],[c_296,c_6])).

tff(c_505,plain,(
    ! [A_54,B_55,B_56] : r1_tarski(k4_xboole_0(A_54,B_55),k2_xboole_0(A_54,B_56)) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_442])).

tff(c_560,plain,(
    ! [B_57] : r1_tarski(k4_xboole_0('#skF_1',B_57),k2_relat_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_65,c_505])).

tff(c_586,plain,(
    ! [B_57] : k4_xboole_0(k4_xboole_0('#skF_1',B_57),k2_relat_1('#skF_3')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_560,c_4])).

tff(c_14,plain,(
    ! [A_11,B_12] : k6_subset_1(A_11,B_12) = k4_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_16,plain,(
    ! [C_15,A_13,B_14] :
      ( k6_subset_1(k10_relat_1(C_15,A_13),k10_relat_1(C_15,B_14)) = k10_relat_1(C_15,k6_subset_1(A_13,B_14))
      | ~ v1_funct_1(C_15)
      | ~ v1_relat_1(C_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_593,plain,(
    ! [C_58,A_59,B_60] :
      ( k4_xboole_0(k10_relat_1(C_58,A_59),k10_relat_1(C_58,B_60)) = k10_relat_1(C_58,k4_xboole_0(A_59,B_60))
      | ~ v1_funct_1(C_58)
      | ~ v1_relat_1(C_58) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_14,c_16])).

tff(c_24,plain,(
    r1_tarski(k10_relat_1('#skF_3','#skF_1'),k10_relat_1('#skF_3','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_109,plain,(
    k4_xboole_0(k10_relat_1('#skF_3','#skF_1'),k10_relat_1('#skF_3','#skF_2')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_24,c_96])).

tff(c_602,plain,
    ( k10_relat_1('#skF_3',k4_xboole_0('#skF_1','#skF_2')) = k1_xboole_0
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_593,c_109])).

tff(c_628,plain,(
    k10_relat_1('#skF_3',k4_xboole_0('#skF_1','#skF_2')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_602])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,B_2)
      | k4_xboole_0(A_1,B_2) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_326,plain,(
    ! [B_44,A_45] :
      ( k9_relat_1(B_44,k10_relat_1(B_44,A_45)) = A_45
      | ~ r1_tarski(A_45,k2_relat_1(B_44))
      | ~ v1_funct_1(B_44)
      | ~ v1_relat_1(B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1344,plain,(
    ! [B_89,A_90] :
      ( k9_relat_1(B_89,k10_relat_1(B_89,A_90)) = A_90
      | ~ v1_funct_1(B_89)
      | ~ v1_relat_1(B_89)
      | k4_xboole_0(A_90,k2_relat_1(B_89)) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_2,c_326])).

tff(c_1356,plain,
    ( k9_relat_1('#skF_3',k1_xboole_0) = k4_xboole_0('#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | k4_xboole_0(k4_xboole_0('#skF_1','#skF_2'),k2_relat_1('#skF_3')) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_628,c_1344])).

tff(c_1366,plain,(
    k9_relat_1('#skF_3',k1_xboole_0) = k4_xboole_0('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_586,c_28,c_26,c_1356])).

tff(c_110,plain,(
    ! [A_10] : k4_xboole_0(A_10,A_10) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_42,c_96])).

tff(c_609,plain,(
    ! [C_58,B_60] :
      ( k10_relat_1(C_58,k4_xboole_0(B_60,B_60)) = k1_xboole_0
      | ~ v1_funct_1(C_58)
      | ~ v1_relat_1(C_58) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_593,c_110])).

tff(c_1495,plain,(
    ! [C_98] :
      ( k10_relat_1(C_98,k1_xboole_0) = k1_xboole_0
      | ~ v1_funct_1(C_98)
      | ~ v1_relat_1(C_98) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_609])).

tff(c_1498,plain,
    ( k10_relat_1('#skF_3',k1_xboole_0) = k1_xboole_0
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_1495])).

tff(c_1501,plain,(
    k10_relat_1('#skF_3',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_1498])).

tff(c_342,plain,(
    ! [B_44,A_1] :
      ( k9_relat_1(B_44,k10_relat_1(B_44,A_1)) = A_1
      | ~ v1_funct_1(B_44)
      | ~ v1_relat_1(B_44)
      | k4_xboole_0(A_1,k2_relat_1(B_44)) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_2,c_326])).

tff(c_1505,plain,
    ( k9_relat_1('#skF_3',k1_xboole_0) = k1_xboole_0
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | k4_xboole_0(k1_xboole_0,k2_relat_1('#skF_3')) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1501,c_342])).

tff(c_1518,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1088,c_28,c_26,c_1366,c_1505])).

tff(c_1520,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_148,c_1518])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:23:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.97/1.47  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.97/1.48  
% 2.97/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.97/1.48  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k6_subset_1 > k4_xboole_0 > k2_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.97/1.48  
% 2.97/1.48  %Foreground sorts:
% 2.97/1.48  
% 2.97/1.48  
% 2.97/1.48  %Background operators:
% 2.97/1.48  
% 2.97/1.48  
% 2.97/1.48  %Foreground operators:
% 2.97/1.48  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.97/1.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.97/1.48  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.97/1.48  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.97/1.48  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.97/1.48  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.97/1.48  tff('#skF_2', type, '#skF_2': $i).
% 2.97/1.48  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.97/1.48  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 2.97/1.48  tff('#skF_3', type, '#skF_3': $i).
% 2.97/1.48  tff('#skF_1', type, '#skF_1': $i).
% 2.97/1.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.97/1.48  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.97/1.48  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.97/1.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.97/1.48  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.97/1.48  
% 3.13/1.50  tff(f_29, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 3.13/1.50  tff(f_68, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r1_tarski(k10_relat_1(C, A), k10_relat_1(C, B)) & r1_tarski(A, k2_relat_1(C))) => r1_tarski(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t158_funct_1)).
% 3.13/1.50  tff(f_41, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 3.13/1.50  tff(f_39, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 3.13/1.50  tff(f_37, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 3.13/1.50  tff(f_33, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_xboole_1)).
% 3.13/1.50  tff(f_43, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 3.13/1.50  tff(f_49, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (k10_relat_1(C, k6_subset_1(A, B)) = k6_subset_1(k10_relat_1(C, A), k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t138_funct_1)).
% 3.13/1.50  tff(f_57, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(A, k2_relat_1(B)) => (k9_relat_1(B, k10_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t147_funct_1)).
% 3.13/1.50  tff(c_136, plain, (![A_32, B_33]: (r1_tarski(A_32, B_33) | k4_xboole_0(A_32, B_33)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.13/1.50  tff(c_20, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.13/1.50  tff(c_148, plain, (k4_xboole_0('#skF_1', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_136, c_20])).
% 3.13/1.50  tff(c_12, plain, (![A_10]: (k4_xboole_0(A_10, k1_xboole_0)=A_10)), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.13/1.50  tff(c_39, plain, (![A_19, B_20]: (r1_tarski(k4_xboole_0(A_19, B_20), A_19))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.13/1.50  tff(c_42, plain, (![A_10]: (r1_tarski(A_10, A_10))), inference(superposition, [status(thm), theory('equality')], [c_12, c_39])).
% 3.13/1.50  tff(c_96, plain, (![A_29, B_30]: (k4_xboole_0(A_29, B_30)=k1_xboole_0 | ~r1_tarski(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.13/1.50  tff(c_113, plain, (![A_31]: (k4_xboole_0(A_31, A_31)=k1_xboole_0)), inference(resolution, [status(thm)], [c_42, c_96])).
% 3.13/1.50  tff(c_10, plain, (![A_8, B_9]: (r1_tarski(k4_xboole_0(A_8, B_9), A_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.13/1.50  tff(c_121, plain, (![A_31]: (r1_tarski(k1_xboole_0, A_31))), inference(superposition, [status(thm), theory('equality')], [c_113, c_10])).
% 3.13/1.50  tff(c_8, plain, (![A_6, B_7]: (k2_xboole_0(A_6, B_7)=B_7 | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.13/1.50  tff(c_785, plain, (![A_65, B_66]: (k2_xboole_0(A_65, B_66)=B_66 | k4_xboole_0(A_65, B_66)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_136, c_8])).
% 3.13/1.50  tff(c_830, plain, (![A_67]: (k2_xboole_0(A_67, k1_xboole_0)=k1_xboole_0 | k1_xboole_0!=A_67)), inference(superposition, [status(thm), theory('equality')], [c_12, c_785])).
% 3.13/1.50  tff(c_6, plain, (![A_3, C_5, B_4]: (r1_tarski(A_3, C_5) | ~r1_tarski(k2_xboole_0(A_3, B_4), C_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.13/1.50  tff(c_860, plain, (![A_67, C_5]: (r1_tarski(A_67, C_5) | ~r1_tarski(k1_xboole_0, C_5) | k1_xboole_0!=A_67)), inference(superposition, [status(thm), theory('equality')], [c_830, c_6])).
% 3.13/1.50  tff(c_932, plain, (![A_69, C_70]: (r1_tarski(A_69, C_70) | k1_xboole_0!=A_69)), inference(demodulation, [status(thm), theory('equality')], [c_121, c_860])).
% 3.13/1.50  tff(c_4, plain, (![A_1, B_2]: (k4_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.13/1.50  tff(c_1088, plain, (![C_70]: (k4_xboole_0(k1_xboole_0, C_70)=k1_xboole_0)), inference(resolution, [status(thm)], [c_932, c_4])).
% 3.13/1.50  tff(c_28, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.13/1.50  tff(c_26, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.13/1.50  tff(c_22, plain, (r1_tarski('#skF_1', k2_relat_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.13/1.50  tff(c_53, plain, (![A_24, B_25]: (k2_xboole_0(A_24, B_25)=B_25 | ~r1_tarski(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.13/1.50  tff(c_65, plain, (k2_xboole_0('#skF_1', k2_relat_1('#skF_3'))=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_22, c_53])).
% 3.13/1.50  tff(c_64, plain, (![A_8, B_9]: (k2_xboole_0(k4_xboole_0(A_8, B_9), A_8)=A_8)), inference(resolution, [status(thm)], [c_10, c_53])).
% 3.13/1.50  tff(c_272, plain, (![A_39, C_40, B_41]: (r1_tarski(A_39, C_40) | ~r1_tarski(k2_xboole_0(A_39, B_41), C_40))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.13/1.50  tff(c_296, plain, (![A_42, B_43]: (r1_tarski(A_42, k2_xboole_0(A_42, B_43)))), inference(resolution, [status(thm)], [c_42, c_272])).
% 3.13/1.50  tff(c_442, plain, (![A_50, B_51, B_52]: (r1_tarski(A_50, k2_xboole_0(k2_xboole_0(A_50, B_51), B_52)))), inference(resolution, [status(thm)], [c_296, c_6])).
% 3.13/1.50  tff(c_505, plain, (![A_54, B_55, B_56]: (r1_tarski(k4_xboole_0(A_54, B_55), k2_xboole_0(A_54, B_56)))), inference(superposition, [status(thm), theory('equality')], [c_64, c_442])).
% 3.13/1.50  tff(c_560, plain, (![B_57]: (r1_tarski(k4_xboole_0('#skF_1', B_57), k2_relat_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_65, c_505])).
% 3.13/1.50  tff(c_586, plain, (![B_57]: (k4_xboole_0(k4_xboole_0('#skF_1', B_57), k2_relat_1('#skF_3'))=k1_xboole_0)), inference(resolution, [status(thm)], [c_560, c_4])).
% 3.13/1.50  tff(c_14, plain, (![A_11, B_12]: (k6_subset_1(A_11, B_12)=k4_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.13/1.50  tff(c_16, plain, (![C_15, A_13, B_14]: (k6_subset_1(k10_relat_1(C_15, A_13), k10_relat_1(C_15, B_14))=k10_relat_1(C_15, k6_subset_1(A_13, B_14)) | ~v1_funct_1(C_15) | ~v1_relat_1(C_15))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.13/1.50  tff(c_593, plain, (![C_58, A_59, B_60]: (k4_xboole_0(k10_relat_1(C_58, A_59), k10_relat_1(C_58, B_60))=k10_relat_1(C_58, k4_xboole_0(A_59, B_60)) | ~v1_funct_1(C_58) | ~v1_relat_1(C_58))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_14, c_16])).
% 3.13/1.50  tff(c_24, plain, (r1_tarski(k10_relat_1('#skF_3', '#skF_1'), k10_relat_1('#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.13/1.50  tff(c_109, plain, (k4_xboole_0(k10_relat_1('#skF_3', '#skF_1'), k10_relat_1('#skF_3', '#skF_2'))=k1_xboole_0), inference(resolution, [status(thm)], [c_24, c_96])).
% 3.13/1.50  tff(c_602, plain, (k10_relat_1('#skF_3', k4_xboole_0('#skF_1', '#skF_2'))=k1_xboole_0 | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_593, c_109])).
% 3.13/1.50  tff(c_628, plain, (k10_relat_1('#skF_3', k4_xboole_0('#skF_1', '#skF_2'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_602])).
% 3.13/1.50  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(A_1, B_2) | k4_xboole_0(A_1, B_2)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.13/1.50  tff(c_326, plain, (![B_44, A_45]: (k9_relat_1(B_44, k10_relat_1(B_44, A_45))=A_45 | ~r1_tarski(A_45, k2_relat_1(B_44)) | ~v1_funct_1(B_44) | ~v1_relat_1(B_44))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.13/1.50  tff(c_1344, plain, (![B_89, A_90]: (k9_relat_1(B_89, k10_relat_1(B_89, A_90))=A_90 | ~v1_funct_1(B_89) | ~v1_relat_1(B_89) | k4_xboole_0(A_90, k2_relat_1(B_89))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_326])).
% 3.13/1.50  tff(c_1356, plain, (k9_relat_1('#skF_3', k1_xboole_0)=k4_xboole_0('#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | k4_xboole_0(k4_xboole_0('#skF_1', '#skF_2'), k2_relat_1('#skF_3'))!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_628, c_1344])).
% 3.13/1.50  tff(c_1366, plain, (k9_relat_1('#skF_3', k1_xboole_0)=k4_xboole_0('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_586, c_28, c_26, c_1356])).
% 3.13/1.50  tff(c_110, plain, (![A_10]: (k4_xboole_0(A_10, A_10)=k1_xboole_0)), inference(resolution, [status(thm)], [c_42, c_96])).
% 3.13/1.50  tff(c_609, plain, (![C_58, B_60]: (k10_relat_1(C_58, k4_xboole_0(B_60, B_60))=k1_xboole_0 | ~v1_funct_1(C_58) | ~v1_relat_1(C_58))), inference(superposition, [status(thm), theory('equality')], [c_593, c_110])).
% 3.13/1.50  tff(c_1495, plain, (![C_98]: (k10_relat_1(C_98, k1_xboole_0)=k1_xboole_0 | ~v1_funct_1(C_98) | ~v1_relat_1(C_98))), inference(demodulation, [status(thm), theory('equality')], [c_110, c_609])).
% 3.13/1.50  tff(c_1498, plain, (k10_relat_1('#skF_3', k1_xboole_0)=k1_xboole_0 | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_28, c_1495])).
% 3.13/1.50  tff(c_1501, plain, (k10_relat_1('#skF_3', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_26, c_1498])).
% 3.13/1.50  tff(c_342, plain, (![B_44, A_1]: (k9_relat_1(B_44, k10_relat_1(B_44, A_1))=A_1 | ~v1_funct_1(B_44) | ~v1_relat_1(B_44) | k4_xboole_0(A_1, k2_relat_1(B_44))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_326])).
% 3.13/1.50  tff(c_1505, plain, (k9_relat_1('#skF_3', k1_xboole_0)=k1_xboole_0 | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | k4_xboole_0(k1_xboole_0, k2_relat_1('#skF_3'))!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_1501, c_342])).
% 3.13/1.50  tff(c_1518, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1088, c_28, c_26, c_1366, c_1505])).
% 3.13/1.50  tff(c_1520, plain, $false, inference(negUnitSimplification, [status(thm)], [c_148, c_1518])).
% 3.13/1.50  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.13/1.50  
% 3.13/1.50  Inference rules
% 3.13/1.50  ----------------------
% 3.13/1.50  #Ref     : 0
% 3.13/1.50  #Sup     : 368
% 3.13/1.50  #Fact    : 0
% 3.13/1.50  #Define  : 0
% 3.13/1.50  #Split   : 1
% 3.13/1.50  #Chain   : 0
% 3.13/1.50  #Close   : 0
% 3.13/1.50  
% 3.13/1.50  Ordering : KBO
% 3.13/1.50  
% 3.13/1.50  Simplification rules
% 3.13/1.50  ----------------------
% 3.13/1.50  #Subsume      : 52
% 3.13/1.50  #Demod        : 184
% 3.13/1.50  #Tautology    : 212
% 3.13/1.50  #SimpNegUnit  : 2
% 3.13/1.50  #BackRed      : 0
% 3.13/1.50  
% 3.13/1.50  #Partial instantiations: 0
% 3.13/1.50  #Strategies tried      : 1
% 3.13/1.50  
% 3.13/1.50  Timing (in seconds)
% 3.13/1.50  ----------------------
% 3.13/1.50  Preprocessing        : 0.28
% 3.13/1.50  Parsing              : 0.15
% 3.13/1.50  CNF conversion       : 0.02
% 3.13/1.50  Main loop            : 0.40
% 3.13/1.50  Inferencing          : 0.15
% 3.13/1.50  Reduction            : 0.14
% 3.13/1.50  Demodulation         : 0.10
% 3.13/1.50  BG Simplification    : 0.02
% 3.13/1.50  Subsumption          : 0.07
% 3.13/1.50  Abstraction          : 0.02
% 3.13/1.50  MUC search           : 0.00
% 3.13/1.50  Cooper               : 0.00
% 3.13/1.50  Total                : 0.72
% 3.13/1.50  Index Insertion      : 0.00
% 3.13/1.50  Index Deletion       : 0.00
% 3.13/1.50  Index Matching       : 0.00
% 3.13/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
