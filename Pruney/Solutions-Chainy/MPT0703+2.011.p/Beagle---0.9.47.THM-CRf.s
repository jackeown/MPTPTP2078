%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:10 EST 2020

% Result     : Theorem 4.77s
% Output     : CNFRefutation 4.77s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 121 expanded)
%              Number of leaves         :   32 (  56 expanded)
%              Depth                    :   14
%              Number of atoms          :  100 ( 201 expanded)
%              Number of equality atoms :   44 (  74 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k1_enumset1 > k9_relat_1 > k6_subset_1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_78,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( ( r1_tarski(k10_relat_1(C,A),k10_relat_1(C,B))
            & r1_tarski(A,k2_relat_1(C)) )
         => r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t158_funct_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_xboole_0(B,C))
     => r1_tarski(k4_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_47,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

tff(f_39,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_51,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => k10_relat_1(C,k6_subset_1(A,B)) = k6_subset_1(k10_relat_1(C,A),k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_funct_1)).

tff(f_37,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(A,k2_relat_1(B))
       => k9_relat_1(B,k10_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).

tff(c_32,plain,(
    r1_tarski('#skF_1',k2_relat_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_8,plain,(
    ! [A_5,C_7,B_6] :
      ( r1_tarski(A_5,k2_xboole_0(C_7,B_6))
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_466,plain,(
    ! [A_60,B_61,C_62] :
      ( r1_tarski(k4_xboole_0(A_60,B_61),C_62)
      | ~ r1_tarski(A_60,k2_xboole_0(B_61,C_62)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( k4_xboole_0(A_3,B_4) = k1_xboole_0
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1437,plain,(
    ! [A_98,B_99,C_100] :
      ( k4_xboole_0(k4_xboole_0(A_98,B_99),C_100) = k1_xboole_0
      | ~ r1_tarski(A_98,k2_xboole_0(B_99,C_100)) ) ),
    inference(resolution,[status(thm)],[c_466,c_6])).

tff(c_3518,plain,(
    ! [A_156,C_157,B_158] :
      ( k4_xboole_0(k4_xboole_0(A_156,C_157),B_158) = k1_xboole_0
      | ~ r1_tarski(A_156,B_158) ) ),
    inference(resolution,[status(thm)],[c_8,c_1437])).

tff(c_145,plain,(
    ! [A_40,B_41] :
      ( r1_tarski(A_40,B_41)
      | k4_xboole_0(A_40,B_41) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_30,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_153,plain,(
    k4_xboole_0('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_145,c_30])).

tff(c_38,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_36,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_154,plain,(
    ! [A_42,B_43] : k4_xboole_0(A_42,k4_xboole_0(A_42,B_43)) = k3_xboole_0(A_42,B_43) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_18,plain,(
    ! [A_15] : k4_xboole_0(k1_xboole_0,A_15) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_188,plain,(
    ! [B_44] : k3_xboole_0(k1_xboole_0,B_44) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_154,c_18])).

tff(c_202,plain,(
    ! [B_2] : k3_xboole_0(B_2,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_188])).

tff(c_12,plain,(
    ! [A_9] : k4_xboole_0(A_9,k1_xboole_0) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_176,plain,(
    ! [A_9] : k4_xboole_0(A_9,A_9) = k3_xboole_0(A_9,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_154])).

tff(c_264,plain,(
    ! [A_9] : k4_xboole_0(A_9,A_9) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_202,c_176])).

tff(c_22,plain,(
    ! [A_18,B_19] : k6_subset_1(A_18,B_19) = k4_xboole_0(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_26,plain,(
    ! [C_24,A_22,B_23] :
      ( k6_subset_1(k10_relat_1(C_24,A_22),k10_relat_1(C_24,B_23)) = k10_relat_1(C_24,k6_subset_1(A_22,B_23))
      | ~ v1_funct_1(C_24)
      | ~ v1_relat_1(C_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_653,plain,(
    ! [C_72,A_73,B_74] :
      ( k4_xboole_0(k10_relat_1(C_72,A_73),k10_relat_1(C_72,B_74)) = k10_relat_1(C_72,k4_xboole_0(A_73,B_74))
      | ~ v1_funct_1(C_72)
      | ~ v1_relat_1(C_72) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_22,c_26])).

tff(c_663,plain,(
    ! [C_72,B_74] :
      ( k10_relat_1(C_72,k4_xboole_0(B_74,B_74)) = k1_xboole_0
      | ~ v1_funct_1(C_72)
      | ~ v1_relat_1(C_72) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_653,c_264])).

tff(c_756,plain,(
    ! [C_77] :
      ( k10_relat_1(C_77,k1_xboole_0) = k1_xboole_0
      | ~ v1_funct_1(C_77)
      | ~ v1_relat_1(C_77) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_264,c_663])).

tff(c_759,plain,
    ( k10_relat_1('#skF_3',k1_xboole_0) = k1_xboole_0
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_756])).

tff(c_762,plain,(
    k10_relat_1('#skF_3',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_759])).

tff(c_10,plain,(
    ! [A_8] : r1_tarski(k1_xboole_0,A_8) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_547,plain,(
    ! [B_68,A_69] :
      ( k9_relat_1(B_68,k10_relat_1(B_68,A_69)) = A_69
      | ~ r1_tarski(A_69,k2_relat_1(B_68))
      | ~ v1_funct_1(B_68)
      | ~ v1_relat_1(B_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_777,plain,(
    ! [B_78] :
      ( k9_relat_1(B_78,k10_relat_1(B_78,k1_xboole_0)) = k1_xboole_0
      | ~ v1_funct_1(B_78)
      | ~ v1_relat_1(B_78) ) ),
    inference(resolution,[status(thm)],[c_10,c_547])).

tff(c_786,plain,
    ( k9_relat_1('#skF_3',k1_xboole_0) = k1_xboole_0
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_762,c_777])).

tff(c_790,plain,(
    k9_relat_1('#skF_3',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_786])).

tff(c_34,plain,(
    r1_tarski(k10_relat_1('#skF_3','#skF_1'),k10_relat_1('#skF_3','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_118,plain,(
    ! [A_36,B_37] :
      ( k4_xboole_0(A_36,B_37) = k1_xboole_0
      | ~ r1_tarski(A_36,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_128,plain,(
    k4_xboole_0(k10_relat_1('#skF_3','#skF_1'),k10_relat_1('#skF_3','#skF_2')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_34,c_118])).

tff(c_666,plain,
    ( k10_relat_1('#skF_3',k4_xboole_0('#skF_1','#skF_2')) = k1_xboole_0
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_653,c_128])).

tff(c_683,plain,(
    k10_relat_1('#skF_3',k4_xboole_0('#skF_1','#skF_2')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_666])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | k4_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2060,plain,(
    ! [B_118,A_119] :
      ( k9_relat_1(B_118,k10_relat_1(B_118,A_119)) = A_119
      | ~ v1_funct_1(B_118)
      | ~ v1_relat_1(B_118)
      | k4_xboole_0(A_119,k2_relat_1(B_118)) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_547])).

tff(c_2100,plain,
    ( k9_relat_1('#skF_3',k1_xboole_0) = k4_xboole_0('#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | k4_xboole_0(k4_xboole_0('#skF_1','#skF_2'),k2_relat_1('#skF_3')) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_683,c_2060])).

tff(c_2130,plain,
    ( k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0
    | k4_xboole_0(k4_xboole_0('#skF_1','#skF_2'),k2_relat_1('#skF_3')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_790,c_2100])).

tff(c_2131,plain,(
    k4_xboole_0(k4_xboole_0('#skF_1','#skF_2'),k2_relat_1('#skF_3')) != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_153,c_2130])).

tff(c_3539,plain,(
    ~ r1_tarski('#skF_1',k2_relat_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_3518,c_2131])).

tff(c_3660,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_3539])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:35:37 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.77/1.93  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.77/1.94  
% 4.77/1.94  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.77/1.94  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k1_enumset1 > k9_relat_1 > k6_subset_1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 4.77/1.94  
% 4.77/1.94  %Foreground sorts:
% 4.77/1.94  
% 4.77/1.94  
% 4.77/1.94  %Background operators:
% 4.77/1.94  
% 4.77/1.94  
% 4.77/1.94  %Foreground operators:
% 4.77/1.94  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.77/1.94  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.77/1.94  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.77/1.94  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.77/1.94  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.77/1.94  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.77/1.94  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.77/1.94  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.77/1.94  tff('#skF_2', type, '#skF_2': $i).
% 4.77/1.94  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 4.77/1.94  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 4.77/1.94  tff('#skF_3', type, '#skF_3': $i).
% 4.77/1.94  tff('#skF_1', type, '#skF_1': $i).
% 4.77/1.94  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.77/1.94  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 4.77/1.94  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.77/1.94  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.77/1.94  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.77/1.94  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.77/1.94  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 4.77/1.94  
% 4.77/1.96  tff(f_78, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r1_tarski(k10_relat_1(C, A), k10_relat_1(C, B)) & r1_tarski(A, k2_relat_1(C))) => r1_tarski(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t158_funct_1)).
% 4.77/1.96  tff(f_35, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_xboole_1)).
% 4.77/1.96  tff(f_43, axiom, (![A, B, C]: (r1_tarski(A, k2_xboole_0(B, C)) => r1_tarski(k4_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_xboole_1)).
% 4.77/1.96  tff(f_31, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 4.77/1.96  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 4.77/1.96  tff(f_45, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 4.77/1.96  tff(f_47, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 4.77/1.96  tff(f_39, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 4.77/1.96  tff(f_51, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 4.77/1.96  tff(f_59, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (k10_relat_1(C, k6_subset_1(A, B)) = k6_subset_1(k10_relat_1(C, A), k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t138_funct_1)).
% 4.77/1.96  tff(f_37, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 4.77/1.96  tff(f_67, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(A, k2_relat_1(B)) => (k9_relat_1(B, k10_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t147_funct_1)).
% 4.77/1.96  tff(c_32, plain, (r1_tarski('#skF_1', k2_relat_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.77/1.96  tff(c_8, plain, (![A_5, C_7, B_6]: (r1_tarski(A_5, k2_xboole_0(C_7, B_6)) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.77/1.96  tff(c_466, plain, (![A_60, B_61, C_62]: (r1_tarski(k4_xboole_0(A_60, B_61), C_62) | ~r1_tarski(A_60, k2_xboole_0(B_61, C_62)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.77/1.96  tff(c_6, plain, (![A_3, B_4]: (k4_xboole_0(A_3, B_4)=k1_xboole_0 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.77/1.96  tff(c_1437, plain, (![A_98, B_99, C_100]: (k4_xboole_0(k4_xboole_0(A_98, B_99), C_100)=k1_xboole_0 | ~r1_tarski(A_98, k2_xboole_0(B_99, C_100)))), inference(resolution, [status(thm)], [c_466, c_6])).
% 4.77/1.96  tff(c_3518, plain, (![A_156, C_157, B_158]: (k4_xboole_0(k4_xboole_0(A_156, C_157), B_158)=k1_xboole_0 | ~r1_tarski(A_156, B_158))), inference(resolution, [status(thm)], [c_8, c_1437])).
% 4.77/1.96  tff(c_145, plain, (![A_40, B_41]: (r1_tarski(A_40, B_41) | k4_xboole_0(A_40, B_41)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.77/1.96  tff(c_30, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.77/1.96  tff(c_153, plain, (k4_xboole_0('#skF_1', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_145, c_30])).
% 4.77/1.96  tff(c_38, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.77/1.96  tff(c_36, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.77/1.96  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.77/1.96  tff(c_154, plain, (![A_42, B_43]: (k4_xboole_0(A_42, k4_xboole_0(A_42, B_43))=k3_xboole_0(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.77/1.96  tff(c_18, plain, (![A_15]: (k4_xboole_0(k1_xboole_0, A_15)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.77/1.96  tff(c_188, plain, (![B_44]: (k3_xboole_0(k1_xboole_0, B_44)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_154, c_18])).
% 4.77/1.96  tff(c_202, plain, (![B_2]: (k3_xboole_0(B_2, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_188])).
% 4.77/1.96  tff(c_12, plain, (![A_9]: (k4_xboole_0(A_9, k1_xboole_0)=A_9)), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.77/1.96  tff(c_176, plain, (![A_9]: (k4_xboole_0(A_9, A_9)=k3_xboole_0(A_9, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_154])).
% 4.77/1.96  tff(c_264, plain, (![A_9]: (k4_xboole_0(A_9, A_9)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_202, c_176])).
% 4.77/1.96  tff(c_22, plain, (![A_18, B_19]: (k6_subset_1(A_18, B_19)=k4_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.77/1.96  tff(c_26, plain, (![C_24, A_22, B_23]: (k6_subset_1(k10_relat_1(C_24, A_22), k10_relat_1(C_24, B_23))=k10_relat_1(C_24, k6_subset_1(A_22, B_23)) | ~v1_funct_1(C_24) | ~v1_relat_1(C_24))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.77/1.96  tff(c_653, plain, (![C_72, A_73, B_74]: (k4_xboole_0(k10_relat_1(C_72, A_73), k10_relat_1(C_72, B_74))=k10_relat_1(C_72, k4_xboole_0(A_73, B_74)) | ~v1_funct_1(C_72) | ~v1_relat_1(C_72))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_22, c_26])).
% 4.77/1.96  tff(c_663, plain, (![C_72, B_74]: (k10_relat_1(C_72, k4_xboole_0(B_74, B_74))=k1_xboole_0 | ~v1_funct_1(C_72) | ~v1_relat_1(C_72))), inference(superposition, [status(thm), theory('equality')], [c_653, c_264])).
% 4.77/1.96  tff(c_756, plain, (![C_77]: (k10_relat_1(C_77, k1_xboole_0)=k1_xboole_0 | ~v1_funct_1(C_77) | ~v1_relat_1(C_77))), inference(demodulation, [status(thm), theory('equality')], [c_264, c_663])).
% 4.77/1.96  tff(c_759, plain, (k10_relat_1('#skF_3', k1_xboole_0)=k1_xboole_0 | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_38, c_756])).
% 4.77/1.96  tff(c_762, plain, (k10_relat_1('#skF_3', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_36, c_759])).
% 4.77/1.96  tff(c_10, plain, (![A_8]: (r1_tarski(k1_xboole_0, A_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.77/1.96  tff(c_547, plain, (![B_68, A_69]: (k9_relat_1(B_68, k10_relat_1(B_68, A_69))=A_69 | ~r1_tarski(A_69, k2_relat_1(B_68)) | ~v1_funct_1(B_68) | ~v1_relat_1(B_68))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.77/1.96  tff(c_777, plain, (![B_78]: (k9_relat_1(B_78, k10_relat_1(B_78, k1_xboole_0))=k1_xboole_0 | ~v1_funct_1(B_78) | ~v1_relat_1(B_78))), inference(resolution, [status(thm)], [c_10, c_547])).
% 4.77/1.96  tff(c_786, plain, (k9_relat_1('#skF_3', k1_xboole_0)=k1_xboole_0 | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_762, c_777])).
% 4.77/1.96  tff(c_790, plain, (k9_relat_1('#skF_3', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_786])).
% 4.77/1.96  tff(c_34, plain, (r1_tarski(k10_relat_1('#skF_3', '#skF_1'), k10_relat_1('#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.77/1.96  tff(c_118, plain, (![A_36, B_37]: (k4_xboole_0(A_36, B_37)=k1_xboole_0 | ~r1_tarski(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.77/1.96  tff(c_128, plain, (k4_xboole_0(k10_relat_1('#skF_3', '#skF_1'), k10_relat_1('#skF_3', '#skF_2'))=k1_xboole_0), inference(resolution, [status(thm)], [c_34, c_118])).
% 4.77/1.96  tff(c_666, plain, (k10_relat_1('#skF_3', k4_xboole_0('#skF_1', '#skF_2'))=k1_xboole_0 | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_653, c_128])).
% 4.77/1.96  tff(c_683, plain, (k10_relat_1('#skF_3', k4_xboole_0('#skF_1', '#skF_2'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_666])).
% 4.77/1.96  tff(c_4, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | k4_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.77/1.96  tff(c_2060, plain, (![B_118, A_119]: (k9_relat_1(B_118, k10_relat_1(B_118, A_119))=A_119 | ~v1_funct_1(B_118) | ~v1_relat_1(B_118) | k4_xboole_0(A_119, k2_relat_1(B_118))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_547])).
% 4.77/1.96  tff(c_2100, plain, (k9_relat_1('#skF_3', k1_xboole_0)=k4_xboole_0('#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | k4_xboole_0(k4_xboole_0('#skF_1', '#skF_2'), k2_relat_1('#skF_3'))!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_683, c_2060])).
% 4.77/1.96  tff(c_2130, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0 | k4_xboole_0(k4_xboole_0('#skF_1', '#skF_2'), k2_relat_1('#skF_3'))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_790, c_2100])).
% 4.77/1.96  tff(c_2131, plain, (k4_xboole_0(k4_xboole_0('#skF_1', '#skF_2'), k2_relat_1('#skF_3'))!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_153, c_2130])).
% 4.77/1.96  tff(c_3539, plain, (~r1_tarski('#skF_1', k2_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_3518, c_2131])).
% 4.77/1.96  tff(c_3660, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_3539])).
% 4.77/1.96  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.77/1.96  
% 4.77/1.96  Inference rules
% 4.77/1.96  ----------------------
% 4.77/1.96  #Ref     : 0
% 4.77/1.96  #Sup     : 862
% 4.77/1.96  #Fact    : 0
% 4.77/1.96  #Define  : 0
% 4.77/1.96  #Split   : 4
% 4.77/1.96  #Chain   : 0
% 4.77/1.96  #Close   : 0
% 4.77/1.96  
% 4.77/1.96  Ordering : KBO
% 4.77/1.96  
% 4.77/1.96  Simplification rules
% 4.77/1.96  ----------------------
% 4.77/1.96  #Subsume      : 99
% 4.77/1.96  #Demod        : 582
% 4.77/1.96  #Tautology    : 452
% 4.77/1.96  #SimpNegUnit  : 8
% 4.77/1.96  #BackRed      : 6
% 4.77/1.96  
% 4.77/1.96  #Partial instantiations: 0
% 4.77/1.96  #Strategies tried      : 1
% 4.77/1.96  
% 4.77/1.96  Timing (in seconds)
% 4.77/1.96  ----------------------
% 4.77/1.96  Preprocessing        : 0.32
% 4.77/1.96  Parsing              : 0.18
% 4.77/1.96  CNF conversion       : 0.02
% 4.77/1.96  Main loop            : 0.85
% 4.77/1.96  Inferencing          : 0.29
% 4.77/1.96  Reduction            : 0.33
% 4.77/1.96  Demodulation         : 0.25
% 4.77/1.96  BG Simplification    : 0.03
% 4.77/1.96  Subsumption          : 0.14
% 4.77/1.96  Abstraction          : 0.04
% 4.77/1.96  MUC search           : 0.00
% 4.77/1.96  Cooper               : 0.00
% 4.77/1.96  Total                : 1.21
% 4.77/1.96  Index Insertion      : 0.00
% 4.77/1.96  Index Deletion       : 0.00
% 4.77/1.96  Index Matching       : 0.00
% 4.77/1.96  BG Taut test         : 0.00
%------------------------------------------------------------------------------
