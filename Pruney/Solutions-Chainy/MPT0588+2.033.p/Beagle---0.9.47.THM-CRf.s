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
% DateTime   : Thu Dec  3 10:02:07 EST 2020

% Result     : Theorem 3.84s
% Output     : CNFRefutation 3.84s
% Verified   : 
% Statistics : Number of formulae       :   63 (  72 expanded)
%              Number of leaves         :   34 (  39 expanded)
%              Depth                    :   13
%              Number of atoms          :   59 (  70 expanded)
%              Number of equality atoms :   33 (  41 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_72,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => k7_relat_1(B,A) = k7_relat_1(B,k3_xboole_0(k1_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t192_relat_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t89_relat_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).

tff(f_29,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_35,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_33,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k2_tarski(A,B),k1_enumset1(C,D,E)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(D,C,B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_49,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(c_36,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_26,plain,(
    ! [A_44,B_45] :
      ( v1_relat_1(k7_relat_1(A_44,B_45))
      | ~ v1_relat_1(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_30,plain,(
    ! [B_50,A_49] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_50,A_49)),k1_relat_1(B_50))
      | ~ v1_relat_1(B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_200,plain,(
    ! [B_76,A_77] :
      ( k7_relat_1(B_76,A_77) = B_76
      | ~ r1_tarski(k1_relat_1(B_76),A_77)
      | ~ v1_relat_1(B_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_937,plain,(
    ! [B_143,A_144] :
      ( k7_relat_1(k7_relat_1(B_143,A_144),k1_relat_1(B_143)) = k7_relat_1(B_143,A_144)
      | ~ v1_relat_1(k7_relat_1(B_143,A_144))
      | ~ v1_relat_1(B_143) ) ),
    inference(resolution,[status(thm)],[c_30,c_200])).

tff(c_28,plain,(
    ! [C_48,A_46,B_47] :
      ( k7_relat_1(k7_relat_1(C_48,A_46),B_47) = k7_relat_1(C_48,k3_xboole_0(A_46,B_47))
      | ~ v1_relat_1(C_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_2748,plain,(
    ! [B_200,A_201] :
      ( k7_relat_1(B_200,k3_xboole_0(A_201,k1_relat_1(B_200))) = k7_relat_1(B_200,A_201)
      | ~ v1_relat_1(B_200)
      | ~ v1_relat_1(k7_relat_1(B_200,A_201))
      | ~ v1_relat_1(B_200) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_937,c_28])).

tff(c_4,plain,(
    ! [A_5,B_6] : k2_xboole_0(k1_tarski(A_5),k1_tarski(B_6)) = k2_tarski(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_10,plain,(
    ! [A_13,B_14] : k1_enumset1(A_13,A_13,B_14) = k2_tarski(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_8,plain,(
    ! [A_12] : k2_tarski(A_12,A_12) = k1_tarski(A_12) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_14,plain,(
    ! [A_18,B_19,C_20,D_21] : k3_enumset1(A_18,A_18,B_19,C_20,D_21) = k2_enumset1(A_18,B_19,C_20,D_21) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_315,plain,(
    ! [A_98,E_99,D_95,C_97,B_96] : k2_xboole_0(k2_tarski(A_98,B_96),k1_enumset1(C_97,D_95,E_99)) = k3_enumset1(A_98,B_96,C_97,D_95,E_99) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_333,plain,(
    ! [A_12,C_97,D_95,E_99] : k3_enumset1(A_12,A_12,C_97,D_95,E_99) = k2_xboole_0(k1_tarski(A_12),k1_enumset1(C_97,D_95,E_99)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_315])).

tff(c_337,plain,(
    ! [A_100,C_101,D_102,E_103] : k2_xboole_0(k1_tarski(A_100),k1_enumset1(C_101,D_102,E_103)) = k2_enumset1(A_100,C_101,D_102,E_103) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_333])).

tff(c_357,plain,(
    ! [A_104,A_105,B_106] : k2_xboole_0(k1_tarski(A_104),k2_tarski(A_105,B_106)) = k2_enumset1(A_104,A_105,A_105,B_106) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_337])).

tff(c_153,plain,(
    ! [D_72,C_73,B_74,A_75] : k2_enumset1(D_72,C_73,B_74,A_75) = k2_enumset1(A_75,B_74,C_73,D_72) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_12,plain,(
    ! [A_15,B_16,C_17] : k2_enumset1(A_15,A_15,B_16,C_17) = k1_enumset1(A_15,B_16,C_17) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_169,plain,(
    ! [D_72,C_73,B_74] : k2_enumset1(D_72,C_73,B_74,B_74) = k1_enumset1(B_74,C_73,D_72) ),
    inference(superposition,[status(thm),theory(equality)],[c_153,c_12])).

tff(c_367,plain,(
    ! [A_104,B_106] : k2_xboole_0(k1_tarski(A_104),k2_tarski(B_106,B_106)) = k1_enumset1(B_106,B_106,A_104) ),
    inference(superposition,[status(thm),theory(equality)],[c_357,c_169])).

tff(c_412,plain,(
    ! [B_107,A_108] : k2_tarski(B_107,A_108) = k2_tarski(A_108,B_107) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_10,c_8,c_367])).

tff(c_24,plain,(
    ! [A_42,B_43] : k1_setfam_1(k2_tarski(A_42,B_43)) = k3_xboole_0(A_42,B_43) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_595,plain,(
    ! [B_126,A_127] : k1_setfam_1(k2_tarski(B_126,A_127)) = k3_xboole_0(A_127,B_126) ),
    inference(superposition,[status(thm),theory(equality)],[c_412,c_24])).

tff(c_601,plain,(
    ! [B_126,A_127] : k3_xboole_0(B_126,A_127) = k3_xboole_0(A_127,B_126) ),
    inference(superposition,[status(thm),theory(equality)],[c_595,c_24])).

tff(c_34,plain,(
    k7_relat_1('#skF_2',k3_xboole_0(k1_relat_1('#skF_2'),'#skF_1')) != k7_relat_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_621,plain,(
    k7_relat_1('#skF_2',k3_xboole_0('#skF_1',k1_relat_1('#skF_2'))) != k7_relat_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_601,c_34])).

tff(c_2770,plain,
    ( ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1'))
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_2748,c_621])).

tff(c_2810,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_2770])).

tff(c_2814,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_2810])).

tff(c_2818,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_2814])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n006.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:51:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.84/1.71  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.84/1.71  
% 3.84/1.71  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.84/1.71  %$ r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 3.84/1.71  
% 3.84/1.71  %Foreground sorts:
% 3.84/1.71  
% 3.84/1.71  
% 3.84/1.71  %Background operators:
% 3.84/1.71  
% 3.84/1.71  
% 3.84/1.71  %Foreground operators:
% 3.84/1.71  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.84/1.71  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.84/1.71  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.84/1.71  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.84/1.71  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.84/1.71  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.84/1.71  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.84/1.71  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.84/1.71  tff('#skF_2', type, '#skF_2': $i).
% 3.84/1.71  tff('#skF_1', type, '#skF_1': $i).
% 3.84/1.71  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.84/1.71  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.84/1.71  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.84/1.71  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.84/1.71  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.84/1.71  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.84/1.71  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.84/1.71  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.84/1.71  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.84/1.71  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.84/1.71  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.84/1.71  
% 3.84/1.73  tff(f_72, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k7_relat_1(B, k3_xboole_0(k1_relat_1(B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t192_relat_1)).
% 3.84/1.73  tff(f_53, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 3.84/1.73  tff(f_61, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), k1_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t89_relat_1)).
% 3.84/1.73  tff(f_67, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t97_relat_1)).
% 3.84/1.73  tff(f_57, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, k3_xboole_0(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_relat_1)).
% 3.84/1.73  tff(f_29, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_enumset1)).
% 3.84/1.73  tff(f_35, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 3.84/1.73  tff(f_33, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 3.84/1.73  tff(f_39, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 3.84/1.73  tff(f_31, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k2_tarski(A, B), k1_enumset1(C, D, E)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_enumset1)).
% 3.84/1.73  tff(f_27, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(D, C, B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t125_enumset1)).
% 3.84/1.73  tff(f_37, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 3.84/1.73  tff(f_49, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 3.84/1.73  tff(c_36, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.84/1.73  tff(c_26, plain, (![A_44, B_45]: (v1_relat_1(k7_relat_1(A_44, B_45)) | ~v1_relat_1(A_44))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.84/1.73  tff(c_30, plain, (![B_50, A_49]: (r1_tarski(k1_relat_1(k7_relat_1(B_50, A_49)), k1_relat_1(B_50)) | ~v1_relat_1(B_50))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.84/1.73  tff(c_200, plain, (![B_76, A_77]: (k7_relat_1(B_76, A_77)=B_76 | ~r1_tarski(k1_relat_1(B_76), A_77) | ~v1_relat_1(B_76))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.84/1.73  tff(c_937, plain, (![B_143, A_144]: (k7_relat_1(k7_relat_1(B_143, A_144), k1_relat_1(B_143))=k7_relat_1(B_143, A_144) | ~v1_relat_1(k7_relat_1(B_143, A_144)) | ~v1_relat_1(B_143))), inference(resolution, [status(thm)], [c_30, c_200])).
% 3.84/1.73  tff(c_28, plain, (![C_48, A_46, B_47]: (k7_relat_1(k7_relat_1(C_48, A_46), B_47)=k7_relat_1(C_48, k3_xboole_0(A_46, B_47)) | ~v1_relat_1(C_48))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.84/1.73  tff(c_2748, plain, (![B_200, A_201]: (k7_relat_1(B_200, k3_xboole_0(A_201, k1_relat_1(B_200)))=k7_relat_1(B_200, A_201) | ~v1_relat_1(B_200) | ~v1_relat_1(k7_relat_1(B_200, A_201)) | ~v1_relat_1(B_200))), inference(superposition, [status(thm), theory('equality')], [c_937, c_28])).
% 3.84/1.73  tff(c_4, plain, (![A_5, B_6]: (k2_xboole_0(k1_tarski(A_5), k1_tarski(B_6))=k2_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.84/1.73  tff(c_10, plain, (![A_13, B_14]: (k1_enumset1(A_13, A_13, B_14)=k2_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.84/1.73  tff(c_8, plain, (![A_12]: (k2_tarski(A_12, A_12)=k1_tarski(A_12))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.84/1.73  tff(c_14, plain, (![A_18, B_19, C_20, D_21]: (k3_enumset1(A_18, A_18, B_19, C_20, D_21)=k2_enumset1(A_18, B_19, C_20, D_21))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.84/1.73  tff(c_315, plain, (![A_98, E_99, D_95, C_97, B_96]: (k2_xboole_0(k2_tarski(A_98, B_96), k1_enumset1(C_97, D_95, E_99))=k3_enumset1(A_98, B_96, C_97, D_95, E_99))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.84/1.73  tff(c_333, plain, (![A_12, C_97, D_95, E_99]: (k3_enumset1(A_12, A_12, C_97, D_95, E_99)=k2_xboole_0(k1_tarski(A_12), k1_enumset1(C_97, D_95, E_99)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_315])).
% 3.84/1.73  tff(c_337, plain, (![A_100, C_101, D_102, E_103]: (k2_xboole_0(k1_tarski(A_100), k1_enumset1(C_101, D_102, E_103))=k2_enumset1(A_100, C_101, D_102, E_103))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_333])).
% 3.84/1.73  tff(c_357, plain, (![A_104, A_105, B_106]: (k2_xboole_0(k1_tarski(A_104), k2_tarski(A_105, B_106))=k2_enumset1(A_104, A_105, A_105, B_106))), inference(superposition, [status(thm), theory('equality')], [c_10, c_337])).
% 3.84/1.73  tff(c_153, plain, (![D_72, C_73, B_74, A_75]: (k2_enumset1(D_72, C_73, B_74, A_75)=k2_enumset1(A_75, B_74, C_73, D_72))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.84/1.73  tff(c_12, plain, (![A_15, B_16, C_17]: (k2_enumset1(A_15, A_15, B_16, C_17)=k1_enumset1(A_15, B_16, C_17))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.84/1.73  tff(c_169, plain, (![D_72, C_73, B_74]: (k2_enumset1(D_72, C_73, B_74, B_74)=k1_enumset1(B_74, C_73, D_72))), inference(superposition, [status(thm), theory('equality')], [c_153, c_12])).
% 3.84/1.73  tff(c_367, plain, (![A_104, B_106]: (k2_xboole_0(k1_tarski(A_104), k2_tarski(B_106, B_106))=k1_enumset1(B_106, B_106, A_104))), inference(superposition, [status(thm), theory('equality')], [c_357, c_169])).
% 3.84/1.73  tff(c_412, plain, (![B_107, A_108]: (k2_tarski(B_107, A_108)=k2_tarski(A_108, B_107))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_10, c_8, c_367])).
% 3.84/1.73  tff(c_24, plain, (![A_42, B_43]: (k1_setfam_1(k2_tarski(A_42, B_43))=k3_xboole_0(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.84/1.73  tff(c_595, plain, (![B_126, A_127]: (k1_setfam_1(k2_tarski(B_126, A_127))=k3_xboole_0(A_127, B_126))), inference(superposition, [status(thm), theory('equality')], [c_412, c_24])).
% 3.84/1.73  tff(c_601, plain, (![B_126, A_127]: (k3_xboole_0(B_126, A_127)=k3_xboole_0(A_127, B_126))), inference(superposition, [status(thm), theory('equality')], [c_595, c_24])).
% 3.84/1.73  tff(c_34, plain, (k7_relat_1('#skF_2', k3_xboole_0(k1_relat_1('#skF_2'), '#skF_1'))!=k7_relat_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.84/1.73  tff(c_621, plain, (k7_relat_1('#skF_2', k3_xboole_0('#skF_1', k1_relat_1('#skF_2')))!=k7_relat_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_601, c_34])).
% 3.84/1.73  tff(c_2770, plain, (~v1_relat_1(k7_relat_1('#skF_2', '#skF_1')) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_2748, c_621])).
% 3.84/1.73  tff(c_2810, plain, (~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_2770])).
% 3.84/1.73  tff(c_2814, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_26, c_2810])).
% 3.84/1.73  tff(c_2818, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_2814])).
% 3.84/1.73  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.84/1.73  
% 3.84/1.73  Inference rules
% 3.84/1.73  ----------------------
% 3.84/1.73  #Ref     : 0
% 3.84/1.73  #Sup     : 680
% 3.84/1.73  #Fact    : 0
% 3.84/1.73  #Define  : 0
% 3.84/1.73  #Split   : 0
% 3.84/1.73  #Chain   : 0
% 3.84/1.73  #Close   : 0
% 3.84/1.73  
% 3.84/1.73  Ordering : KBO
% 3.84/1.73  
% 3.84/1.73  Simplification rules
% 3.84/1.73  ----------------------
% 3.84/1.73  #Subsume      : 94
% 3.84/1.73  #Demod        : 444
% 3.84/1.73  #Tautology    : 416
% 3.84/1.73  #SimpNegUnit  : 0
% 3.84/1.73  #BackRed      : 1
% 3.84/1.73  
% 3.84/1.73  #Partial instantiations: 0
% 3.84/1.73  #Strategies tried      : 1
% 3.84/1.73  
% 3.84/1.73  Timing (in seconds)
% 3.84/1.73  ----------------------
% 3.84/1.73  Preprocessing        : 0.31
% 3.84/1.73  Parsing              : 0.16
% 3.84/1.73  CNF conversion       : 0.02
% 3.84/1.73  Main loop            : 0.60
% 3.84/1.73  Inferencing          : 0.23
% 3.84/1.73  Reduction            : 0.24
% 3.84/1.73  Demodulation         : 0.20
% 3.84/1.73  BG Simplification    : 0.03
% 3.84/1.73  Subsumption          : 0.08
% 3.84/1.73  Abstraction          : 0.04
% 3.84/1.73  MUC search           : 0.00
% 3.84/1.73  Cooper               : 0.00
% 3.84/1.73  Total                : 0.94
% 3.84/1.73  Index Insertion      : 0.00
% 3.84/1.73  Index Deletion       : 0.00
% 3.84/1.73  Index Matching       : 0.00
% 3.84/1.73  BG Taut test         : 0.00
%------------------------------------------------------------------------------
