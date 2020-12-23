%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:38 EST 2020

% Result     : Theorem 56.21s
% Output     : CNFRefutation 56.21s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 103 expanded)
%              Number of leaves         :   44 (  51 expanded)
%              Depth                    :   13
%              Number of atoms          :   86 ( 106 expanded)
%              Number of equality atoms :   53 (  63 expanded)
%              Maximal formula depth    :   24 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k7_enumset1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_1 > #skF_3 > #skF_4 > #skF_5 > #skF_6 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k7_enumset1,type,(
    k7_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_110,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(k2_xboole_0(k1_tarski(A),B),B)
       => r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_zfmisc_1)).

tff(f_91,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_93,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_95,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_97,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_99,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_101,axiom,(
    ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

tff(f_103,axiom,(
    ! [A,B,C,D,E,F,G] : k6_enumset1(A,A,B,C,D,E,F,G) = k5_enumset1(A,B,C,D,E,F,G) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

tff(f_89,axiom,(
    ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k5_enumset1(A,B,C,D,E,F,G),k1_tarski(H)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_enumset1)).

tff(f_87,axiom,(
    ! [A,B,C,D,E,F,G,H,I] : k7_enumset1(A,B,C,D,E,F,G,H,I) = k2_xboole_0(k6_enumset1(A,B,C,D,E,F,G,H),k1_tarski(I)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t134_enumset1)).

tff(f_85,axiom,(
    ! [A,B,C,D,E,F,G,H,I,J] :
      ( J = k7_enumset1(A,B,C,D,E,F,G,H,I)
    <=> ! [K] :
          ( r2_hidden(K,J)
        <=> ~ ( K != A
              & K != B
              & K != C
              & K != D
              & K != E
              & K != F
              & K != G
              & K != H
              & K != I ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_enumset1)).

tff(f_48,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_52,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_46,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_50,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_38,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

tff(c_118,plain,(
    ~ r2_hidden('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_102,plain,(
    ! [A_52] : k2_tarski(A_52,A_52) = k1_tarski(A_52) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_104,plain,(
    ! [A_53,B_54] : k1_enumset1(A_53,A_53,B_54) = k2_tarski(A_53,B_54) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_106,plain,(
    ! [A_55,B_56,C_57] : k2_enumset1(A_55,A_55,B_56,C_57) = k1_enumset1(A_55,B_56,C_57) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_108,plain,(
    ! [A_58,B_59,C_60,D_61] : k3_enumset1(A_58,A_58,B_59,C_60,D_61) = k2_enumset1(A_58,B_59,C_60,D_61) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_110,plain,(
    ! [B_63,E_66,C_64,A_62,D_65] : k4_enumset1(A_62,A_62,B_63,C_64,D_65,E_66) = k3_enumset1(A_62,B_63,C_64,D_65,E_66) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_112,plain,(
    ! [D_70,B_68,F_72,A_67,C_69,E_71] : k5_enumset1(A_67,A_67,B_68,C_69,D_70,E_71,F_72) = k4_enumset1(A_67,B_68,C_69,D_70,E_71,F_72) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_114,plain,(
    ! [C_75,E_77,B_74,G_79,F_78,A_73,D_76] : k6_enumset1(A_73,A_73,B_74,C_75,D_76,E_77,F_78,G_79) = k5_enumset1(A_73,B_74,C_75,D_76,E_77,F_78,G_79) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_100,plain,(
    ! [C_46,E_48,F_49,G_50,A_44,B_45,H_51,D_47] : k2_xboole_0(k5_enumset1(A_44,B_45,C_46,D_47,E_48,F_49,G_50),k1_tarski(H_51)) = k6_enumset1(A_44,B_45,C_46,D_47,E_48,F_49,G_50,H_51) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_11126,plain,(
    ! [F_505,G_504,C_506,H_502,A_501,I_503,D_508,E_507,B_509] : k2_xboole_0(k6_enumset1(A_501,B_509,C_506,D_508,E_507,F_505,G_504,H_502),k1_tarski(I_503)) = k7_enumset1(A_501,B_509,C_506,D_508,E_507,F_505,G_504,H_502,I_503) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_11180,plain,(
    ! [C_75,E_77,B_74,G_79,F_78,I_503,A_73,D_76] : k7_enumset1(A_73,A_73,B_74,C_75,D_76,E_77,F_78,G_79,I_503) = k2_xboole_0(k5_enumset1(A_73,B_74,C_75,D_76,E_77,F_78,G_79),k1_tarski(I_503)) ),
    inference(superposition,[status(thm),theory(equality)],[c_114,c_11126])).

tff(c_87650,plain,(
    ! [A_156550,C_156544,I_156548,B_156547,E_156549,F_156543,D_156546,G_156545] : k7_enumset1(A_156550,A_156550,B_156547,C_156544,D_156546,E_156549,F_156543,G_156545,I_156548) = k6_enumset1(A_156550,B_156547,C_156544,D_156546,E_156549,F_156543,G_156545,I_156548) ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_11180])).

tff(c_50,plain,(
    ! [G_28,E_26,F_27,K_34,H_29,A_22,B_23,C_24,I_30] : r2_hidden(K_34,k7_enumset1(A_22,B_23,C_24,K_34,E_26,F_27,G_28,H_29,I_30)) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_88322,plain,(
    ! [I_157274,D_157273,G_157277,F_157271,E_157272,A_157275,B_157276,C_157278] : r2_hidden(C_157278,k6_enumset1(A_157275,B_157276,C_157278,D_157273,E_157272,F_157271,G_157277,I_157274)) ),
    inference(superposition,[status(thm),theory(equality)],[c_87650,c_50])).

tff(c_88335,plain,(
    ! [G_158001,A_158005,B_158003,D_158002,E_158004,F_157999,C_158000] : r2_hidden(B_158003,k5_enumset1(A_158005,B_158003,C_158000,D_158002,E_158004,F_157999,G_158001)) ),
    inference(superposition,[status(thm),theory(equality)],[c_114,c_88322])).

tff(c_88348,plain,(
    ! [B_158726,D_158731,C_158730,A_158728,F_158729,E_158727] : r2_hidden(A_158728,k4_enumset1(A_158728,B_158726,C_158730,D_158731,E_158727,F_158729)) ),
    inference(superposition,[status(thm),theory(equality)],[c_112,c_88335])).

tff(c_88361,plain,(
    ! [B_159455,C_159453,E_159452,A_159454,D_159456] : r2_hidden(A_159454,k3_enumset1(A_159454,B_159455,C_159453,D_159456,E_159452)) ),
    inference(superposition,[status(thm),theory(equality)],[c_110,c_88348])).

tff(c_88374,plain,(
    ! [A_160177,B_160178,C_160179,D_160180] : r2_hidden(A_160177,k2_enumset1(A_160177,B_160178,C_160179,D_160180)) ),
    inference(superposition,[status(thm),theory(equality)],[c_108,c_88361])).

tff(c_88387,plain,(
    ! [A_160901,B_160902,C_160903] : r2_hidden(A_160901,k1_enumset1(A_160901,B_160902,C_160903)) ),
    inference(superposition,[status(thm),theory(equality)],[c_106,c_88374])).

tff(c_88400,plain,(
    ! [A_161624,B_161625] : r2_hidden(A_161624,k2_tarski(A_161624,B_161625)) ),
    inference(superposition,[status(thm),theory(equality)],[c_104,c_88387])).

tff(c_88413,plain,(
    ! [A_162346] : r2_hidden(A_162346,k1_tarski(A_162346)) ),
    inference(superposition,[status(thm),theory(equality)],[c_102,c_88400])).

tff(c_32,plain,(
    ! [A_15,B_16] : r1_tarski(A_15,k2_xboole_0(A_15,B_16)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_36,plain,(
    ! [A_20,B_21] : k5_xboole_0(A_20,k4_xboole_0(B_21,A_20)) = k2_xboole_0(A_20,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_245,plain,(
    ! [A_96,B_97] : k5_xboole_0(A_96,k3_xboole_0(A_96,B_97)) = k4_xboole_0(A_96,B_97) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_254,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k3_xboole_0(B_2,A_1)) = k4_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_245])).

tff(c_4,plain,(
    ! [B_4,A_3] : k5_xboole_0(B_4,A_3) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_30,plain,(
    ! [A_13,B_14] : k5_xboole_0(A_13,k3_xboole_0(A_13,B_14)) = k4_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_343,plain,(
    ! [A_118,B_119,C_120] : k5_xboole_0(k5_xboole_0(A_118,B_119),C_120) = k5_xboole_0(A_118,k5_xboole_0(B_119,C_120)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_2604,plain,(
    ! [A_251,B_252,C_253] : k5_xboole_0(A_251,k5_xboole_0(k3_xboole_0(A_251,B_252),C_253)) = k5_xboole_0(k4_xboole_0(A_251,B_252),C_253) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_343])).

tff(c_3463,plain,(
    ! [A_266,A_267,B_268] : k5_xboole_0(A_266,k5_xboole_0(A_267,k3_xboole_0(A_266,B_268))) = k5_xboole_0(k4_xboole_0(A_266,B_268),A_267) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_2604])).

tff(c_3622,plain,(
    ! [B_2,A_1] : k5_xboole_0(k4_xboole_0(B_2,A_1),A_1) = k5_xboole_0(B_2,k4_xboole_0(A_1,B_2)) ),
    inference(superposition,[status(thm),theory(equality)],[c_254,c_3463])).

tff(c_3667,plain,(
    ! [B_269,A_270] : k5_xboole_0(k4_xboole_0(B_269,A_270),A_270) = k2_xboole_0(B_269,A_270) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_3622])).

tff(c_3841,plain,(
    ! [A_274,B_275] : k5_xboole_0(A_274,k4_xboole_0(B_275,A_274)) = k2_xboole_0(B_275,A_274) ),
    inference(superposition,[status(thm),theory(equality)],[c_3667,c_4])).

tff(c_3913,plain,(
    ! [B_275,A_274] : k2_xboole_0(B_275,A_274) = k2_xboole_0(A_274,B_275) ),
    inference(superposition,[status(thm),theory(equality)],[c_3841,c_36])).

tff(c_120,plain,(
    r1_tarski(k2_xboole_0(k1_tarski('#skF_5'),'#skF_6'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_269,plain,(
    ! [B_100,A_101] :
      ( B_100 = A_101
      | ~ r1_tarski(B_100,A_101)
      | ~ r1_tarski(A_101,B_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_279,plain,
    ( k2_xboole_0(k1_tarski('#skF_5'),'#skF_6') = '#skF_6'
    | ~ r1_tarski('#skF_6',k2_xboole_0(k1_tarski('#skF_5'),'#skF_6')) ),
    inference(resolution,[status(thm)],[c_120,c_269])).

tff(c_325,plain,(
    ~ r1_tarski('#skF_6',k2_xboole_0(k1_tarski('#skF_5'),'#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_279])).

tff(c_3944,plain,(
    ~ r1_tarski('#skF_6',k2_xboole_0('#skF_6',k1_tarski('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3913,c_325])).

tff(c_3948,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_3944])).

tff(c_3949,plain,(
    k2_xboole_0(k1_tarski('#skF_5'),'#skF_6') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_279])).

tff(c_10,plain,(
    ! [D_10,A_5,B_6] :
      ( ~ r2_hidden(D_10,A_5)
      | r2_hidden(D_10,k2_xboole_0(A_5,B_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_3956,plain,(
    ! [D_10] :
      ( ~ r2_hidden(D_10,k1_tarski('#skF_5'))
      | r2_hidden(D_10,'#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3949,c_10])).

tff(c_88417,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_88413,c_3956])).

tff(c_88430,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_118,c_88417])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 20:32:12 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 56.21/42.69  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 56.21/42.69  
% 56.21/42.69  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 56.21/42.70  %$ r2_hidden > r1_tarski > k7_enumset1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_1 > #skF_3 > #skF_4 > #skF_5 > #skF_6 > #skF_2
% 56.21/42.70  
% 56.21/42.70  %Foreground sorts:
% 56.21/42.70  
% 56.21/42.70  
% 56.21/42.70  %Background operators:
% 56.21/42.70  
% 56.21/42.70  
% 56.21/42.70  %Foreground operators:
% 56.21/42.70  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 56.21/42.70  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 56.21/42.70  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 56.21/42.70  tff(k1_tarski, type, k1_tarski: $i > $i).
% 56.21/42.70  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 56.21/42.70  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 56.21/42.70  tff(k7_enumset1, type, k7_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 56.21/42.70  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 56.21/42.70  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 56.21/42.70  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 56.21/42.70  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 56.21/42.70  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 56.21/42.70  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 56.21/42.70  tff('#skF_5', type, '#skF_5': $i).
% 56.21/42.70  tff('#skF_6', type, '#skF_6': $i).
% 56.21/42.70  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 56.21/42.70  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 56.21/42.70  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 56.21/42.70  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 56.21/42.70  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 56.21/42.70  tff(k3_tarski, type, k3_tarski: $i > $i).
% 56.21/42.70  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 56.21/42.70  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 56.21/42.70  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 56.21/42.70  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 56.21/42.70  
% 56.21/42.71  tff(f_110, negated_conjecture, ~(![A, B]: (r1_tarski(k2_xboole_0(k1_tarski(A), B), B) => r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_zfmisc_1)).
% 56.21/42.71  tff(f_91, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 56.21/42.71  tff(f_93, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 56.21/42.71  tff(f_95, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 56.21/42.71  tff(f_97, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 56.21/42.71  tff(f_99, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 56.21/42.71  tff(f_101, axiom, (![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 56.21/42.71  tff(f_103, axiom, (![A, B, C, D, E, F, G]: (k6_enumset1(A, A, B, C, D, E, F, G) = k5_enumset1(A, B, C, D, E, F, G))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_enumset1)).
% 56.21/42.71  tff(f_89, axiom, (![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k5_enumset1(A, B, C, D, E, F, G), k1_tarski(H)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t68_enumset1)).
% 56.21/42.71  tff(f_87, axiom, (![A, B, C, D, E, F, G, H, I]: (k7_enumset1(A, B, C, D, E, F, G, H, I) = k2_xboole_0(k6_enumset1(A, B, C, D, E, F, G, H), k1_tarski(I)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t134_enumset1)).
% 56.21/42.71  tff(f_85, axiom, (![A, B, C, D, E, F, G, H, I, J]: ((J = k7_enumset1(A, B, C, D, E, F, G, H, I)) <=> (![K]: (r2_hidden(K, J) <=> ~((((((((~(K = A) & ~(K = B)) & ~(K = C)) & ~(K = D)) & ~(K = E)) & ~(K = F)) & ~(K = G)) & ~(K = H)) & ~(K = I)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_enumset1)).
% 56.21/42.71  tff(f_48, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 56.21/42.71  tff(f_52, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 56.21/42.71  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 56.21/42.71  tff(f_46, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 56.21/42.71  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 56.21/42.71  tff(f_50, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 56.21/42.71  tff(f_44, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 56.21/42.71  tff(f_38, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_xboole_0)).
% 56.21/42.71  tff(c_118, plain, (~r2_hidden('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_110])).
% 56.21/42.71  tff(c_102, plain, (![A_52]: (k2_tarski(A_52, A_52)=k1_tarski(A_52))), inference(cnfTransformation, [status(thm)], [f_91])).
% 56.21/42.71  tff(c_104, plain, (![A_53, B_54]: (k1_enumset1(A_53, A_53, B_54)=k2_tarski(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_93])).
% 56.21/42.71  tff(c_106, plain, (![A_55, B_56, C_57]: (k2_enumset1(A_55, A_55, B_56, C_57)=k1_enumset1(A_55, B_56, C_57))), inference(cnfTransformation, [status(thm)], [f_95])).
% 56.21/42.71  tff(c_108, plain, (![A_58, B_59, C_60, D_61]: (k3_enumset1(A_58, A_58, B_59, C_60, D_61)=k2_enumset1(A_58, B_59, C_60, D_61))), inference(cnfTransformation, [status(thm)], [f_97])).
% 56.21/42.71  tff(c_110, plain, (![B_63, E_66, C_64, A_62, D_65]: (k4_enumset1(A_62, A_62, B_63, C_64, D_65, E_66)=k3_enumset1(A_62, B_63, C_64, D_65, E_66))), inference(cnfTransformation, [status(thm)], [f_99])).
% 56.21/42.71  tff(c_112, plain, (![D_70, B_68, F_72, A_67, C_69, E_71]: (k5_enumset1(A_67, A_67, B_68, C_69, D_70, E_71, F_72)=k4_enumset1(A_67, B_68, C_69, D_70, E_71, F_72))), inference(cnfTransformation, [status(thm)], [f_101])).
% 56.21/42.71  tff(c_114, plain, (![C_75, E_77, B_74, G_79, F_78, A_73, D_76]: (k6_enumset1(A_73, A_73, B_74, C_75, D_76, E_77, F_78, G_79)=k5_enumset1(A_73, B_74, C_75, D_76, E_77, F_78, G_79))), inference(cnfTransformation, [status(thm)], [f_103])).
% 56.21/42.71  tff(c_100, plain, (![C_46, E_48, F_49, G_50, A_44, B_45, H_51, D_47]: (k2_xboole_0(k5_enumset1(A_44, B_45, C_46, D_47, E_48, F_49, G_50), k1_tarski(H_51))=k6_enumset1(A_44, B_45, C_46, D_47, E_48, F_49, G_50, H_51))), inference(cnfTransformation, [status(thm)], [f_89])).
% 56.21/42.71  tff(c_11126, plain, (![F_505, G_504, C_506, H_502, A_501, I_503, D_508, E_507, B_509]: (k2_xboole_0(k6_enumset1(A_501, B_509, C_506, D_508, E_507, F_505, G_504, H_502), k1_tarski(I_503))=k7_enumset1(A_501, B_509, C_506, D_508, E_507, F_505, G_504, H_502, I_503))), inference(cnfTransformation, [status(thm)], [f_87])).
% 56.21/42.72  tff(c_11180, plain, (![C_75, E_77, B_74, G_79, F_78, I_503, A_73, D_76]: (k7_enumset1(A_73, A_73, B_74, C_75, D_76, E_77, F_78, G_79, I_503)=k2_xboole_0(k5_enumset1(A_73, B_74, C_75, D_76, E_77, F_78, G_79), k1_tarski(I_503)))), inference(superposition, [status(thm), theory('equality')], [c_114, c_11126])).
% 56.21/42.72  tff(c_87650, plain, (![A_156550, C_156544, I_156548, B_156547, E_156549, F_156543, D_156546, G_156545]: (k7_enumset1(A_156550, A_156550, B_156547, C_156544, D_156546, E_156549, F_156543, G_156545, I_156548)=k6_enumset1(A_156550, B_156547, C_156544, D_156546, E_156549, F_156543, G_156545, I_156548))), inference(demodulation, [status(thm), theory('equality')], [c_100, c_11180])).
% 56.21/42.72  tff(c_50, plain, (![G_28, E_26, F_27, K_34, H_29, A_22, B_23, C_24, I_30]: (r2_hidden(K_34, k7_enumset1(A_22, B_23, C_24, K_34, E_26, F_27, G_28, H_29, I_30)))), inference(cnfTransformation, [status(thm)], [f_85])).
% 56.21/42.72  tff(c_88322, plain, (![I_157274, D_157273, G_157277, F_157271, E_157272, A_157275, B_157276, C_157278]: (r2_hidden(C_157278, k6_enumset1(A_157275, B_157276, C_157278, D_157273, E_157272, F_157271, G_157277, I_157274)))), inference(superposition, [status(thm), theory('equality')], [c_87650, c_50])).
% 56.21/42.72  tff(c_88335, plain, (![G_158001, A_158005, B_158003, D_158002, E_158004, F_157999, C_158000]: (r2_hidden(B_158003, k5_enumset1(A_158005, B_158003, C_158000, D_158002, E_158004, F_157999, G_158001)))), inference(superposition, [status(thm), theory('equality')], [c_114, c_88322])).
% 56.21/42.72  tff(c_88348, plain, (![B_158726, D_158731, C_158730, A_158728, F_158729, E_158727]: (r2_hidden(A_158728, k4_enumset1(A_158728, B_158726, C_158730, D_158731, E_158727, F_158729)))), inference(superposition, [status(thm), theory('equality')], [c_112, c_88335])).
% 56.21/42.72  tff(c_88361, plain, (![B_159455, C_159453, E_159452, A_159454, D_159456]: (r2_hidden(A_159454, k3_enumset1(A_159454, B_159455, C_159453, D_159456, E_159452)))), inference(superposition, [status(thm), theory('equality')], [c_110, c_88348])).
% 56.21/42.72  tff(c_88374, plain, (![A_160177, B_160178, C_160179, D_160180]: (r2_hidden(A_160177, k2_enumset1(A_160177, B_160178, C_160179, D_160180)))), inference(superposition, [status(thm), theory('equality')], [c_108, c_88361])).
% 56.21/42.72  tff(c_88387, plain, (![A_160901, B_160902, C_160903]: (r2_hidden(A_160901, k1_enumset1(A_160901, B_160902, C_160903)))), inference(superposition, [status(thm), theory('equality')], [c_106, c_88374])).
% 56.21/42.72  tff(c_88400, plain, (![A_161624, B_161625]: (r2_hidden(A_161624, k2_tarski(A_161624, B_161625)))), inference(superposition, [status(thm), theory('equality')], [c_104, c_88387])).
% 56.21/42.72  tff(c_88413, plain, (![A_162346]: (r2_hidden(A_162346, k1_tarski(A_162346)))), inference(superposition, [status(thm), theory('equality')], [c_102, c_88400])).
% 56.21/42.72  tff(c_32, plain, (![A_15, B_16]: (r1_tarski(A_15, k2_xboole_0(A_15, B_16)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 56.21/42.72  tff(c_36, plain, (![A_20, B_21]: (k5_xboole_0(A_20, k4_xboole_0(B_21, A_20))=k2_xboole_0(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_52])).
% 56.21/42.72  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 56.21/42.72  tff(c_245, plain, (![A_96, B_97]: (k5_xboole_0(A_96, k3_xboole_0(A_96, B_97))=k4_xboole_0(A_96, B_97))), inference(cnfTransformation, [status(thm)], [f_46])).
% 56.21/42.72  tff(c_254, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k3_xboole_0(B_2, A_1))=k4_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_245])).
% 56.21/42.72  tff(c_4, plain, (![B_4, A_3]: (k5_xboole_0(B_4, A_3)=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 56.21/42.72  tff(c_30, plain, (![A_13, B_14]: (k5_xboole_0(A_13, k3_xboole_0(A_13, B_14))=k4_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_46])).
% 56.21/42.72  tff(c_343, plain, (![A_118, B_119, C_120]: (k5_xboole_0(k5_xboole_0(A_118, B_119), C_120)=k5_xboole_0(A_118, k5_xboole_0(B_119, C_120)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 56.21/42.72  tff(c_2604, plain, (![A_251, B_252, C_253]: (k5_xboole_0(A_251, k5_xboole_0(k3_xboole_0(A_251, B_252), C_253))=k5_xboole_0(k4_xboole_0(A_251, B_252), C_253))), inference(superposition, [status(thm), theory('equality')], [c_30, c_343])).
% 56.21/42.72  tff(c_3463, plain, (![A_266, A_267, B_268]: (k5_xboole_0(A_266, k5_xboole_0(A_267, k3_xboole_0(A_266, B_268)))=k5_xboole_0(k4_xboole_0(A_266, B_268), A_267))), inference(superposition, [status(thm), theory('equality')], [c_4, c_2604])).
% 56.21/42.72  tff(c_3622, plain, (![B_2, A_1]: (k5_xboole_0(k4_xboole_0(B_2, A_1), A_1)=k5_xboole_0(B_2, k4_xboole_0(A_1, B_2)))), inference(superposition, [status(thm), theory('equality')], [c_254, c_3463])).
% 56.21/42.72  tff(c_3667, plain, (![B_269, A_270]: (k5_xboole_0(k4_xboole_0(B_269, A_270), A_270)=k2_xboole_0(B_269, A_270))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_3622])).
% 56.21/42.72  tff(c_3841, plain, (![A_274, B_275]: (k5_xboole_0(A_274, k4_xboole_0(B_275, A_274))=k2_xboole_0(B_275, A_274))), inference(superposition, [status(thm), theory('equality')], [c_3667, c_4])).
% 56.21/42.72  tff(c_3913, plain, (![B_275, A_274]: (k2_xboole_0(B_275, A_274)=k2_xboole_0(A_274, B_275))), inference(superposition, [status(thm), theory('equality')], [c_3841, c_36])).
% 56.21/42.72  tff(c_120, plain, (r1_tarski(k2_xboole_0(k1_tarski('#skF_5'), '#skF_6'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_110])).
% 56.21/42.72  tff(c_269, plain, (![B_100, A_101]: (B_100=A_101 | ~r1_tarski(B_100, A_101) | ~r1_tarski(A_101, B_100))), inference(cnfTransformation, [status(thm)], [f_44])).
% 56.21/42.72  tff(c_279, plain, (k2_xboole_0(k1_tarski('#skF_5'), '#skF_6')='#skF_6' | ~r1_tarski('#skF_6', k2_xboole_0(k1_tarski('#skF_5'), '#skF_6'))), inference(resolution, [status(thm)], [c_120, c_269])).
% 56.21/42.72  tff(c_325, plain, (~r1_tarski('#skF_6', k2_xboole_0(k1_tarski('#skF_5'), '#skF_6'))), inference(splitLeft, [status(thm)], [c_279])).
% 56.21/42.72  tff(c_3944, plain, (~r1_tarski('#skF_6', k2_xboole_0('#skF_6', k1_tarski('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_3913, c_325])).
% 56.21/42.72  tff(c_3948, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_3944])).
% 56.21/42.72  tff(c_3949, plain, (k2_xboole_0(k1_tarski('#skF_5'), '#skF_6')='#skF_6'), inference(splitRight, [status(thm)], [c_279])).
% 56.21/42.72  tff(c_10, plain, (![D_10, A_5, B_6]: (~r2_hidden(D_10, A_5) | r2_hidden(D_10, k2_xboole_0(A_5, B_6)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 56.21/42.72  tff(c_3956, plain, (![D_10]: (~r2_hidden(D_10, k1_tarski('#skF_5')) | r2_hidden(D_10, '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_3949, c_10])).
% 56.21/42.72  tff(c_88417, plain, (r2_hidden('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_88413, c_3956])).
% 56.21/42.72  tff(c_88430, plain, $false, inference(negUnitSimplification, [status(thm)], [c_118, c_88417])).
% 56.21/42.72  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 56.21/42.72  
% 56.21/42.72  Inference rules
% 56.21/42.72  ----------------------
% 56.21/42.72  #Ref     : 0
% 56.21/42.72  #Sup     : 19622
% 56.21/42.72  #Fact    : 672
% 56.21/42.72  #Define  : 0
% 56.21/42.72  #Split   : 5
% 56.21/42.72  #Chain   : 0
% 56.21/42.72  #Close   : 0
% 56.21/42.72  
% 56.21/42.72  Ordering : KBO
% 56.21/42.72  
% 56.21/42.72  Simplification rules
% 56.21/42.72  ----------------------
% 56.21/42.72  #Subsume      : 7445
% 56.21/42.72  #Demod        : 7492
% 56.21/42.72  #Tautology    : 2754
% 56.21/42.72  #SimpNegUnit  : 1
% 56.21/42.72  #BackRed      : 12
% 56.21/42.72  
% 56.21/42.72  #Partial instantiations: 40480
% 56.21/42.72  #Strategies tried      : 1
% 56.21/42.72  
% 56.21/42.72  Timing (in seconds)
% 56.21/42.72  ----------------------
% 56.21/42.72  Preprocessing        : 0.38
% 56.21/42.72  Parsing              : 0.17
% 56.21/42.72  CNF conversion       : 0.03
% 56.21/42.72  Main loop            : 41.53
% 56.21/42.72  Inferencing          : 9.20
% 56.21/42.72  Reduction            : 11.48
% 56.21/42.72  Demodulation         : 10.71
% 56.21/42.72  BG Simplification    : 0.66
% 56.21/42.72  Subsumption          : 19.56
% 56.21/42.72  Abstraction          : 2.32
% 56.21/42.72  MUC search           : 0.00
% 56.21/42.72  Cooper               : 0.00
% 56.21/42.72  Total                : 41.95
% 56.21/42.72  Index Insertion      : 0.00
% 56.21/42.72  Index Deletion       : 0.00
% 56.21/42.72  Index Matching       : 0.00
% 56.21/42.72  BG Taut test         : 0.00
%------------------------------------------------------------------------------
