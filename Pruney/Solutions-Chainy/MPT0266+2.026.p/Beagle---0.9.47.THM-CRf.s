%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:29 EST 2020

% Result     : Theorem 48.04s
% Output     : CNFRefutation 48.04s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 107 expanded)
%              Number of leaves         :   38 (  52 expanded)
%              Depth                    :   11
%              Number of atoms          :   73 ( 103 expanded)
%              Number of equality atoms :   49 (  78 expanded)
%              Maximal formula depth    :   24 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k7_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k7_enumset1,type,(
    k7_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_103,negated_conjecture,(
    ~ ! [A,B,C] :
        ( k3_xboole_0(k2_tarski(A,B),C) = k2_tarski(A,B)
       => r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_31,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_35,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).

tff(f_33,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_78,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_80,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_76,axiom,(
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k1_enumset1(A,B,C),k2_enumset1(D,E,F,G)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_enumset1)).

tff(f_82,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_72,axiom,(
    ! [A,B,C,D,E,F,G,H,I] : k7_enumset1(A,B,C,D,E,F,G,H,I) = k2_xboole_0(k2_enumset1(A,B,C,D),k3_enumset1(E,F,G,H,I)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l142_enumset1)).

tff(f_70,axiom,(
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

tff(f_92,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_90,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l49_zfmisc_1)).

tff(f_98,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(c_100,plain,(
    ~ r2_hidden('#skF_3','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_2,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,A_1) = k5_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_6,plain,(
    ! [A_5] : k3_xboole_0(A_5,A_5) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_10,plain,(
    ! [A_10] : k5_xboole_0(A_10,A_10) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_4,plain,(
    ! [A_3] : k2_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_467,plain,(
    ! [A_110,B_111] : k5_xboole_0(k5_xboole_0(A_110,B_111),k2_xboole_0(A_110,B_111)) = k3_xboole_0(A_110,B_111) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_525,plain,(
    ! [A_3] : k5_xboole_0(k5_xboole_0(A_3,A_3),A_3) = k3_xboole_0(A_3,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_467])).

tff(c_531,plain,(
    ! [A_3] : k5_xboole_0(k1_xboole_0,A_3) = A_3 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_10,c_525])).

tff(c_257,plain,(
    ! [A_103,B_104,C_105] : k5_xboole_0(k5_xboole_0(A_103,B_104),C_105) = k5_xboole_0(A_103,k5_xboole_0(B_104,C_105)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_296,plain,(
    ! [A_10,C_105] : k5_xboole_0(A_10,k5_xboole_0(A_10,C_105)) = k5_xboole_0(k1_xboole_0,C_105) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_257])).

tff(c_694,plain,(
    ! [A_118,C_119] : k5_xboole_0(A_118,k5_xboole_0(A_118,C_119)) = C_119 ),
    inference(demodulation,[status(thm),theory(equality)],[c_531,c_296])).

tff(c_761,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k5_xboole_0(B_2,A_1)) = B_2 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_694])).

tff(c_102,plain,(
    k3_xboole_0(k2_tarski('#skF_3','#skF_4'),'#skF_5') = k2_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_12,plain,(
    ! [A_11,B_12] : k5_xboole_0(k5_xboole_0(A_11,B_12),k2_xboole_0(A_11,B_12)) = k3_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_7196,plain,(
    ! [A_352,B_353] : k5_xboole_0(k5_xboole_0(A_352,B_353),k3_xboole_0(A_352,B_353)) = k2_xboole_0(A_352,B_353) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_694])).

tff(c_7411,plain,(
    k5_xboole_0(k5_xboole_0(k2_tarski('#skF_3','#skF_4'),'#skF_5'),k2_tarski('#skF_3','#skF_4')) = k2_xboole_0(k2_tarski('#skF_3','#skF_4'),'#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_102,c_7196])).

tff(c_7445,plain,(
    k2_xboole_0(k2_tarski('#skF_3','#skF_4'),'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_761,c_2,c_2,c_7411])).

tff(c_80,plain,(
    ! [A_46,B_47] : k1_enumset1(A_46,A_46,B_47) = k2_tarski(A_46,B_47) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_82,plain,(
    ! [A_48,B_49,C_50] : k2_enumset1(A_48,A_48,B_49,C_50) = k1_enumset1(A_48,B_49,C_50) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_2009,plain,(
    ! [E_244,D_242,F_243,B_239,G_241,A_238,C_240] : k2_xboole_0(k1_enumset1(A_238,B_239,C_240),k2_enumset1(D_242,E_244,F_243,G_241)) = k5_enumset1(A_238,B_239,C_240,D_242,E_244,F_243,G_241) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_26251,plain,(
    ! [A_595,A_592,B_594,B_593,C_596,C_591] : k5_enumset1(A_592,B_594,C_591,A_595,A_595,B_593,C_596) = k2_xboole_0(k1_enumset1(A_592,B_594,C_591),k1_enumset1(A_595,B_593,C_596)) ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_2009])).

tff(c_26313,plain,(
    ! [A_595,B_593,C_596] : k5_enumset1(A_595,B_593,C_596,A_595,A_595,B_593,C_596) = k1_enumset1(A_595,B_593,C_596) ),
    inference(superposition,[status(thm),theory(equality)],[c_26251,c_4])).

tff(c_78,plain,(
    ! [E_43,G_45,F_44,D_42,A_39,C_41,B_40] : k2_xboole_0(k1_enumset1(A_39,B_40,C_41),k2_enumset1(D_42,E_43,F_44,G_45)) = k5_enumset1(A_39,B_40,C_41,D_42,E_43,F_44,G_45) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_84,plain,(
    ! [A_51,B_52,C_53,D_54] : k3_enumset1(A_51,A_51,B_52,C_53,D_54) = k2_enumset1(A_51,B_52,C_53,D_54) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_3309,plain,(
    ! [F_260,G_263,B_256,E_262,A_257,H_259,D_255,C_261,I_258] : k2_xboole_0(k2_enumset1(A_257,B_256,C_261,D_255),k3_enumset1(E_262,F_260,G_263,H_259,I_258)) = k7_enumset1(A_257,B_256,C_261,D_255,E_262,F_260,G_263,H_259,I_258) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_37236,plain,(
    ! [E_645,A_641,F_644,B_640,G_646,C_642,I_643,H_639] : k7_enumset1(A_641,A_641,B_640,C_642,E_645,F_644,G_646,H_639,I_643) = k2_xboole_0(k1_enumset1(A_641,B_640,C_642),k3_enumset1(E_645,F_644,G_646,H_639,I_643)) ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_3309])).

tff(c_28,plain,(
    ! [H_20,E_17,F_18,I_21,A_13,B_14,K_25,G_19,D_16] : r2_hidden(K_25,k7_enumset1(A_13,B_14,K_25,D_16,E_17,F_18,G_19,H_20,I_21)) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_66037,plain,(
    ! [H_772,E_771,G_769,I_776,F_774,A_775,B_773,C_770] : r2_hidden(B_773,k2_xboole_0(k1_enumset1(A_775,B_773,C_770),k3_enumset1(E_771,F_774,G_769,H_772,I_776))) ),
    inference(superposition,[status(thm),theory(equality)],[c_37236,c_28])).

tff(c_66058,plain,(
    ! [B_52,A_775,B_773,C_770,C_53,D_54,A_51] : r2_hidden(B_773,k2_xboole_0(k1_enumset1(A_775,B_773,C_770),k2_enumset1(A_51,B_52,C_53,D_54))) ),
    inference(superposition,[status(thm),theory(equality)],[c_84,c_66037])).

tff(c_66067,plain,(
    ! [A_779,B_783,C_782,B_778,A_777,D_781,C_780] : r2_hidden(B_783,k5_enumset1(A_779,B_783,C_782,A_777,B_778,C_780,D_781)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_66058])).

tff(c_66087,plain,(
    ! [B_784,A_785,C_786] : r2_hidden(B_784,k1_enumset1(A_785,B_784,C_786)) ),
    inference(superposition,[status(thm),theory(equality)],[c_26313,c_66067])).

tff(c_66707,plain,(
    ! [A_788,B_789] : r2_hidden(A_788,k2_tarski(A_788,B_789)) ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_66087])).

tff(c_171,plain,(
    ! [A_82,B_83] : k3_tarski(k2_tarski(A_82,B_83)) = k2_xboole_0(A_82,B_83) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_90,plain,(
    ! [A_66,B_67] :
      ( r1_tarski(A_66,k3_tarski(B_67))
      | ~ r2_hidden(A_66,B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_177,plain,(
    ! [A_66,A_82,B_83] :
      ( r1_tarski(A_66,k2_xboole_0(A_82,B_83))
      | ~ r2_hidden(A_66,k2_tarski(A_82,B_83)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_171,c_90])).

tff(c_66724,plain,(
    ! [A_790,B_791] : r1_tarski(A_790,k2_xboole_0(A_790,B_791)) ),
    inference(resolution,[status(thm)],[c_66707,c_177])).

tff(c_66756,plain,(
    r1_tarski(k2_tarski('#skF_3','#skF_4'),'#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_7445,c_66724])).

tff(c_98,plain,(
    ! [A_70,C_72,B_71] :
      ( r2_hidden(A_70,C_72)
      | ~ r1_tarski(k2_tarski(A_70,B_71),C_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_66785,plain,(
    r2_hidden('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_66756,c_98])).

tff(c_66790,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_66785])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n016.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:04:04 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 48.04/37.64  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 48.04/37.64  
% 48.04/37.64  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 48.04/37.65  %$ r2_hidden > r1_tarski > k7_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_1 > #skF_4
% 48.04/37.65  
% 48.04/37.65  %Foreground sorts:
% 48.04/37.65  
% 48.04/37.65  
% 48.04/37.65  %Background operators:
% 48.04/37.65  
% 48.04/37.65  
% 48.04/37.65  %Foreground operators:
% 48.04/37.65  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 48.04/37.65  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 48.04/37.65  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 48.04/37.65  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 48.04/37.65  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 48.04/37.65  tff(k7_enumset1, type, k7_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 48.04/37.65  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 48.04/37.65  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 48.04/37.65  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 48.04/37.65  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 48.04/37.65  tff('#skF_5', type, '#skF_5': $i).
% 48.04/37.65  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 48.04/37.65  tff('#skF_3', type, '#skF_3': $i).
% 48.04/37.65  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 48.04/37.65  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 48.04/37.65  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 48.04/37.65  tff(k3_tarski, type, k3_tarski: $i > $i).
% 48.04/37.65  tff('#skF_4', type, '#skF_4': $i).
% 48.04/37.65  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 48.04/37.65  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 48.04/37.65  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 48.04/37.65  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 48.04/37.65  
% 48.04/37.66  tff(f_103, negated_conjecture, ~(![A, B, C]: ((k3_xboole_0(k2_tarski(A, B), C) = k2_tarski(A, B)) => r2_hidden(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_zfmisc_1)).
% 48.04/37.66  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 48.04/37.66  tff(f_31, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 48.04/37.66  tff(f_35, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 48.04/37.66  tff(f_29, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 48.04/37.66  tff(f_37, axiom, (![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_xboole_1)).
% 48.04/37.66  tff(f_33, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 48.04/37.66  tff(f_78, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 48.04/37.66  tff(f_80, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 48.04/37.66  tff(f_76, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k1_enumset1(A, B, C), k2_enumset1(D, E, F, G)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t58_enumset1)).
% 48.04/37.66  tff(f_82, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 48.04/37.66  tff(f_72, axiom, (![A, B, C, D, E, F, G, H, I]: (k7_enumset1(A, B, C, D, E, F, G, H, I) = k2_xboole_0(k2_enumset1(A, B, C, D), k3_enumset1(E, F, G, H, I)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l142_enumset1)).
% 48.04/37.66  tff(f_70, axiom, (![A, B, C, D, E, F, G, H, I, J]: ((J = k7_enumset1(A, B, C, D, E, F, G, H, I)) <=> (![K]: (r2_hidden(K, J) <=> ~((((((((~(K = A) & ~(K = B)) & ~(K = C)) & ~(K = D)) & ~(K = E)) & ~(K = F)) & ~(K = G)) & ~(K = H)) & ~(K = I)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_enumset1)).
% 48.04/37.66  tff(f_92, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 48.04/37.66  tff(f_90, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 48.04/37.66  tff(f_98, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 48.04/37.66  tff(c_100, plain, (~r2_hidden('#skF_3', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_103])).
% 48.04/37.66  tff(c_2, plain, (![B_2, A_1]: (k5_xboole_0(B_2, A_1)=k5_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 48.04/37.66  tff(c_6, plain, (![A_5]: (k3_xboole_0(A_5, A_5)=A_5)), inference(cnfTransformation, [status(thm)], [f_31])).
% 48.04/37.66  tff(c_10, plain, (![A_10]: (k5_xboole_0(A_10, A_10)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 48.04/37.66  tff(c_4, plain, (![A_3]: (k2_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 48.04/37.66  tff(c_467, plain, (![A_110, B_111]: (k5_xboole_0(k5_xboole_0(A_110, B_111), k2_xboole_0(A_110, B_111))=k3_xboole_0(A_110, B_111))), inference(cnfTransformation, [status(thm)], [f_37])).
% 48.04/37.66  tff(c_525, plain, (![A_3]: (k5_xboole_0(k5_xboole_0(A_3, A_3), A_3)=k3_xboole_0(A_3, A_3))), inference(superposition, [status(thm), theory('equality')], [c_4, c_467])).
% 48.04/37.66  tff(c_531, plain, (![A_3]: (k5_xboole_0(k1_xboole_0, A_3)=A_3)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_10, c_525])).
% 48.04/37.66  tff(c_257, plain, (![A_103, B_104, C_105]: (k5_xboole_0(k5_xboole_0(A_103, B_104), C_105)=k5_xboole_0(A_103, k5_xboole_0(B_104, C_105)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 48.04/37.66  tff(c_296, plain, (![A_10, C_105]: (k5_xboole_0(A_10, k5_xboole_0(A_10, C_105))=k5_xboole_0(k1_xboole_0, C_105))), inference(superposition, [status(thm), theory('equality')], [c_10, c_257])).
% 48.04/37.66  tff(c_694, plain, (![A_118, C_119]: (k5_xboole_0(A_118, k5_xboole_0(A_118, C_119))=C_119)), inference(demodulation, [status(thm), theory('equality')], [c_531, c_296])).
% 48.04/37.66  tff(c_761, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k5_xboole_0(B_2, A_1))=B_2)), inference(superposition, [status(thm), theory('equality')], [c_2, c_694])).
% 48.04/37.66  tff(c_102, plain, (k3_xboole_0(k2_tarski('#skF_3', '#skF_4'), '#skF_5')=k2_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_103])).
% 48.04/37.66  tff(c_12, plain, (![A_11, B_12]: (k5_xboole_0(k5_xboole_0(A_11, B_12), k2_xboole_0(A_11, B_12))=k3_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_37])).
% 48.04/37.66  tff(c_7196, plain, (![A_352, B_353]: (k5_xboole_0(k5_xboole_0(A_352, B_353), k3_xboole_0(A_352, B_353))=k2_xboole_0(A_352, B_353))), inference(superposition, [status(thm), theory('equality')], [c_12, c_694])).
% 48.04/37.66  tff(c_7411, plain, (k5_xboole_0(k5_xboole_0(k2_tarski('#skF_3', '#skF_4'), '#skF_5'), k2_tarski('#skF_3', '#skF_4'))=k2_xboole_0(k2_tarski('#skF_3', '#skF_4'), '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_102, c_7196])).
% 48.04/37.66  tff(c_7445, plain, (k2_xboole_0(k2_tarski('#skF_3', '#skF_4'), '#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_761, c_2, c_2, c_7411])).
% 48.04/37.66  tff(c_80, plain, (![A_46, B_47]: (k1_enumset1(A_46, A_46, B_47)=k2_tarski(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_78])).
% 48.04/37.66  tff(c_82, plain, (![A_48, B_49, C_50]: (k2_enumset1(A_48, A_48, B_49, C_50)=k1_enumset1(A_48, B_49, C_50))), inference(cnfTransformation, [status(thm)], [f_80])).
% 48.04/37.66  tff(c_2009, plain, (![E_244, D_242, F_243, B_239, G_241, A_238, C_240]: (k2_xboole_0(k1_enumset1(A_238, B_239, C_240), k2_enumset1(D_242, E_244, F_243, G_241))=k5_enumset1(A_238, B_239, C_240, D_242, E_244, F_243, G_241))), inference(cnfTransformation, [status(thm)], [f_76])).
% 48.04/37.66  tff(c_26251, plain, (![A_595, A_592, B_594, B_593, C_596, C_591]: (k5_enumset1(A_592, B_594, C_591, A_595, A_595, B_593, C_596)=k2_xboole_0(k1_enumset1(A_592, B_594, C_591), k1_enumset1(A_595, B_593, C_596)))), inference(superposition, [status(thm), theory('equality')], [c_82, c_2009])).
% 48.04/37.66  tff(c_26313, plain, (![A_595, B_593, C_596]: (k5_enumset1(A_595, B_593, C_596, A_595, A_595, B_593, C_596)=k1_enumset1(A_595, B_593, C_596))), inference(superposition, [status(thm), theory('equality')], [c_26251, c_4])).
% 48.04/37.66  tff(c_78, plain, (![E_43, G_45, F_44, D_42, A_39, C_41, B_40]: (k2_xboole_0(k1_enumset1(A_39, B_40, C_41), k2_enumset1(D_42, E_43, F_44, G_45))=k5_enumset1(A_39, B_40, C_41, D_42, E_43, F_44, G_45))), inference(cnfTransformation, [status(thm)], [f_76])).
% 48.04/37.66  tff(c_84, plain, (![A_51, B_52, C_53, D_54]: (k3_enumset1(A_51, A_51, B_52, C_53, D_54)=k2_enumset1(A_51, B_52, C_53, D_54))), inference(cnfTransformation, [status(thm)], [f_82])).
% 48.04/37.66  tff(c_3309, plain, (![F_260, G_263, B_256, E_262, A_257, H_259, D_255, C_261, I_258]: (k2_xboole_0(k2_enumset1(A_257, B_256, C_261, D_255), k3_enumset1(E_262, F_260, G_263, H_259, I_258))=k7_enumset1(A_257, B_256, C_261, D_255, E_262, F_260, G_263, H_259, I_258))), inference(cnfTransformation, [status(thm)], [f_72])).
% 48.04/37.66  tff(c_37236, plain, (![E_645, A_641, F_644, B_640, G_646, C_642, I_643, H_639]: (k7_enumset1(A_641, A_641, B_640, C_642, E_645, F_644, G_646, H_639, I_643)=k2_xboole_0(k1_enumset1(A_641, B_640, C_642), k3_enumset1(E_645, F_644, G_646, H_639, I_643)))), inference(superposition, [status(thm), theory('equality')], [c_82, c_3309])).
% 48.04/37.66  tff(c_28, plain, (![H_20, E_17, F_18, I_21, A_13, B_14, K_25, G_19, D_16]: (r2_hidden(K_25, k7_enumset1(A_13, B_14, K_25, D_16, E_17, F_18, G_19, H_20, I_21)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 48.04/37.66  tff(c_66037, plain, (![H_772, E_771, G_769, I_776, F_774, A_775, B_773, C_770]: (r2_hidden(B_773, k2_xboole_0(k1_enumset1(A_775, B_773, C_770), k3_enumset1(E_771, F_774, G_769, H_772, I_776))))), inference(superposition, [status(thm), theory('equality')], [c_37236, c_28])).
% 48.04/37.66  tff(c_66058, plain, (![B_52, A_775, B_773, C_770, C_53, D_54, A_51]: (r2_hidden(B_773, k2_xboole_0(k1_enumset1(A_775, B_773, C_770), k2_enumset1(A_51, B_52, C_53, D_54))))), inference(superposition, [status(thm), theory('equality')], [c_84, c_66037])).
% 48.04/37.66  tff(c_66067, plain, (![A_779, B_783, C_782, B_778, A_777, D_781, C_780]: (r2_hidden(B_783, k5_enumset1(A_779, B_783, C_782, A_777, B_778, C_780, D_781)))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_66058])).
% 48.04/37.66  tff(c_66087, plain, (![B_784, A_785, C_786]: (r2_hidden(B_784, k1_enumset1(A_785, B_784, C_786)))), inference(superposition, [status(thm), theory('equality')], [c_26313, c_66067])).
% 48.04/37.66  tff(c_66707, plain, (![A_788, B_789]: (r2_hidden(A_788, k2_tarski(A_788, B_789)))), inference(superposition, [status(thm), theory('equality')], [c_80, c_66087])).
% 48.04/37.66  tff(c_171, plain, (![A_82, B_83]: (k3_tarski(k2_tarski(A_82, B_83))=k2_xboole_0(A_82, B_83))), inference(cnfTransformation, [status(thm)], [f_92])).
% 48.04/37.66  tff(c_90, plain, (![A_66, B_67]: (r1_tarski(A_66, k3_tarski(B_67)) | ~r2_hidden(A_66, B_67))), inference(cnfTransformation, [status(thm)], [f_90])).
% 48.04/37.66  tff(c_177, plain, (![A_66, A_82, B_83]: (r1_tarski(A_66, k2_xboole_0(A_82, B_83)) | ~r2_hidden(A_66, k2_tarski(A_82, B_83)))), inference(superposition, [status(thm), theory('equality')], [c_171, c_90])).
% 48.04/37.66  tff(c_66724, plain, (![A_790, B_791]: (r1_tarski(A_790, k2_xboole_0(A_790, B_791)))), inference(resolution, [status(thm)], [c_66707, c_177])).
% 48.04/37.66  tff(c_66756, plain, (r1_tarski(k2_tarski('#skF_3', '#skF_4'), '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_7445, c_66724])).
% 48.04/37.66  tff(c_98, plain, (![A_70, C_72, B_71]: (r2_hidden(A_70, C_72) | ~r1_tarski(k2_tarski(A_70, B_71), C_72))), inference(cnfTransformation, [status(thm)], [f_98])).
% 48.04/37.66  tff(c_66785, plain, (r2_hidden('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_66756, c_98])).
% 48.04/37.66  tff(c_66790, plain, $false, inference(negUnitSimplification, [status(thm)], [c_100, c_66785])).
% 48.04/37.66  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 48.04/37.66  
% 48.04/37.66  Inference rules
% 48.04/37.66  ----------------------
% 48.04/37.66  #Ref     : 0
% 48.04/37.66  #Sup     : 17489
% 48.04/37.66  #Fact    : 72
% 48.04/37.66  #Define  : 0
% 48.04/37.66  #Split   : 0
% 48.04/37.66  #Chain   : 0
% 48.04/37.66  #Close   : 0
% 48.04/37.66  
% 48.04/37.66  Ordering : KBO
% 48.04/37.66  
% 48.04/37.66  Simplification rules
% 48.04/37.66  ----------------------
% 48.04/37.66  #Subsume      : 1093
% 48.04/37.66  #Demod        : 26113
% 48.04/37.66  #Tautology    : 5692
% 48.04/37.66  #SimpNegUnit  : 1
% 48.04/37.66  #BackRed      : 4
% 48.04/37.66  
% 48.04/37.66  #Partial instantiations: 0
% 48.04/37.66  #Strategies tried      : 1
% 48.04/37.66  
% 48.04/37.66  Timing (in seconds)
% 48.04/37.66  ----------------------
% 48.04/37.66  Preprocessing        : 0.39
% 48.04/37.66  Parsing              : 0.20
% 48.04/37.66  CNF conversion       : 0.03
% 48.04/37.66  Main loop            : 36.44
% 48.04/37.66  Inferencing          : 2.48
% 48.04/37.66  Reduction            : 15.18
% 48.04/37.67  Demodulation         : 14.60
% 48.04/37.67  BG Simplification    : 0.44
% 48.04/37.67  Subsumption          : 17.80
% 48.04/37.67  Abstraction          : 0.93
% 48.04/37.67  MUC search           : 0.00
% 48.04/37.67  Cooper               : 0.00
% 48.04/37.67  Total                : 36.87
% 48.04/37.67  Index Insertion      : 0.00
% 48.04/37.67  Index Deletion       : 0.00
% 48.04/37.67  Index Matching       : 0.00
% 48.04/37.67  BG Taut test         : 0.00
%------------------------------------------------------------------------------
