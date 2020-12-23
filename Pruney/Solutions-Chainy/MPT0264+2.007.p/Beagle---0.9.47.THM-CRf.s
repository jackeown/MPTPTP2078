%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:21 EST 2020

% Result     : Theorem 11.72s
% Output     : CNFRefutation 11.72s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 350 expanded)
%              Number of leaves         :   30 ( 131 expanded)
%              Depth                    :   14
%              Number of atoms          :   76 ( 352 expanded)
%              Number of equality atoms :   63 ( 335 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_71,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k3_xboole_0(k2_tarski(A,B),C) = k1_tarski(A)
          & r2_hidden(B,C)
          & A != B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_zfmisc_1)).

tff(f_46,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_44,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_48,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_42,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_enumset1(A,B,C),k1_tarski(D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).

tff(f_33,axiom,(
    ! [A,B] : k3_xboole_0(A,k2_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_31,axiom,(
    ! [A,B,C] : k3_xboole_0(k3_xboole_0(A,B),C) = k3_xboole_0(A,k3_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_62,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k3_xboole_0(B,k1_tarski(A)) = k1_tarski(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l31_zfmisc_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( k3_xboole_0(A,k1_tarski(B)) = k1_tarski(B)
     => r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l29_zfmisc_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(c_40,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_42,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_26,plain,(
    ! [A_20,B_21] : k1_enumset1(A_20,A_20,B_21) = k2_tarski(A_20,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_24,plain,(
    ! [A_19] : k2_tarski(A_19,A_19) = k1_tarski(A_19) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_28,plain,(
    ! [A_22,B_23,C_24] : k2_enumset1(A_22,A_22,B_23,C_24) = k1_enumset1(A_22,B_23,C_24) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_1056,plain,(
    ! [A_94,B_95,C_96,D_97] : k2_xboole_0(k1_enumset1(A_94,B_95,C_96),k1_tarski(D_97)) = k2_enumset1(A_94,B_95,C_96,D_97) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_1080,plain,(
    ! [A_20,B_21,D_97] : k2_xboole_0(k2_tarski(A_20,B_21),k1_tarski(D_97)) = k2_enumset1(A_20,A_20,B_21,D_97) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_1056])).

tff(c_1180,plain,(
    ! [A_108,B_109,D_110] : k2_xboole_0(k2_tarski(A_108,B_109),k1_tarski(D_110)) = k1_enumset1(A_108,B_109,D_110) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_1080])).

tff(c_1210,plain,(
    ! [A_19,D_110] : k2_xboole_0(k1_tarski(A_19),k1_tarski(D_110)) = k1_enumset1(A_19,A_19,D_110) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_1180])).

tff(c_1215,plain,(
    ! [A_111,D_112] : k2_xboole_0(k1_tarski(A_111),k1_tarski(D_112)) = k2_tarski(A_111,D_112) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_1210])).

tff(c_8,plain,(
    ! [A_8,B_9] : k3_xboole_0(A_8,k2_xboole_0(A_8,B_9)) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1236,plain,(
    ! [A_111,D_112] : k3_xboole_0(k1_tarski(A_111),k2_tarski(A_111,D_112)) = k1_tarski(A_111) ),
    inference(superposition,[status(thm),theory(equality)],[c_1215,c_8])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_1354,plain,(
    ! [D_120,A_121] : k2_xboole_0(k1_tarski(D_120),k1_tarski(A_121)) = k2_tarski(A_121,D_120) ),
    inference(superposition,[status(thm),theory(equality)],[c_1215,c_2])).

tff(c_1214,plain,(
    ! [A_19,D_110] : k2_xboole_0(k1_tarski(A_19),k1_tarski(D_110)) = k2_tarski(A_19,D_110) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_1210])).

tff(c_1360,plain,(
    ! [D_120,A_121] : k2_tarski(D_120,A_121) = k2_tarski(A_121,D_120) ),
    inference(superposition,[status(thm),theory(equality)],[c_1354,c_1214])).

tff(c_44,plain,(
    k3_xboole_0(k2_tarski('#skF_3','#skF_4'),'#skF_5') = k1_tarski('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_247,plain,(
    ! [A_65,B_66,C_67] : k3_xboole_0(k3_xboole_0(A_65,B_66),C_67) = k3_xboole_0(A_65,k3_xboole_0(B_66,C_67)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_646,plain,(
    ! [C_88,A_89,B_90] : k3_xboole_0(C_88,k3_xboole_0(A_89,B_90)) = k3_xboole_0(A_89,k3_xboole_0(B_90,C_88)) ),
    inference(superposition,[status(thm),theory(equality)],[c_247,c_4])).

tff(c_842,plain,(
    ! [A_89] : k3_xboole_0('#skF_5',k3_xboole_0(A_89,k2_tarski('#skF_3','#skF_4'))) = k3_xboole_0(A_89,k1_tarski('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_646])).

tff(c_1583,plain,(
    ! [A_128] : k3_xboole_0('#skF_5',k3_xboole_0(A_128,k2_tarski('#skF_4','#skF_3'))) = k3_xboole_0(A_128,k1_tarski('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1360,c_842])).

tff(c_1608,plain,(
    k3_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_3')) = k3_xboole_0('#skF_5',k1_tarski('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1236,c_1583])).

tff(c_38,plain,(
    ! [B_43,A_42] :
      ( k3_xboole_0(B_43,k1_tarski(A_42)) = k1_tarski(A_42)
      | ~ r2_hidden(A_42,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_443,plain,(
    ! [C_80] : k3_xboole_0(k2_tarski('#skF_3','#skF_4'),k3_xboole_0('#skF_5',C_80)) = k3_xboole_0(k1_tarski('#skF_3'),C_80) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_247])).

tff(c_456,plain,(
    ! [A_42] :
      ( k3_xboole_0(k2_tarski('#skF_3','#skF_4'),k1_tarski(A_42)) = k3_xboole_0(k1_tarski('#skF_3'),k1_tarski(A_42))
      | ~ r2_hidden(A_42,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_443])).

tff(c_20353,plain,(
    ! [A_378] :
      ( k3_xboole_0(k2_tarski('#skF_4','#skF_3'),k1_tarski(A_378)) = k3_xboole_0(k1_tarski('#skF_3'),k1_tarski(A_378))
      | ~ r2_hidden(A_378,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1360,c_456])).

tff(c_1230,plain,(
    ! [D_112,A_111] : k2_xboole_0(k1_tarski(D_112),k1_tarski(A_111)) = k2_tarski(A_111,D_112) ),
    inference(superposition,[status(thm),theory(equality)],[c_1215,c_2])).

tff(c_70,plain,(
    ! [B_50,A_51] : k2_xboole_0(B_50,A_51) = k2_xboole_0(A_51,B_50) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_85,plain,(
    ! [A_51,B_50] : k3_xboole_0(A_51,k2_xboole_0(B_50,A_51)) = A_51 ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_8])).

tff(c_4311,plain,(
    ! [B_231,A_232,A_233] : k3_xboole_0(k2_xboole_0(B_231,A_232),k3_xboole_0(A_233,A_232)) = k3_xboole_0(A_233,A_232) ),
    inference(superposition,[status(thm),theory(equality)],[c_85,c_646])).

tff(c_1770,plain,(
    ! [A_134,B_135,C_136] : k3_xboole_0(A_134,k3_xboole_0(k2_xboole_0(A_134,B_135),C_136)) = k3_xboole_0(A_134,C_136) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_247])).

tff(c_1881,plain,(
    ! [B_2,A_1,C_136] : k3_xboole_0(B_2,k3_xboole_0(k2_xboole_0(A_1,B_2),C_136)) = k3_xboole_0(B_2,C_136) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1770])).

tff(c_4339,plain,(
    ! [A_1,B_231,A_232] : k3_xboole_0(k2_xboole_0(A_1,k2_xboole_0(B_231,A_232)),A_232) = k3_xboole_0(k2_xboole_0(B_231,A_232),A_232) ),
    inference(superposition,[status(thm),theory(equality)],[c_4311,c_1881])).

tff(c_4536,plain,(
    ! [A_1,B_231,A_232] : k3_xboole_0(k2_xboole_0(A_1,k2_xboole_0(B_231,A_232)),A_232) = A_232 ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_4,c_4339])).

tff(c_4576,plain,(
    ! [A_234,B_235,A_236] : k3_xboole_0(k2_xboole_0(A_234,k2_xboole_0(B_235,A_236)),A_236) = A_236 ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_4,c_4339])).

tff(c_848,plain,(
    ! [B_50,A_51,A_89] : k3_xboole_0(k2_xboole_0(B_50,A_51),k3_xboole_0(A_89,A_51)) = k3_xboole_0(A_89,A_51) ),
    inference(superposition,[status(thm),theory(equality)],[c_85,c_646])).

tff(c_4582,plain,(
    ! [B_50,A_236,A_234,B_235] : k3_xboole_0(k2_xboole_0(B_50,A_236),A_236) = k3_xboole_0(k2_xboole_0(A_234,k2_xboole_0(B_235,A_236)),A_236) ),
    inference(superposition,[status(thm),theory(equality)],[c_4576,c_848])).

tff(c_4738,plain,(
    ! [B_237,A_238] : k3_xboole_0(k2_xboole_0(B_237,A_238),A_238) = A_238 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4536,c_4582])).

tff(c_4833,plain,(
    ! [A_111,D_112] : k3_xboole_0(k2_tarski(A_111,D_112),k1_tarski(A_111)) = k1_tarski(A_111) ),
    inference(superposition,[status(thm),theory(equality)],[c_1230,c_4738])).

tff(c_20405,plain,
    ( k3_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) = k1_tarski('#skF_4')
    | ~ r2_hidden('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_20353,c_4833])).

tff(c_20486,plain,(
    k3_xboole_0('#skF_5',k1_tarski('#skF_4')) = k1_tarski('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_1608,c_4,c_20405])).

tff(c_905,plain,(
    ! [B_91,A_92,C_93] : k3_xboole_0(k3_xboole_0(B_91,A_92),C_93) = k3_xboole_0(A_92,k3_xboole_0(B_91,C_93)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_247])).

tff(c_1011,plain,(
    ! [C_93] : k3_xboole_0('#skF_5',k3_xboole_0(k2_tarski('#skF_3','#skF_4'),C_93)) = k3_xboole_0(k1_tarski('#skF_3'),C_93) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_905])).

tff(c_6585,plain,(
    ! [C_261] : k3_xboole_0('#skF_5',k3_xboole_0(k2_tarski('#skF_4','#skF_3'),C_261)) = k3_xboole_0(k1_tarski('#skF_3'),C_261) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1360,c_1011])).

tff(c_6649,plain,(
    k3_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) = k3_xboole_0('#skF_5',k1_tarski('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_4833,c_6585])).

tff(c_20498,plain,(
    k3_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) = k1_tarski('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20486,c_6649])).

tff(c_36,plain,(
    ! [B_41,A_40] :
      ( r2_hidden(B_41,A_40)
      | k3_xboole_0(A_40,k1_tarski(B_41)) != k1_tarski(B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_20728,plain,(
    r2_hidden('#skF_4',k1_tarski('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_20498,c_36])).

tff(c_10,plain,(
    ! [C_14,A_10] :
      ( C_14 = A_10
      | ~ r2_hidden(C_14,k1_tarski(A_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_20733,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_20728,c_10])).

tff(c_20737,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_20733])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:14:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.72/5.09  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.72/5.10  
% 11.72/5.10  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.72/5.10  %$ r2_hidden > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 11.72/5.10  
% 11.72/5.10  %Foreground sorts:
% 11.72/5.10  
% 11.72/5.10  
% 11.72/5.10  %Background operators:
% 11.72/5.10  
% 11.72/5.10  
% 11.72/5.10  %Foreground operators:
% 11.72/5.10  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.72/5.10  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 11.72/5.10  tff(k1_tarski, type, k1_tarski: $i > $i).
% 11.72/5.10  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 11.72/5.10  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 11.72/5.10  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 11.72/5.10  tff('#skF_5', type, '#skF_5': $i).
% 11.72/5.10  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 11.72/5.10  tff('#skF_3', type, '#skF_3': $i).
% 11.72/5.10  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 11.72/5.10  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.72/5.10  tff('#skF_4', type, '#skF_4': $i).
% 11.72/5.10  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.72/5.10  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 11.72/5.10  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 11.72/5.10  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 11.72/5.10  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 11.72/5.10  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 11.72/5.10  
% 11.72/5.12  tff(f_71, negated_conjecture, ~(![A, B, C]: ~(((k3_xboole_0(k2_tarski(A, B), C) = k1_tarski(A)) & r2_hidden(B, C)) & ~(A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_zfmisc_1)).
% 11.72/5.12  tff(f_46, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 11.72/5.12  tff(f_44, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 11.72/5.12  tff(f_48, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 11.72/5.12  tff(f_42, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_enumset1(A, B, C), k1_tarski(D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_enumset1)).
% 11.72/5.12  tff(f_33, axiom, (![A, B]: (k3_xboole_0(A, k2_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_xboole_1)).
% 11.72/5.12  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 11.72/5.12  tff(f_31, axiom, (![A, B, C]: (k3_xboole_0(k3_xboole_0(A, B), C) = k3_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_xboole_1)).
% 11.72/5.12  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 11.72/5.12  tff(f_62, axiom, (![A, B]: (r2_hidden(A, B) => (k3_xboole_0(B, k1_tarski(A)) = k1_tarski(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l31_zfmisc_1)).
% 11.72/5.12  tff(f_58, axiom, (![A, B]: ((k3_xboole_0(A, k1_tarski(B)) = k1_tarski(B)) => r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l29_zfmisc_1)).
% 11.72/5.12  tff(f_40, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 11.72/5.12  tff(c_40, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_71])).
% 11.72/5.12  tff(c_42, plain, (r2_hidden('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_71])).
% 11.72/5.12  tff(c_26, plain, (![A_20, B_21]: (k1_enumset1(A_20, A_20, B_21)=k2_tarski(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_46])).
% 11.72/5.12  tff(c_24, plain, (![A_19]: (k2_tarski(A_19, A_19)=k1_tarski(A_19))), inference(cnfTransformation, [status(thm)], [f_44])).
% 11.72/5.12  tff(c_28, plain, (![A_22, B_23, C_24]: (k2_enumset1(A_22, A_22, B_23, C_24)=k1_enumset1(A_22, B_23, C_24))), inference(cnfTransformation, [status(thm)], [f_48])).
% 11.72/5.12  tff(c_1056, plain, (![A_94, B_95, C_96, D_97]: (k2_xboole_0(k1_enumset1(A_94, B_95, C_96), k1_tarski(D_97))=k2_enumset1(A_94, B_95, C_96, D_97))), inference(cnfTransformation, [status(thm)], [f_42])).
% 11.72/5.12  tff(c_1080, plain, (![A_20, B_21, D_97]: (k2_xboole_0(k2_tarski(A_20, B_21), k1_tarski(D_97))=k2_enumset1(A_20, A_20, B_21, D_97))), inference(superposition, [status(thm), theory('equality')], [c_26, c_1056])).
% 11.72/5.12  tff(c_1180, plain, (![A_108, B_109, D_110]: (k2_xboole_0(k2_tarski(A_108, B_109), k1_tarski(D_110))=k1_enumset1(A_108, B_109, D_110))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_1080])).
% 11.72/5.12  tff(c_1210, plain, (![A_19, D_110]: (k2_xboole_0(k1_tarski(A_19), k1_tarski(D_110))=k1_enumset1(A_19, A_19, D_110))), inference(superposition, [status(thm), theory('equality')], [c_24, c_1180])).
% 11.72/5.12  tff(c_1215, plain, (![A_111, D_112]: (k2_xboole_0(k1_tarski(A_111), k1_tarski(D_112))=k2_tarski(A_111, D_112))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_1210])).
% 11.72/5.12  tff(c_8, plain, (![A_8, B_9]: (k3_xboole_0(A_8, k2_xboole_0(A_8, B_9))=A_8)), inference(cnfTransformation, [status(thm)], [f_33])).
% 11.72/5.12  tff(c_1236, plain, (![A_111, D_112]: (k3_xboole_0(k1_tarski(A_111), k2_tarski(A_111, D_112))=k1_tarski(A_111))), inference(superposition, [status(thm), theory('equality')], [c_1215, c_8])).
% 11.72/5.12  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 11.72/5.12  tff(c_1354, plain, (![D_120, A_121]: (k2_xboole_0(k1_tarski(D_120), k1_tarski(A_121))=k2_tarski(A_121, D_120))), inference(superposition, [status(thm), theory('equality')], [c_1215, c_2])).
% 11.72/5.12  tff(c_1214, plain, (![A_19, D_110]: (k2_xboole_0(k1_tarski(A_19), k1_tarski(D_110))=k2_tarski(A_19, D_110))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_1210])).
% 11.72/5.12  tff(c_1360, plain, (![D_120, A_121]: (k2_tarski(D_120, A_121)=k2_tarski(A_121, D_120))), inference(superposition, [status(thm), theory('equality')], [c_1354, c_1214])).
% 11.72/5.12  tff(c_44, plain, (k3_xboole_0(k2_tarski('#skF_3', '#skF_4'), '#skF_5')=k1_tarski('#skF_3')), inference(cnfTransformation, [status(thm)], [f_71])).
% 11.72/5.12  tff(c_247, plain, (![A_65, B_66, C_67]: (k3_xboole_0(k3_xboole_0(A_65, B_66), C_67)=k3_xboole_0(A_65, k3_xboole_0(B_66, C_67)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 11.72/5.12  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(B_4, A_3)=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 11.72/5.12  tff(c_646, plain, (![C_88, A_89, B_90]: (k3_xboole_0(C_88, k3_xboole_0(A_89, B_90))=k3_xboole_0(A_89, k3_xboole_0(B_90, C_88)))), inference(superposition, [status(thm), theory('equality')], [c_247, c_4])).
% 11.72/5.12  tff(c_842, plain, (![A_89]: (k3_xboole_0('#skF_5', k3_xboole_0(A_89, k2_tarski('#skF_3', '#skF_4')))=k3_xboole_0(A_89, k1_tarski('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_44, c_646])).
% 11.72/5.12  tff(c_1583, plain, (![A_128]: (k3_xboole_0('#skF_5', k3_xboole_0(A_128, k2_tarski('#skF_4', '#skF_3')))=k3_xboole_0(A_128, k1_tarski('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_1360, c_842])).
% 11.72/5.12  tff(c_1608, plain, (k3_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_3'))=k3_xboole_0('#skF_5', k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1236, c_1583])).
% 11.72/5.12  tff(c_38, plain, (![B_43, A_42]: (k3_xboole_0(B_43, k1_tarski(A_42))=k1_tarski(A_42) | ~r2_hidden(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_62])).
% 11.72/5.12  tff(c_443, plain, (![C_80]: (k3_xboole_0(k2_tarski('#skF_3', '#skF_4'), k3_xboole_0('#skF_5', C_80))=k3_xboole_0(k1_tarski('#skF_3'), C_80))), inference(superposition, [status(thm), theory('equality')], [c_44, c_247])).
% 11.72/5.12  tff(c_456, plain, (![A_42]: (k3_xboole_0(k2_tarski('#skF_3', '#skF_4'), k1_tarski(A_42))=k3_xboole_0(k1_tarski('#skF_3'), k1_tarski(A_42)) | ~r2_hidden(A_42, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_38, c_443])).
% 11.72/5.12  tff(c_20353, plain, (![A_378]: (k3_xboole_0(k2_tarski('#skF_4', '#skF_3'), k1_tarski(A_378))=k3_xboole_0(k1_tarski('#skF_3'), k1_tarski(A_378)) | ~r2_hidden(A_378, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_1360, c_456])).
% 11.72/5.12  tff(c_1230, plain, (![D_112, A_111]: (k2_xboole_0(k1_tarski(D_112), k1_tarski(A_111))=k2_tarski(A_111, D_112))), inference(superposition, [status(thm), theory('equality')], [c_1215, c_2])).
% 11.72/5.12  tff(c_70, plain, (![B_50, A_51]: (k2_xboole_0(B_50, A_51)=k2_xboole_0(A_51, B_50))), inference(cnfTransformation, [status(thm)], [f_27])).
% 11.72/5.12  tff(c_85, plain, (![A_51, B_50]: (k3_xboole_0(A_51, k2_xboole_0(B_50, A_51))=A_51)), inference(superposition, [status(thm), theory('equality')], [c_70, c_8])).
% 11.72/5.12  tff(c_4311, plain, (![B_231, A_232, A_233]: (k3_xboole_0(k2_xboole_0(B_231, A_232), k3_xboole_0(A_233, A_232))=k3_xboole_0(A_233, A_232))), inference(superposition, [status(thm), theory('equality')], [c_85, c_646])).
% 11.72/5.12  tff(c_1770, plain, (![A_134, B_135, C_136]: (k3_xboole_0(A_134, k3_xboole_0(k2_xboole_0(A_134, B_135), C_136))=k3_xboole_0(A_134, C_136))), inference(superposition, [status(thm), theory('equality')], [c_8, c_247])).
% 11.72/5.12  tff(c_1881, plain, (![B_2, A_1, C_136]: (k3_xboole_0(B_2, k3_xboole_0(k2_xboole_0(A_1, B_2), C_136))=k3_xboole_0(B_2, C_136))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1770])).
% 11.72/5.12  tff(c_4339, plain, (![A_1, B_231, A_232]: (k3_xboole_0(k2_xboole_0(A_1, k2_xboole_0(B_231, A_232)), A_232)=k3_xboole_0(k2_xboole_0(B_231, A_232), A_232))), inference(superposition, [status(thm), theory('equality')], [c_4311, c_1881])).
% 11.72/5.12  tff(c_4536, plain, (![A_1, B_231, A_232]: (k3_xboole_0(k2_xboole_0(A_1, k2_xboole_0(B_231, A_232)), A_232)=A_232)), inference(demodulation, [status(thm), theory('equality')], [c_85, c_4, c_4339])).
% 11.72/5.12  tff(c_4576, plain, (![A_234, B_235, A_236]: (k3_xboole_0(k2_xboole_0(A_234, k2_xboole_0(B_235, A_236)), A_236)=A_236)), inference(demodulation, [status(thm), theory('equality')], [c_85, c_4, c_4339])).
% 11.72/5.12  tff(c_848, plain, (![B_50, A_51, A_89]: (k3_xboole_0(k2_xboole_0(B_50, A_51), k3_xboole_0(A_89, A_51))=k3_xboole_0(A_89, A_51))), inference(superposition, [status(thm), theory('equality')], [c_85, c_646])).
% 11.72/5.12  tff(c_4582, plain, (![B_50, A_236, A_234, B_235]: (k3_xboole_0(k2_xboole_0(B_50, A_236), A_236)=k3_xboole_0(k2_xboole_0(A_234, k2_xboole_0(B_235, A_236)), A_236))), inference(superposition, [status(thm), theory('equality')], [c_4576, c_848])).
% 11.72/5.12  tff(c_4738, plain, (![B_237, A_238]: (k3_xboole_0(k2_xboole_0(B_237, A_238), A_238)=A_238)), inference(demodulation, [status(thm), theory('equality')], [c_4536, c_4582])).
% 11.72/5.12  tff(c_4833, plain, (![A_111, D_112]: (k3_xboole_0(k2_tarski(A_111, D_112), k1_tarski(A_111))=k1_tarski(A_111))), inference(superposition, [status(thm), theory('equality')], [c_1230, c_4738])).
% 11.72/5.12  tff(c_20405, plain, (k3_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))=k1_tarski('#skF_4') | ~r2_hidden('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_20353, c_4833])).
% 11.72/5.12  tff(c_20486, plain, (k3_xboole_0('#skF_5', k1_tarski('#skF_4'))=k1_tarski('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_1608, c_4, c_20405])).
% 11.72/5.12  tff(c_905, plain, (![B_91, A_92, C_93]: (k3_xboole_0(k3_xboole_0(B_91, A_92), C_93)=k3_xboole_0(A_92, k3_xboole_0(B_91, C_93)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_247])).
% 11.72/5.12  tff(c_1011, plain, (![C_93]: (k3_xboole_0('#skF_5', k3_xboole_0(k2_tarski('#skF_3', '#skF_4'), C_93))=k3_xboole_0(k1_tarski('#skF_3'), C_93))), inference(superposition, [status(thm), theory('equality')], [c_44, c_905])).
% 11.72/5.12  tff(c_6585, plain, (![C_261]: (k3_xboole_0('#skF_5', k3_xboole_0(k2_tarski('#skF_4', '#skF_3'), C_261))=k3_xboole_0(k1_tarski('#skF_3'), C_261))), inference(demodulation, [status(thm), theory('equality')], [c_1360, c_1011])).
% 11.72/5.12  tff(c_6649, plain, (k3_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))=k3_xboole_0('#skF_5', k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_4833, c_6585])).
% 11.72/5.12  tff(c_20498, plain, (k3_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))=k1_tarski('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_20486, c_6649])).
% 11.72/5.12  tff(c_36, plain, (![B_41, A_40]: (r2_hidden(B_41, A_40) | k3_xboole_0(A_40, k1_tarski(B_41))!=k1_tarski(B_41))), inference(cnfTransformation, [status(thm)], [f_58])).
% 11.72/5.12  tff(c_20728, plain, (r2_hidden('#skF_4', k1_tarski('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_20498, c_36])).
% 11.72/5.12  tff(c_10, plain, (![C_14, A_10]: (C_14=A_10 | ~r2_hidden(C_14, k1_tarski(A_10)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 11.72/5.12  tff(c_20733, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_20728, c_10])).
% 11.72/5.12  tff(c_20737, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_20733])).
% 11.72/5.12  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.72/5.12  
% 11.72/5.12  Inference rules
% 11.72/5.12  ----------------------
% 11.72/5.12  #Ref     : 0
% 11.72/5.12  #Sup     : 5122
% 11.72/5.12  #Fact    : 0
% 11.72/5.12  #Define  : 0
% 11.72/5.12  #Split   : 0
% 11.72/5.12  #Chain   : 0
% 11.72/5.12  #Close   : 0
% 11.72/5.12  
% 11.72/5.12  Ordering : KBO
% 11.72/5.12  
% 11.72/5.12  Simplification rules
% 11.72/5.12  ----------------------
% 11.72/5.12  #Subsume      : 380
% 11.72/5.12  #Demod        : 3958
% 11.72/5.12  #Tautology    : 1914
% 11.72/5.12  #SimpNegUnit  : 1
% 11.72/5.12  #BackRed      : 7
% 11.72/5.12  
% 11.72/5.12  #Partial instantiations: 0
% 11.72/5.12  #Strategies tried      : 1
% 11.72/5.12  
% 11.72/5.12  Timing (in seconds)
% 11.72/5.12  ----------------------
% 11.87/5.12  Preprocessing        : 0.30
% 11.87/5.12  Parsing              : 0.16
% 11.87/5.12  CNF conversion       : 0.02
% 11.87/5.12  Main loop            : 4.04
% 11.87/5.12  Inferencing          : 0.72
% 11.87/5.12  Reduction            : 2.58
% 11.87/5.12  Demodulation         : 2.39
% 11.87/5.12  BG Simplification    : 0.11
% 11.87/5.12  Subsumption          : 0.49
% 11.87/5.12  Abstraction          : 0.16
% 11.87/5.12  MUC search           : 0.00
% 11.87/5.12  Cooper               : 0.00
% 11.87/5.12  Total                : 4.37
% 11.87/5.12  Index Insertion      : 0.00
% 11.87/5.12  Index Deletion       : 0.00
% 11.87/5.12  Index Matching       : 0.00
% 11.87/5.12  BG Taut test         : 0.00
%------------------------------------------------------------------------------
