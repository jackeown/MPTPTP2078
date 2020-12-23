%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:02 EST 2020

% Result     : Theorem 5.95s
% Output     : CNFRefutation 6.17s
% Verified   : 
% Statistics : Number of formulae       :   62 (  83 expanded)
%              Number of leaves         :   30 (  42 expanded)
%              Depth                    :   17
%              Number of atoms          :   56 (  84 expanded)
%              Number of equality atoms :   48 (  75 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(f_69,negated_conjecture,(
    ~ ! [A,B] :
        ( k2_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
       => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_zfmisc_1)).

tff(f_54,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_52,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_56,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_58,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_60,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_62,axiom,(
    ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

tff(f_64,axiom,(
    ! [A,B,C,D,E,F,G] : k6_enumset1(A,A,B,C,D,E,F,G) = k5_enumset1(A,B,C,D,E,F,G) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

tff(f_50,axiom,(
    ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k5_enumset1(A,B,C,D,E,F,G),k1_tarski(H)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_enumset1)).

tff(f_48,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(c_50,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_38,plain,(
    ! [A_26,B_27] : k1_enumset1(A_26,A_26,B_27) = k2_tarski(A_26,B_27) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_36,plain,(
    ! [A_25] : k2_tarski(A_25,A_25) = k1_tarski(A_25) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_40,plain,(
    ! [A_28,B_29,C_30] : k2_enumset1(A_28,A_28,B_29,C_30) = k1_enumset1(A_28,B_29,C_30) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_42,plain,(
    ! [A_31,B_32,C_33,D_34] : k3_enumset1(A_31,A_31,B_32,C_33,D_34) = k2_enumset1(A_31,B_32,C_33,D_34) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_44,plain,(
    ! [A_35,B_36,C_37,D_38,E_39] : k4_enumset1(A_35,A_35,B_36,C_37,D_38,E_39) = k3_enumset1(A_35,B_36,C_37,D_38,E_39) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_46,plain,(
    ! [E_44,C_42,F_45,A_40,D_43,B_41] : k5_enumset1(A_40,A_40,B_41,C_42,D_43,E_44,F_45) = k4_enumset1(A_40,B_41,C_42,D_43,E_44,F_45) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_48,plain,(
    ! [A_46,E_50,B_47,C_48,D_49,G_52,F_51] : k6_enumset1(A_46,A_46,B_47,C_48,D_49,E_50,F_51,G_52) = k5_enumset1(A_46,B_47,C_48,D_49,E_50,F_51,G_52) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_3786,plain,(
    ! [H_214,B_209,F_210,E_212,G_213,D_211,C_207,A_208] : k2_xboole_0(k5_enumset1(A_208,B_209,C_207,D_211,E_212,F_210,G_213),k1_tarski(H_214)) = k6_enumset1(A_208,B_209,C_207,D_211,E_212,F_210,G_213,H_214) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_3819,plain,(
    ! [E_44,C_42,H_214,F_45,A_40,D_43,B_41] : k6_enumset1(A_40,A_40,B_41,C_42,D_43,E_44,F_45,H_214) = k2_xboole_0(k4_enumset1(A_40,B_41,C_42,D_43,E_44,F_45),k1_tarski(H_214)) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_3786])).

tff(c_3825,plain,(
    ! [D_217,B_221,A_216,F_219,C_220,H_218,E_215] : k2_xboole_0(k4_enumset1(A_216,B_221,C_220,D_217,E_215,F_219),k1_tarski(H_218)) = k5_enumset1(A_216,B_221,C_220,D_217,E_215,F_219,H_218) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_3819])).

tff(c_3858,plain,(
    ! [A_35,B_36,C_37,D_38,E_39,H_218] : k5_enumset1(A_35,A_35,B_36,C_37,D_38,E_39,H_218) = k2_xboole_0(k3_enumset1(A_35,B_36,C_37,D_38,E_39),k1_tarski(H_218)) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_3825])).

tff(c_3864,plain,(
    ! [D_226,H_223,B_227,C_224,A_222,E_225] : k2_xboole_0(k3_enumset1(A_222,B_227,C_224,D_226,E_225),k1_tarski(H_223)) = k4_enumset1(A_222,B_227,C_224,D_226,E_225,H_223) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_3858])).

tff(c_3897,plain,(
    ! [A_31,C_33,H_223,B_32,D_34] : k4_enumset1(A_31,A_31,B_32,C_33,D_34,H_223) = k2_xboole_0(k2_enumset1(A_31,B_32,C_33,D_34),k1_tarski(H_223)) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_3864])).

tff(c_3903,plain,(
    ! [D_228,A_230,H_231,C_232,B_229] : k2_xboole_0(k2_enumset1(A_230,B_229,C_232,D_228),k1_tarski(H_231)) = k3_enumset1(A_230,B_229,C_232,D_228,H_231) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_3897])).

tff(c_3936,plain,(
    ! [A_28,B_29,C_30,H_231] : k3_enumset1(A_28,A_28,B_29,C_30,H_231) = k2_xboole_0(k1_enumset1(A_28,B_29,C_30),k1_tarski(H_231)) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_3903])).

tff(c_3995,plain,(
    ! [A_233,B_234,C_235,H_236] : k2_xboole_0(k1_enumset1(A_233,B_234,C_235),k1_tarski(H_236)) = k2_enumset1(A_233,B_234,C_235,H_236) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_3936])).

tff(c_4028,plain,(
    ! [A_26,B_27,H_236] : k2_xboole_0(k2_tarski(A_26,B_27),k1_tarski(H_236)) = k2_enumset1(A_26,A_26,B_27,H_236) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_3995])).

tff(c_4034,plain,(
    ! [A_237,B_238,H_239] : k2_xboole_0(k2_tarski(A_237,B_238),k1_tarski(H_239)) = k1_enumset1(A_237,B_238,H_239) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_4028])).

tff(c_4067,plain,(
    ! [A_25,H_239] : k2_xboole_0(k1_tarski(A_25),k1_tarski(H_239)) = k1_enumset1(A_25,A_25,H_239) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_4034])).

tff(c_4073,plain,(
    ! [A_240,H_241] : k2_xboole_0(k1_tarski(A_240),k1_tarski(H_241)) = k2_tarski(A_240,H_241) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_4067])).

tff(c_52,plain,(
    k2_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) = k1_tarski('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_4103,plain,(
    k2_tarski('#skF_3','#skF_4') = k1_tarski('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_4073,c_52])).

tff(c_69,plain,(
    ! [A_63,B_64] : k1_enumset1(A_63,A_63,B_64) = k2_tarski(A_63,B_64) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_12,plain,(
    ! [E_16,A_10,B_11] : r2_hidden(E_16,k1_enumset1(A_10,B_11,E_16)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_75,plain,(
    ! [B_64,A_63] : r2_hidden(B_64,k2_tarski(A_63,B_64)) ),
    inference(superposition,[status(thm),theory(equality)],[c_69,c_12])).

tff(c_4126,plain,(
    r2_hidden('#skF_4',k1_tarski('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_4103,c_75])).

tff(c_241,plain,(
    ! [E_88,C_89,B_90,A_91] :
      ( E_88 = C_89
      | E_88 = B_90
      | E_88 = A_91
      | ~ r2_hidden(E_88,k1_enumset1(A_91,B_90,C_89)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_260,plain,(
    ! [E_92,B_93,A_94] :
      ( E_92 = B_93
      | E_92 = A_94
      | E_92 = A_94
      | ~ r2_hidden(E_92,k2_tarski(A_94,B_93)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_241])).

tff(c_269,plain,(
    ! [E_92,A_25] :
      ( E_92 = A_25
      | E_92 = A_25
      | E_92 = A_25
      | ~ r2_hidden(E_92,k1_tarski(A_25)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_260])).

tff(c_4134,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_4126,c_269])).

tff(c_4138,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_50,c_50,c_4134])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:10:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.95/2.29  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.95/2.29  
% 5.95/2.29  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.17/2.30  %$ r2_hidden > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 6.17/2.30  
% 6.17/2.30  %Foreground sorts:
% 6.17/2.30  
% 6.17/2.30  
% 6.17/2.30  %Background operators:
% 6.17/2.30  
% 6.17/2.30  
% 6.17/2.30  %Foreground operators:
% 6.17/2.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.17/2.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.17/2.30  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.17/2.30  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.17/2.30  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 6.17/2.30  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 6.17/2.30  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.17/2.30  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.17/2.30  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 6.17/2.30  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.17/2.30  tff('#skF_3', type, '#skF_3': $i).
% 6.17/2.30  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 6.17/2.30  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 6.17/2.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.17/2.30  tff('#skF_4', type, '#skF_4': $i).
% 6.17/2.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.17/2.30  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.17/2.30  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.17/2.30  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 6.17/2.30  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 6.17/2.30  
% 6.17/2.31  tff(f_69, negated_conjecture, ~(![A, B]: ((k2_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_zfmisc_1)).
% 6.17/2.31  tff(f_54, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 6.17/2.31  tff(f_52, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 6.17/2.31  tff(f_56, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 6.17/2.31  tff(f_58, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 6.17/2.31  tff(f_60, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 6.17/2.31  tff(f_62, axiom, (![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 6.17/2.31  tff(f_64, axiom, (![A, B, C, D, E, F, G]: (k6_enumset1(A, A, B, C, D, E, F, G) = k5_enumset1(A, B, C, D, E, F, G))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_enumset1)).
% 6.17/2.31  tff(f_50, axiom, (![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k5_enumset1(A, B, C, D, E, F, G), k1_tarski(H)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t68_enumset1)).
% 6.17/2.31  tff(f_48, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 6.17/2.31  tff(c_50, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_69])).
% 6.17/2.31  tff(c_38, plain, (![A_26, B_27]: (k1_enumset1(A_26, A_26, B_27)=k2_tarski(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_54])).
% 6.17/2.31  tff(c_36, plain, (![A_25]: (k2_tarski(A_25, A_25)=k1_tarski(A_25))), inference(cnfTransformation, [status(thm)], [f_52])).
% 6.17/2.31  tff(c_40, plain, (![A_28, B_29, C_30]: (k2_enumset1(A_28, A_28, B_29, C_30)=k1_enumset1(A_28, B_29, C_30))), inference(cnfTransformation, [status(thm)], [f_56])).
% 6.17/2.31  tff(c_42, plain, (![A_31, B_32, C_33, D_34]: (k3_enumset1(A_31, A_31, B_32, C_33, D_34)=k2_enumset1(A_31, B_32, C_33, D_34))), inference(cnfTransformation, [status(thm)], [f_58])).
% 6.17/2.31  tff(c_44, plain, (![A_35, B_36, C_37, D_38, E_39]: (k4_enumset1(A_35, A_35, B_36, C_37, D_38, E_39)=k3_enumset1(A_35, B_36, C_37, D_38, E_39))), inference(cnfTransformation, [status(thm)], [f_60])).
% 6.17/2.31  tff(c_46, plain, (![E_44, C_42, F_45, A_40, D_43, B_41]: (k5_enumset1(A_40, A_40, B_41, C_42, D_43, E_44, F_45)=k4_enumset1(A_40, B_41, C_42, D_43, E_44, F_45))), inference(cnfTransformation, [status(thm)], [f_62])).
% 6.17/2.31  tff(c_48, plain, (![A_46, E_50, B_47, C_48, D_49, G_52, F_51]: (k6_enumset1(A_46, A_46, B_47, C_48, D_49, E_50, F_51, G_52)=k5_enumset1(A_46, B_47, C_48, D_49, E_50, F_51, G_52))), inference(cnfTransformation, [status(thm)], [f_64])).
% 6.17/2.31  tff(c_3786, plain, (![H_214, B_209, F_210, E_212, G_213, D_211, C_207, A_208]: (k2_xboole_0(k5_enumset1(A_208, B_209, C_207, D_211, E_212, F_210, G_213), k1_tarski(H_214))=k6_enumset1(A_208, B_209, C_207, D_211, E_212, F_210, G_213, H_214))), inference(cnfTransformation, [status(thm)], [f_50])).
% 6.17/2.31  tff(c_3819, plain, (![E_44, C_42, H_214, F_45, A_40, D_43, B_41]: (k6_enumset1(A_40, A_40, B_41, C_42, D_43, E_44, F_45, H_214)=k2_xboole_0(k4_enumset1(A_40, B_41, C_42, D_43, E_44, F_45), k1_tarski(H_214)))), inference(superposition, [status(thm), theory('equality')], [c_46, c_3786])).
% 6.17/2.31  tff(c_3825, plain, (![D_217, B_221, A_216, F_219, C_220, H_218, E_215]: (k2_xboole_0(k4_enumset1(A_216, B_221, C_220, D_217, E_215, F_219), k1_tarski(H_218))=k5_enumset1(A_216, B_221, C_220, D_217, E_215, F_219, H_218))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_3819])).
% 6.17/2.31  tff(c_3858, plain, (![A_35, B_36, C_37, D_38, E_39, H_218]: (k5_enumset1(A_35, A_35, B_36, C_37, D_38, E_39, H_218)=k2_xboole_0(k3_enumset1(A_35, B_36, C_37, D_38, E_39), k1_tarski(H_218)))), inference(superposition, [status(thm), theory('equality')], [c_44, c_3825])).
% 6.17/2.31  tff(c_3864, plain, (![D_226, H_223, B_227, C_224, A_222, E_225]: (k2_xboole_0(k3_enumset1(A_222, B_227, C_224, D_226, E_225), k1_tarski(H_223))=k4_enumset1(A_222, B_227, C_224, D_226, E_225, H_223))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_3858])).
% 6.17/2.31  tff(c_3897, plain, (![A_31, C_33, H_223, B_32, D_34]: (k4_enumset1(A_31, A_31, B_32, C_33, D_34, H_223)=k2_xboole_0(k2_enumset1(A_31, B_32, C_33, D_34), k1_tarski(H_223)))), inference(superposition, [status(thm), theory('equality')], [c_42, c_3864])).
% 6.17/2.31  tff(c_3903, plain, (![D_228, A_230, H_231, C_232, B_229]: (k2_xboole_0(k2_enumset1(A_230, B_229, C_232, D_228), k1_tarski(H_231))=k3_enumset1(A_230, B_229, C_232, D_228, H_231))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_3897])).
% 6.17/2.31  tff(c_3936, plain, (![A_28, B_29, C_30, H_231]: (k3_enumset1(A_28, A_28, B_29, C_30, H_231)=k2_xboole_0(k1_enumset1(A_28, B_29, C_30), k1_tarski(H_231)))), inference(superposition, [status(thm), theory('equality')], [c_40, c_3903])).
% 6.17/2.31  tff(c_3995, plain, (![A_233, B_234, C_235, H_236]: (k2_xboole_0(k1_enumset1(A_233, B_234, C_235), k1_tarski(H_236))=k2_enumset1(A_233, B_234, C_235, H_236))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_3936])).
% 6.17/2.31  tff(c_4028, plain, (![A_26, B_27, H_236]: (k2_xboole_0(k2_tarski(A_26, B_27), k1_tarski(H_236))=k2_enumset1(A_26, A_26, B_27, H_236))), inference(superposition, [status(thm), theory('equality')], [c_38, c_3995])).
% 6.17/2.31  tff(c_4034, plain, (![A_237, B_238, H_239]: (k2_xboole_0(k2_tarski(A_237, B_238), k1_tarski(H_239))=k1_enumset1(A_237, B_238, H_239))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_4028])).
% 6.17/2.31  tff(c_4067, plain, (![A_25, H_239]: (k2_xboole_0(k1_tarski(A_25), k1_tarski(H_239))=k1_enumset1(A_25, A_25, H_239))), inference(superposition, [status(thm), theory('equality')], [c_36, c_4034])).
% 6.17/2.31  tff(c_4073, plain, (![A_240, H_241]: (k2_xboole_0(k1_tarski(A_240), k1_tarski(H_241))=k2_tarski(A_240, H_241))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_4067])).
% 6.17/2.31  tff(c_52, plain, (k2_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))=k1_tarski('#skF_3')), inference(cnfTransformation, [status(thm)], [f_69])).
% 6.17/2.31  tff(c_4103, plain, (k2_tarski('#skF_3', '#skF_4')=k1_tarski('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_4073, c_52])).
% 6.17/2.31  tff(c_69, plain, (![A_63, B_64]: (k1_enumset1(A_63, A_63, B_64)=k2_tarski(A_63, B_64))), inference(cnfTransformation, [status(thm)], [f_54])).
% 6.17/2.31  tff(c_12, plain, (![E_16, A_10, B_11]: (r2_hidden(E_16, k1_enumset1(A_10, B_11, E_16)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 6.17/2.31  tff(c_75, plain, (![B_64, A_63]: (r2_hidden(B_64, k2_tarski(A_63, B_64)))), inference(superposition, [status(thm), theory('equality')], [c_69, c_12])).
% 6.17/2.31  tff(c_4126, plain, (r2_hidden('#skF_4', k1_tarski('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_4103, c_75])).
% 6.17/2.31  tff(c_241, plain, (![E_88, C_89, B_90, A_91]: (E_88=C_89 | E_88=B_90 | E_88=A_91 | ~r2_hidden(E_88, k1_enumset1(A_91, B_90, C_89)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 6.17/2.31  tff(c_260, plain, (![E_92, B_93, A_94]: (E_92=B_93 | E_92=A_94 | E_92=A_94 | ~r2_hidden(E_92, k2_tarski(A_94, B_93)))), inference(superposition, [status(thm), theory('equality')], [c_38, c_241])).
% 6.17/2.31  tff(c_269, plain, (![E_92, A_25]: (E_92=A_25 | E_92=A_25 | E_92=A_25 | ~r2_hidden(E_92, k1_tarski(A_25)))), inference(superposition, [status(thm), theory('equality')], [c_36, c_260])).
% 6.17/2.31  tff(c_4134, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_4126, c_269])).
% 6.17/2.31  tff(c_4138, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_50, c_50, c_4134])).
% 6.17/2.31  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.17/2.31  
% 6.17/2.31  Inference rules
% 6.17/2.31  ----------------------
% 6.17/2.31  #Ref     : 0
% 6.17/2.31  #Sup     : 1032
% 6.17/2.31  #Fact    : 0
% 6.17/2.31  #Define  : 0
% 6.17/2.31  #Split   : 0
% 6.17/2.31  #Chain   : 0
% 6.17/2.31  #Close   : 0
% 6.17/2.31  
% 6.17/2.31  Ordering : KBO
% 6.17/2.31  
% 6.17/2.31  Simplification rules
% 6.17/2.31  ----------------------
% 6.17/2.31  #Subsume      : 0
% 6.17/2.31  #Demod        : 1342
% 6.17/2.31  #Tautology    : 317
% 6.17/2.31  #SimpNegUnit  : 1
% 6.17/2.31  #BackRed      : 0
% 6.17/2.31  
% 6.17/2.31  #Partial instantiations: 0
% 6.17/2.31  #Strategies tried      : 1
% 6.17/2.31  
% 6.17/2.31  Timing (in seconds)
% 6.17/2.31  ----------------------
% 6.17/2.31  Preprocessing        : 0.33
% 6.17/2.31  Parsing              : 0.17
% 6.17/2.31  CNF conversion       : 0.02
% 6.17/2.31  Main loop            : 1.17
% 6.17/2.31  Inferencing          : 0.35
% 6.17/2.31  Reduction            : 0.58
% 6.17/2.31  Demodulation         : 0.50
% 6.17/2.31  BG Simplification    : 0.06
% 6.17/2.31  Subsumption          : 0.13
% 6.17/2.31  Abstraction          : 0.10
% 6.17/2.31  MUC search           : 0.00
% 6.17/2.31  Cooper               : 0.00
% 6.17/2.31  Total                : 1.53
% 6.17/2.32  Index Insertion      : 0.00
% 6.17/2.32  Index Deletion       : 0.00
% 6.17/2.32  Index Matching       : 0.00
% 6.17/2.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
