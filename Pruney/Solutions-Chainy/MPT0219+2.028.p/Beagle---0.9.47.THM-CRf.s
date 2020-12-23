%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:53 EST 2020

% Result     : Theorem 16.46s
% Output     : CNFRefutation 16.56s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 116 expanded)
%              Number of leaves         :   36 (  55 expanded)
%              Depth                    :   13
%              Number of atoms          :   73 ( 119 expanded)
%              Number of equality atoms :   53 (  98 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_82,negated_conjecture,(
    ~ ! [A,B] :
        ( k2_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
       => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_zfmisc_1)).

tff(f_40,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_46,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_48,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_44,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_38,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_42,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_65,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_67,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_63,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(c_62,plain,(
    '#skF_5' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_14,plain,(
    ! [A_12] : k5_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_20,plain,(
    ! [A_18] : k5_xboole_0(A_18,A_18) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_64,plain,(
    k2_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_5')) = k1_tarski('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_22,plain,(
    ! [A_19,B_20] : k5_xboole_0(A_19,k4_xboole_0(B_20,A_19)) = k2_xboole_0(A_19,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_102,plain,(
    ! [B_64,A_65] : k5_xboole_0(B_64,A_65) = k5_xboole_0(A_65,B_64) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_118,plain,(
    ! [A_65] : k5_xboole_0(k1_xboole_0,A_65) = A_65 ),
    inference(superposition,[status(thm),theory(equality)],[c_102,c_14])).

tff(c_482,plain,(
    ! [A_106,B_107,C_108] : k5_xboole_0(k5_xboole_0(A_106,B_107),C_108) = k5_xboole_0(A_106,k5_xboole_0(B_107,C_108)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_568,plain,(
    ! [A_18,C_108] : k5_xboole_0(A_18,k5_xboole_0(A_18,C_108)) = k5_xboole_0(k1_xboole_0,C_108) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_482])).

tff(c_582,plain,(
    ! [A_109,C_110] : k5_xboole_0(A_109,k5_xboole_0(A_109,C_110)) = C_110 ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_568])).

tff(c_1212,plain,(
    ! [A_153,B_154] : k5_xboole_0(A_153,k2_xboole_0(A_153,B_154)) = k4_xboole_0(B_154,A_153) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_582])).

tff(c_1248,plain,(
    k5_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_4')) = k4_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_1212])).

tff(c_1257,plain,(
    k4_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_4')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_1248])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_310,plain,(
    ! [A_90,B_91] : k5_xboole_0(A_90,k3_xboole_0(A_90,B_91)) = k4_xboole_0(A_90,B_91) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_326,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,k3_xboole_0(A_1,B_2)) = k4_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_310])).

tff(c_615,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,k4_xboole_0(B_2,A_1)) = k3_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_326,c_582])).

tff(c_1271,plain,(
    k3_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_5')) = k5_xboole_0(k1_tarski('#skF_5'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1257,c_615])).

tff(c_1280,plain,(
    k3_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_5')) = k1_tarski('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_1271])).

tff(c_12,plain,(
    ! [A_10,B_11] : k5_xboole_0(A_10,k3_xboole_0(A_10,B_11)) = k4_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_4,plain,(
    ! [B_4,A_3] : k5_xboole_0(B_4,A_3) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_653,plain,(
    ! [A_111,B_112] : k5_xboole_0(A_111,k5_xboole_0(B_112,A_111)) = B_112 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_582])).

tff(c_2165,plain,(
    ! [A_195,B_196] : k5_xboole_0(k3_xboole_0(A_195,B_196),k4_xboole_0(A_195,B_196)) = A_195 ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_653])).

tff(c_2195,plain,(
    k5_xboole_0(k1_tarski('#skF_5'),k4_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_5'))) = k1_tarski('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1280,c_2165])).

tff(c_2399,plain,(
    k2_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_4')) = k1_tarski('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2195,c_22])).

tff(c_16,plain,(
    ! [A_13,B_14] : r1_tarski(A_13,k2_xboole_0(A_13,B_14)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_48,plain,(
    ! [A_28] : k2_tarski(A_28,A_28) = k1_tarski(A_28) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_241,plain,(
    ! [A_75,B_76] : k1_enumset1(A_75,A_75,B_76) = k2_tarski(A_75,B_76) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_26,plain,(
    ! [E_27,A_21,B_22] : r2_hidden(E_27,k1_enumset1(A_21,B_22,E_27)) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_259,plain,(
    ! [B_77,A_78] : r2_hidden(B_77,k2_tarski(A_78,B_77)) ),
    inference(superposition,[status(thm),theory(equality)],[c_241,c_26])).

tff(c_262,plain,(
    ! [A_28] : r2_hidden(A_28,k1_tarski(A_28)) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_259])).

tff(c_353,plain,(
    ! [C_93,B_94,A_95] :
      ( r2_hidden(C_93,B_94)
      | ~ r2_hidden(C_93,A_95)
      | ~ r1_tarski(A_95,B_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_385,plain,(
    ! [A_96,B_97] :
      ( r2_hidden(A_96,B_97)
      | ~ r1_tarski(k1_tarski(A_96),B_97) ) ),
    inference(resolution,[status(thm)],[c_262,c_353])).

tff(c_396,plain,(
    ! [A_96,B_14] : r2_hidden(A_96,k2_xboole_0(k1_tarski(A_96),B_14)) ),
    inference(resolution,[status(thm)],[c_16,c_385])).

tff(c_2420,plain,(
    r2_hidden('#skF_5',k1_tarski('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2399,c_396])).

tff(c_50,plain,(
    ! [A_29,B_30] : k1_enumset1(A_29,A_29,B_30) = k2_tarski(A_29,B_30) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_973,plain,(
    ! [E_121,C_122,B_123,A_124] :
      ( E_121 = C_122
      | E_121 = B_123
      | E_121 = A_124
      | ~ r2_hidden(E_121,k1_enumset1(A_124,B_123,C_122)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_11985,plain,(
    ! [E_22564,B_22565,A_22566] :
      ( E_22564 = B_22565
      | E_22564 = A_22566
      | E_22564 = A_22566
      | ~ r2_hidden(E_22564,k2_tarski(A_22566,B_22565)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_973])).

tff(c_43110,plain,(
    ! [E_99788,A_99789] :
      ( E_99788 = A_99789
      | E_99788 = A_99789
      | E_99788 = A_99789
      | ~ r2_hidden(E_99788,k1_tarski(A_99789)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_11985])).

tff(c_43130,plain,(
    '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_2420,c_43110])).

tff(c_43143,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_62,c_62,c_43130])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 12:41:25 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 16.46/8.36  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 16.46/8.37  
% 16.46/8.37  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 16.46/8.37  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 16.46/8.37  
% 16.46/8.37  %Foreground sorts:
% 16.46/8.37  
% 16.46/8.37  
% 16.46/8.37  %Background operators:
% 16.46/8.37  
% 16.46/8.37  
% 16.46/8.37  %Foreground operators:
% 16.46/8.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 16.46/8.37  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 16.46/8.37  tff(k1_tarski, type, k1_tarski: $i > $i).
% 16.46/8.37  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 16.46/8.37  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 16.46/8.37  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 16.46/8.37  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 16.46/8.37  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 16.46/8.37  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 16.46/8.37  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 16.46/8.37  tff('#skF_5', type, '#skF_5': $i).
% 16.46/8.37  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 16.46/8.37  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 16.46/8.37  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 16.46/8.37  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 16.46/8.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 16.46/8.37  tff('#skF_4', type, '#skF_4': $i).
% 16.46/8.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 16.46/8.37  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 16.46/8.37  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 16.46/8.37  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 16.46/8.37  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 16.46/8.37  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 16.46/8.37  
% 16.56/8.38  tff(f_82, negated_conjecture, ~(![A, B]: ((k2_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_zfmisc_1)).
% 16.56/8.38  tff(f_40, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 16.56/8.38  tff(f_46, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 16.56/8.38  tff(f_48, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 16.56/8.38  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 16.56/8.38  tff(f_44, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 16.56/8.38  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 16.56/8.38  tff(f_38, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 16.56/8.38  tff(f_42, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 16.56/8.38  tff(f_65, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 16.56/8.38  tff(f_67, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 16.56/8.38  tff(f_63, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 16.56/8.38  tff(f_36, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 16.56/8.38  tff(c_62, plain, ('#skF_5'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_82])).
% 16.56/8.38  tff(c_14, plain, (![A_12]: (k5_xboole_0(A_12, k1_xboole_0)=A_12)), inference(cnfTransformation, [status(thm)], [f_40])).
% 16.56/8.38  tff(c_20, plain, (![A_18]: (k5_xboole_0(A_18, A_18)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_46])).
% 16.56/8.38  tff(c_64, plain, (k2_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_5'))=k1_tarski('#skF_4')), inference(cnfTransformation, [status(thm)], [f_82])).
% 16.56/8.38  tff(c_22, plain, (![A_19, B_20]: (k5_xboole_0(A_19, k4_xboole_0(B_20, A_19))=k2_xboole_0(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_48])).
% 16.56/8.38  tff(c_102, plain, (![B_64, A_65]: (k5_xboole_0(B_64, A_65)=k5_xboole_0(A_65, B_64))), inference(cnfTransformation, [status(thm)], [f_29])).
% 16.56/8.38  tff(c_118, plain, (![A_65]: (k5_xboole_0(k1_xboole_0, A_65)=A_65)), inference(superposition, [status(thm), theory('equality')], [c_102, c_14])).
% 16.56/8.38  tff(c_482, plain, (![A_106, B_107, C_108]: (k5_xboole_0(k5_xboole_0(A_106, B_107), C_108)=k5_xboole_0(A_106, k5_xboole_0(B_107, C_108)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 16.56/8.38  tff(c_568, plain, (![A_18, C_108]: (k5_xboole_0(A_18, k5_xboole_0(A_18, C_108))=k5_xboole_0(k1_xboole_0, C_108))), inference(superposition, [status(thm), theory('equality')], [c_20, c_482])).
% 16.56/8.38  tff(c_582, plain, (![A_109, C_110]: (k5_xboole_0(A_109, k5_xboole_0(A_109, C_110))=C_110)), inference(demodulation, [status(thm), theory('equality')], [c_118, c_568])).
% 16.56/8.38  tff(c_1212, plain, (![A_153, B_154]: (k5_xboole_0(A_153, k2_xboole_0(A_153, B_154))=k4_xboole_0(B_154, A_153))), inference(superposition, [status(thm), theory('equality')], [c_22, c_582])).
% 16.56/8.38  tff(c_1248, plain, (k5_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_4'))=k4_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_64, c_1212])).
% 16.56/8.38  tff(c_1257, plain, (k4_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_4'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_20, c_1248])).
% 16.56/8.38  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 16.56/8.38  tff(c_310, plain, (![A_90, B_91]: (k5_xboole_0(A_90, k3_xboole_0(A_90, B_91))=k4_xboole_0(A_90, B_91))), inference(cnfTransformation, [status(thm)], [f_38])).
% 16.56/8.38  tff(c_326, plain, (![B_2, A_1]: (k5_xboole_0(B_2, k3_xboole_0(A_1, B_2))=k4_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_310])).
% 16.56/8.38  tff(c_615, plain, (![B_2, A_1]: (k5_xboole_0(B_2, k4_xboole_0(B_2, A_1))=k3_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_326, c_582])).
% 16.56/8.38  tff(c_1271, plain, (k3_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_5'))=k5_xboole_0(k1_tarski('#skF_5'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1257, c_615])).
% 16.56/8.38  tff(c_1280, plain, (k3_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_5'))=k1_tarski('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_1271])).
% 16.56/8.38  tff(c_12, plain, (![A_10, B_11]: (k5_xboole_0(A_10, k3_xboole_0(A_10, B_11))=k4_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_38])).
% 16.56/8.38  tff(c_4, plain, (![B_4, A_3]: (k5_xboole_0(B_4, A_3)=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 16.56/8.38  tff(c_653, plain, (![A_111, B_112]: (k5_xboole_0(A_111, k5_xboole_0(B_112, A_111))=B_112)), inference(superposition, [status(thm), theory('equality')], [c_4, c_582])).
% 16.56/8.38  tff(c_2165, plain, (![A_195, B_196]: (k5_xboole_0(k3_xboole_0(A_195, B_196), k4_xboole_0(A_195, B_196))=A_195)), inference(superposition, [status(thm), theory('equality')], [c_12, c_653])).
% 16.56/8.38  tff(c_2195, plain, (k5_xboole_0(k1_tarski('#skF_5'), k4_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_5')))=k1_tarski('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1280, c_2165])).
% 16.56/8.38  tff(c_2399, plain, (k2_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_4'))=k1_tarski('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2195, c_22])).
% 16.56/8.38  tff(c_16, plain, (![A_13, B_14]: (r1_tarski(A_13, k2_xboole_0(A_13, B_14)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 16.56/8.38  tff(c_48, plain, (![A_28]: (k2_tarski(A_28, A_28)=k1_tarski(A_28))), inference(cnfTransformation, [status(thm)], [f_65])).
% 16.56/8.38  tff(c_241, plain, (![A_75, B_76]: (k1_enumset1(A_75, A_75, B_76)=k2_tarski(A_75, B_76))), inference(cnfTransformation, [status(thm)], [f_67])).
% 16.56/8.38  tff(c_26, plain, (![E_27, A_21, B_22]: (r2_hidden(E_27, k1_enumset1(A_21, B_22, E_27)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 16.56/8.38  tff(c_259, plain, (![B_77, A_78]: (r2_hidden(B_77, k2_tarski(A_78, B_77)))), inference(superposition, [status(thm), theory('equality')], [c_241, c_26])).
% 16.56/8.38  tff(c_262, plain, (![A_28]: (r2_hidden(A_28, k1_tarski(A_28)))), inference(superposition, [status(thm), theory('equality')], [c_48, c_259])).
% 16.56/8.38  tff(c_353, plain, (![C_93, B_94, A_95]: (r2_hidden(C_93, B_94) | ~r2_hidden(C_93, A_95) | ~r1_tarski(A_95, B_94))), inference(cnfTransformation, [status(thm)], [f_36])).
% 16.56/8.38  tff(c_385, plain, (![A_96, B_97]: (r2_hidden(A_96, B_97) | ~r1_tarski(k1_tarski(A_96), B_97))), inference(resolution, [status(thm)], [c_262, c_353])).
% 16.56/8.38  tff(c_396, plain, (![A_96, B_14]: (r2_hidden(A_96, k2_xboole_0(k1_tarski(A_96), B_14)))), inference(resolution, [status(thm)], [c_16, c_385])).
% 16.56/8.38  tff(c_2420, plain, (r2_hidden('#skF_5', k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_2399, c_396])).
% 16.56/8.38  tff(c_50, plain, (![A_29, B_30]: (k1_enumset1(A_29, A_29, B_30)=k2_tarski(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_67])).
% 16.56/8.38  tff(c_973, plain, (![E_121, C_122, B_123, A_124]: (E_121=C_122 | E_121=B_123 | E_121=A_124 | ~r2_hidden(E_121, k1_enumset1(A_124, B_123, C_122)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 16.56/8.38  tff(c_11985, plain, (![E_22564, B_22565, A_22566]: (E_22564=B_22565 | E_22564=A_22566 | E_22564=A_22566 | ~r2_hidden(E_22564, k2_tarski(A_22566, B_22565)))), inference(superposition, [status(thm), theory('equality')], [c_50, c_973])).
% 16.56/8.38  tff(c_43110, plain, (![E_99788, A_99789]: (E_99788=A_99789 | E_99788=A_99789 | E_99788=A_99789 | ~r2_hidden(E_99788, k1_tarski(A_99789)))), inference(superposition, [status(thm), theory('equality')], [c_48, c_11985])).
% 16.56/8.38  tff(c_43130, plain, ('#skF_5'='#skF_4'), inference(resolution, [status(thm)], [c_2420, c_43110])).
% 16.56/8.38  tff(c_43143, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_62, c_62, c_43130])).
% 16.56/8.38  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 16.56/8.38  
% 16.56/8.38  Inference rules
% 16.56/8.38  ----------------------
% 16.56/8.38  #Ref     : 0
% 16.56/8.38  #Sup     : 7483
% 16.56/8.38  #Fact    : 54
% 16.56/8.38  #Define  : 0
% 16.56/8.38  #Split   : 0
% 16.56/8.38  #Chain   : 0
% 16.56/8.38  #Close   : 0
% 16.56/8.38  
% 16.56/8.38  Ordering : KBO
% 16.56/8.38  
% 16.56/8.38  Simplification rules
% 16.56/8.38  ----------------------
% 16.56/8.38  #Subsume      : 724
% 16.56/8.38  #Demod        : 8876
% 16.56/8.38  #Tautology    : 3193
% 16.56/8.38  #SimpNegUnit  : 1
% 16.56/8.38  #BackRed      : 1
% 16.56/8.38  
% 16.56/8.38  #Partial instantiations: 33246
% 16.56/8.38  #Strategies tried      : 1
% 16.56/8.38  
% 16.56/8.38  Timing (in seconds)
% 16.56/8.38  ----------------------
% 16.56/8.39  Preprocessing        : 0.39
% 16.56/8.39  Parsing              : 0.17
% 16.56/8.39  CNF conversion       : 0.04
% 16.56/8.39  Main loop            : 7.16
% 16.56/8.39  Inferencing          : 1.84
% 16.56/8.39  Reduction            : 4.18
% 16.56/8.39  Demodulation         : 3.90
% 16.56/8.39  BG Simplification    : 0.16
% 16.56/8.39  Subsumption          : 0.77
% 16.56/8.39  Abstraction          : 0.22
% 16.56/8.39  MUC search           : 0.00
% 16.56/8.39  Cooper               : 0.00
% 16.56/8.39  Total                : 7.59
% 16.56/8.39  Index Insertion      : 0.00
% 16.56/8.39  Index Deletion       : 0.00
% 16.56/8.39  Index Matching       : 0.00
% 16.56/8.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
