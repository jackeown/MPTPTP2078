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
% DateTime   : Thu Dec  3 09:47:58 EST 2020

% Result     : Theorem 11.33s
% Output     : CNFRefutation 11.33s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 139 expanded)
%              Number of leaves         :   32 (  60 expanded)
%              Depth                    :   16
%              Number of atoms          :   69 ( 144 expanded)
%              Number of equality atoms :   53 ( 127 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_76,negated_conjecture,(
    ~ ! [A,B] :
        ( k2_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
       => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_zfmisc_1)).

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

tff(f_44,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_42,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_40,axiom,(
    ! [A,B] : k3_xboole_0(A,k2_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).

tff(f_38,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_48,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_46,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(c_66,plain,(
    '#skF_5' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_58,plain,(
    ! [A_28] : k2_tarski(A_28,A_28) = k1_tarski(A_28) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_153,plain,(
    ! [A_55,B_56] : k1_enumset1(A_55,A_55,B_56) = k2_tarski(A_55,B_56) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_40,plain,(
    ! [E_27,B_22,C_23] : r2_hidden(E_27,k1_enumset1(E_27,B_22,C_23)) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_171,plain,(
    ! [A_57,B_58] : r2_hidden(A_57,k2_tarski(A_57,B_58)) ),
    inference(superposition,[status(thm),theory(equality)],[c_153,c_40])).

tff(c_174,plain,(
    ! [A_28] : r2_hidden(A_28,k1_tarski(A_28)) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_171])).

tff(c_28,plain,(
    ! [A_15] : k5_xboole_0(A_15,k1_xboole_0) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_26,plain,(
    ! [A_13,B_14] : k4_xboole_0(A_13,k2_xboole_0(A_13,B_14)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_24,plain,(
    ! [A_11,B_12] : k3_xboole_0(A_11,k2_xboole_0(A_11,B_12)) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_212,plain,(
    ! [A_68,B_69] : k5_xboole_0(A_68,k3_xboole_0(A_68,B_69)) = k4_xboole_0(A_68,B_69) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_224,plain,(
    ! [A_11,B_12] : k4_xboole_0(A_11,k2_xboole_0(A_11,B_12)) = k5_xboole_0(A_11,A_11) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_212])).

tff(c_234,plain,(
    ! [A_11] : k5_xboole_0(A_11,A_11) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_224])).

tff(c_68,plain,(
    k2_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6')) = k1_tarski('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_32,plain,(
    ! [A_19,B_20] : k5_xboole_0(A_19,k4_xboole_0(B_20,A_19)) = k2_xboole_0(A_19,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_332,plain,(
    ! [A_81,B_82,C_83] : k5_xboole_0(k5_xboole_0(A_81,B_82),C_83) = k5_xboole_0(A_81,k5_xboole_0(B_82,C_83)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_812,plain,(
    ! [A_101,C_102] : k5_xboole_0(A_101,k5_xboole_0(A_101,C_102)) = k5_xboole_0(k1_xboole_0,C_102) ),
    inference(superposition,[status(thm),theory(equality)],[c_234,c_332])).

tff(c_902,plain,(
    ! [A_11] : k5_xboole_0(k1_xboole_0,A_11) = k5_xboole_0(A_11,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_234,c_812])).

tff(c_931,plain,(
    ! [A_11] : k5_xboole_0(k1_xboole_0,A_11) = A_11 ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_902])).

tff(c_370,plain,(
    ! [A_11,C_83] : k5_xboole_0(A_11,k5_xboole_0(A_11,C_83)) = k5_xboole_0(k1_xboole_0,C_83) ),
    inference(superposition,[status(thm),theory(equality)],[c_234,c_332])).

tff(c_1015,plain,(
    ! [A_104,C_105] : k5_xboole_0(A_104,k5_xboole_0(A_104,C_105)) = C_105 ),
    inference(demodulation,[status(thm),theory(equality)],[c_931,c_370])).

tff(c_1899,plain,(
    ! [A_148,B_149] : k5_xboole_0(A_148,k2_xboole_0(A_148,B_149)) = k4_xboole_0(B_149,A_148) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_1015])).

tff(c_1945,plain,(
    k5_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_5')) = k4_xboole_0(k1_tarski('#skF_6'),k1_tarski('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_1899])).

tff(c_1953,plain,(
    k4_xboole_0(k1_tarski('#skF_6'),k1_tarski('#skF_5')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_234,c_1945])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_227,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k3_xboole_0(B_2,A_1)) = k4_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_212])).

tff(c_1979,plain,(
    ! [A_153,B_154] : k5_xboole_0(A_153,k4_xboole_0(A_153,B_154)) = k3_xboole_0(B_154,A_153) ),
    inference(superposition,[status(thm),theory(equality)],[c_227,c_1015])).

tff(c_2015,plain,(
    k3_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6')) = k5_xboole_0(k1_tarski('#skF_6'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1953,c_1979])).

tff(c_2050,plain,(
    k3_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6')) = k1_tarski('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_2015])).

tff(c_8,plain,(
    ! [D_8,A_3,B_4] :
      ( r2_hidden(D_8,A_3)
      | ~ r2_hidden(D_8,k3_xboole_0(A_3,B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_2114,plain,(
    ! [D_8] :
      ( r2_hidden(D_8,k1_tarski('#skF_5'))
      | ~ r2_hidden(D_8,k1_tarski('#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2050,c_8])).

tff(c_60,plain,(
    ! [A_29,B_30] : k1_enumset1(A_29,A_29,B_30) = k2_tarski(A_29,B_30) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_1116,plain,(
    ! [E_107,C_108,B_109,A_110] :
      ( E_107 = C_108
      | E_107 = B_109
      | E_107 = A_110
      | ~ r2_hidden(E_107,k1_enumset1(A_110,B_109,C_108)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_5275,plain,(
    ! [E_230,B_231,A_232] :
      ( E_230 = B_231
      | E_230 = A_232
      | E_230 = A_232
      | ~ r2_hidden(E_230,k2_tarski(A_232,B_231)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_1116])).

tff(c_20267,plain,(
    ! [E_466,A_467] :
      ( E_466 = A_467
      | E_466 = A_467
      | E_466 = A_467
      | ~ r2_hidden(E_466,k1_tarski(A_467)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_5275])).

tff(c_20473,plain,(
    ! [D_468] :
      ( D_468 = '#skF_5'
      | ~ r2_hidden(D_468,k1_tarski('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_2114,c_20267])).

tff(c_20617,plain,(
    '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_174,c_20473])).

tff(c_20655,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_20617])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n018.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 15:30:27 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.33/4.55  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.33/4.56  
% 11.33/4.56  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.33/4.56  %$ r2_hidden > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3
% 11.33/4.56  
% 11.33/4.56  %Foreground sorts:
% 11.33/4.56  
% 11.33/4.56  
% 11.33/4.56  %Background operators:
% 11.33/4.56  
% 11.33/4.56  
% 11.33/4.56  %Foreground operators:
% 11.33/4.56  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 11.33/4.56  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.33/4.56  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 11.33/4.56  tff(k1_tarski, type, k1_tarski: $i > $i).
% 11.33/4.56  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 11.33/4.56  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 11.33/4.56  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 11.33/4.56  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 11.33/4.56  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 11.33/4.56  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 11.33/4.56  tff('#skF_5', type, '#skF_5': $i).
% 11.33/4.56  tff('#skF_6', type, '#skF_6': $i).
% 11.33/4.56  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 11.33/4.56  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 11.33/4.56  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 11.33/4.56  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.33/4.56  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.33/4.56  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 11.33/4.56  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 11.33/4.56  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 11.33/4.56  
% 11.33/4.57  tff(f_76, negated_conjecture, ~(![A, B]: ((k2_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_zfmisc_1)).
% 11.33/4.57  tff(f_65, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 11.33/4.57  tff(f_67, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 11.33/4.57  tff(f_63, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 11.33/4.57  tff(f_44, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 11.33/4.57  tff(f_42, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 11.33/4.57  tff(f_40, axiom, (![A, B]: (k3_xboole_0(A, k2_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_xboole_1)).
% 11.33/4.57  tff(f_38, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 11.33/4.57  tff(f_48, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 11.33/4.57  tff(f_46, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 11.33/4.57  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 11.33/4.57  tff(f_36, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 11.33/4.57  tff(c_66, plain, ('#skF_5'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_76])).
% 11.33/4.57  tff(c_58, plain, (![A_28]: (k2_tarski(A_28, A_28)=k1_tarski(A_28))), inference(cnfTransformation, [status(thm)], [f_65])).
% 11.33/4.57  tff(c_153, plain, (![A_55, B_56]: (k1_enumset1(A_55, A_55, B_56)=k2_tarski(A_55, B_56))), inference(cnfTransformation, [status(thm)], [f_67])).
% 11.33/4.57  tff(c_40, plain, (![E_27, B_22, C_23]: (r2_hidden(E_27, k1_enumset1(E_27, B_22, C_23)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 11.33/4.57  tff(c_171, plain, (![A_57, B_58]: (r2_hidden(A_57, k2_tarski(A_57, B_58)))), inference(superposition, [status(thm), theory('equality')], [c_153, c_40])).
% 11.33/4.57  tff(c_174, plain, (![A_28]: (r2_hidden(A_28, k1_tarski(A_28)))), inference(superposition, [status(thm), theory('equality')], [c_58, c_171])).
% 11.33/4.57  tff(c_28, plain, (![A_15]: (k5_xboole_0(A_15, k1_xboole_0)=A_15)), inference(cnfTransformation, [status(thm)], [f_44])).
% 11.33/4.57  tff(c_26, plain, (![A_13, B_14]: (k4_xboole_0(A_13, k2_xboole_0(A_13, B_14))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_42])).
% 11.33/4.57  tff(c_24, plain, (![A_11, B_12]: (k3_xboole_0(A_11, k2_xboole_0(A_11, B_12))=A_11)), inference(cnfTransformation, [status(thm)], [f_40])).
% 11.33/4.57  tff(c_212, plain, (![A_68, B_69]: (k5_xboole_0(A_68, k3_xboole_0(A_68, B_69))=k4_xboole_0(A_68, B_69))), inference(cnfTransformation, [status(thm)], [f_38])).
% 11.33/4.57  tff(c_224, plain, (![A_11, B_12]: (k4_xboole_0(A_11, k2_xboole_0(A_11, B_12))=k5_xboole_0(A_11, A_11))), inference(superposition, [status(thm), theory('equality')], [c_24, c_212])).
% 11.33/4.57  tff(c_234, plain, (![A_11]: (k5_xboole_0(A_11, A_11)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_26, c_224])).
% 11.33/4.57  tff(c_68, plain, (k2_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6'))=k1_tarski('#skF_5')), inference(cnfTransformation, [status(thm)], [f_76])).
% 11.33/4.57  tff(c_32, plain, (![A_19, B_20]: (k5_xboole_0(A_19, k4_xboole_0(B_20, A_19))=k2_xboole_0(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_48])).
% 11.33/4.57  tff(c_332, plain, (![A_81, B_82, C_83]: (k5_xboole_0(k5_xboole_0(A_81, B_82), C_83)=k5_xboole_0(A_81, k5_xboole_0(B_82, C_83)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 11.33/4.57  tff(c_812, plain, (![A_101, C_102]: (k5_xboole_0(A_101, k5_xboole_0(A_101, C_102))=k5_xboole_0(k1_xboole_0, C_102))), inference(superposition, [status(thm), theory('equality')], [c_234, c_332])).
% 11.33/4.57  tff(c_902, plain, (![A_11]: (k5_xboole_0(k1_xboole_0, A_11)=k5_xboole_0(A_11, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_234, c_812])).
% 11.33/4.57  tff(c_931, plain, (![A_11]: (k5_xboole_0(k1_xboole_0, A_11)=A_11)), inference(demodulation, [status(thm), theory('equality')], [c_28, c_902])).
% 11.33/4.57  tff(c_370, plain, (![A_11, C_83]: (k5_xboole_0(A_11, k5_xboole_0(A_11, C_83))=k5_xboole_0(k1_xboole_0, C_83))), inference(superposition, [status(thm), theory('equality')], [c_234, c_332])).
% 11.33/4.57  tff(c_1015, plain, (![A_104, C_105]: (k5_xboole_0(A_104, k5_xboole_0(A_104, C_105))=C_105)), inference(demodulation, [status(thm), theory('equality')], [c_931, c_370])).
% 11.33/4.57  tff(c_1899, plain, (![A_148, B_149]: (k5_xboole_0(A_148, k2_xboole_0(A_148, B_149))=k4_xboole_0(B_149, A_148))), inference(superposition, [status(thm), theory('equality')], [c_32, c_1015])).
% 11.33/4.57  tff(c_1945, plain, (k5_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_5'))=k4_xboole_0(k1_tarski('#skF_6'), k1_tarski('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_68, c_1899])).
% 11.33/4.57  tff(c_1953, plain, (k4_xboole_0(k1_tarski('#skF_6'), k1_tarski('#skF_5'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_234, c_1945])).
% 11.33/4.57  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 11.33/4.57  tff(c_227, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k3_xboole_0(B_2, A_1))=k4_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_212])).
% 11.33/4.57  tff(c_1979, plain, (![A_153, B_154]: (k5_xboole_0(A_153, k4_xboole_0(A_153, B_154))=k3_xboole_0(B_154, A_153))), inference(superposition, [status(thm), theory('equality')], [c_227, c_1015])).
% 11.33/4.57  tff(c_2015, plain, (k3_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6'))=k5_xboole_0(k1_tarski('#skF_6'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1953, c_1979])).
% 11.33/4.57  tff(c_2050, plain, (k3_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6'))=k1_tarski('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_2015])).
% 11.33/4.57  tff(c_8, plain, (![D_8, A_3, B_4]: (r2_hidden(D_8, A_3) | ~r2_hidden(D_8, k3_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 11.33/4.57  tff(c_2114, plain, (![D_8]: (r2_hidden(D_8, k1_tarski('#skF_5')) | ~r2_hidden(D_8, k1_tarski('#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_2050, c_8])).
% 11.33/4.57  tff(c_60, plain, (![A_29, B_30]: (k1_enumset1(A_29, A_29, B_30)=k2_tarski(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_67])).
% 11.33/4.57  tff(c_1116, plain, (![E_107, C_108, B_109, A_110]: (E_107=C_108 | E_107=B_109 | E_107=A_110 | ~r2_hidden(E_107, k1_enumset1(A_110, B_109, C_108)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 11.33/4.57  tff(c_5275, plain, (![E_230, B_231, A_232]: (E_230=B_231 | E_230=A_232 | E_230=A_232 | ~r2_hidden(E_230, k2_tarski(A_232, B_231)))), inference(superposition, [status(thm), theory('equality')], [c_60, c_1116])).
% 11.33/4.57  tff(c_20267, plain, (![E_466, A_467]: (E_466=A_467 | E_466=A_467 | E_466=A_467 | ~r2_hidden(E_466, k1_tarski(A_467)))), inference(superposition, [status(thm), theory('equality')], [c_58, c_5275])).
% 11.33/4.57  tff(c_20473, plain, (![D_468]: (D_468='#skF_5' | ~r2_hidden(D_468, k1_tarski('#skF_6')))), inference(resolution, [status(thm)], [c_2114, c_20267])).
% 11.33/4.57  tff(c_20617, plain, ('#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_174, c_20473])).
% 11.33/4.57  tff(c_20655, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_20617])).
% 11.33/4.57  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.33/4.57  
% 11.33/4.57  Inference rules
% 11.33/4.57  ----------------------
% 11.33/4.57  #Ref     : 0
% 11.33/4.57  #Sup     : 4895
% 11.33/4.57  #Fact    : 6
% 11.33/4.57  #Define  : 0
% 11.33/4.57  #Split   : 0
% 11.33/4.57  #Chain   : 0
% 11.33/4.57  #Close   : 0
% 11.33/4.57  
% 11.33/4.57  Ordering : KBO
% 11.33/4.57  
% 11.33/4.57  Simplification rules
% 11.33/4.57  ----------------------
% 11.33/4.57  #Subsume      : 399
% 11.33/4.57  #Demod        : 5663
% 11.33/4.57  #Tautology    : 2716
% 11.33/4.57  #SimpNegUnit  : 1
% 11.33/4.57  #BackRed      : 4
% 11.33/4.57  
% 11.33/4.57  #Partial instantiations: 0
% 11.33/4.57  #Strategies tried      : 1
% 11.33/4.57  
% 11.33/4.57  Timing (in seconds)
% 11.33/4.57  ----------------------
% 11.33/4.57  Preprocessing        : 0.33
% 11.33/4.57  Parsing              : 0.17
% 11.33/4.57  CNF conversion       : 0.03
% 11.33/4.57  Main loop            : 3.46
% 11.33/4.58  Inferencing          : 0.76
% 11.33/4.58  Reduction            : 1.81
% 11.33/4.58  Demodulation         : 1.60
% 11.33/4.58  BG Simplification    : 0.10
% 11.33/4.58  Subsumption          : 0.62
% 11.33/4.58  Abstraction          : 0.15
% 11.33/4.58  MUC search           : 0.00
% 11.33/4.58  Cooper               : 0.00
% 11.33/4.58  Total                : 3.83
% 11.33/4.58  Index Insertion      : 0.00
% 11.33/4.58  Index Deletion       : 0.00
% 11.33/4.58  Index Matching       : 0.00
% 11.33/4.58  BG Taut test         : 0.00
%------------------------------------------------------------------------------
