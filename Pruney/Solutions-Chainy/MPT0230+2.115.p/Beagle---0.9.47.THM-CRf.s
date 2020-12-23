%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:10 EST 2020

% Result     : Theorem 2.57s
% Output     : CNFRefutation 2.57s
% Verified   : 
% Statistics : Number of formulae       :   74 (  95 expanded)
%              Number of leaves         :   37 (  48 expanded)
%              Depth                    :   15
%              Number of atoms          :   73 ( 111 expanded)
%              Number of equality atoms :   52 (  75 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_7 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

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

tff('#skF_7',type,(
    '#skF_7': $i )).

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

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_98,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( r1_tarski(k1_tarski(A),k2_tarski(B,C))
          & A != B
          & A != C ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_zfmisc_1)).

tff(f_86,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_84,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_80,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_enumset1(A,B,C),k1_tarski(D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).

tff(f_59,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_61,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_49,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_51,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_57,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_55,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_78,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(c_58,plain,(
    '#skF_5' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_56,plain,(
    '#skF_7' != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_52,plain,(
    ! [A_34,B_35,C_36] : k2_enumset1(A_34,A_34,B_35,C_36) = k1_enumset1(A_34,B_35,C_36) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_50,plain,(
    ! [A_32,B_33] : k1_enumset1(A_32,A_32,B_33) = k2_tarski(A_32,B_33) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_648,plain,(
    ! [A_114,B_115,C_116,D_117] : k2_xboole_0(k1_enumset1(A_114,B_115,C_116),k1_tarski(D_117)) = k2_enumset1(A_114,B_115,C_116,D_117) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_657,plain,(
    ! [A_32,B_33,D_117] : k2_xboole_0(k2_tarski(A_32,B_33),k1_tarski(D_117)) = k2_enumset1(A_32,A_32,B_33,D_117) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_648])).

tff(c_662,plain,(
    ! [A_122,B_123,D_124] : k2_xboole_0(k2_tarski(A_122,B_123),k1_tarski(D_124)) = k1_enumset1(A_122,B_123,D_124) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_657])).

tff(c_16,plain,(
    ! [A_16] : k5_xboole_0(A_16,k1_xboole_0) = A_16 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_18,plain,(
    ! [A_17] : r1_xboole_0(A_17,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_8,plain,(
    ! [A_8] :
      ( r2_hidden('#skF_2'(A_8),A_8)
      | k1_xboole_0 = A_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_158,plain,(
    ! [A_68,B_69,C_70] :
      ( ~ r1_xboole_0(A_68,B_69)
      | ~ r2_hidden(C_70,k3_xboole_0(A_68,B_69)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_182,plain,(
    ! [A_74,B_75] :
      ( ~ r1_xboole_0(A_74,B_75)
      | k3_xboole_0(A_74,B_75) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_158])).

tff(c_186,plain,(
    ! [A_17] : k3_xboole_0(A_17,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_18,c_182])).

tff(c_209,plain,(
    ! [A_77,B_78] : k5_xboole_0(A_77,k3_xboole_0(A_77,B_78)) = k4_xboole_0(A_77,B_78) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_218,plain,(
    ! [A_17] : k5_xboole_0(A_17,k1_xboole_0) = k4_xboole_0(A_17,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_186,c_209])).

tff(c_228,plain,(
    ! [A_79] : k4_xboole_0(A_79,k1_xboole_0) = A_79 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_218])).

tff(c_14,plain,(
    ! [A_14,B_15] : k4_xboole_0(A_14,k4_xboole_0(A_14,B_15)) = k3_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_237,plain,(
    ! [A_79] : k4_xboole_0(A_79,A_79) = k3_xboole_0(A_79,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_228,c_14])).

tff(c_242,plain,(
    ! [A_79] : k4_xboole_0(A_79,A_79) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_186,c_237])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_224,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k4_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_209])).

tff(c_279,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_242,c_224])).

tff(c_60,plain,(
    r1_tarski(k1_tarski('#skF_5'),k2_tarski('#skF_6','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_117,plain,(
    ! [A_60,B_61] :
      ( k3_xboole_0(A_60,B_61) = A_60
      | ~ r1_tarski(A_60,B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_121,plain,(
    k3_xboole_0(k1_tarski('#skF_5'),k2_tarski('#skF_6','#skF_7')) = k1_tarski('#skF_5') ),
    inference(resolution,[status(thm)],[c_60,c_117])).

tff(c_221,plain,(
    k5_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_5')) = k4_xboole_0(k1_tarski('#skF_5'),k2_tarski('#skF_6','#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_121,c_209])).

tff(c_402,plain,(
    k4_xboole_0(k1_tarski('#skF_5'),k2_tarski('#skF_6','#skF_7')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_279,c_221])).

tff(c_20,plain,(
    ! [A_18,B_19] : k5_xboole_0(A_18,k4_xboole_0(B_19,A_18)) = k2_xboole_0(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_406,plain,(
    k2_xboole_0(k2_tarski('#skF_6','#skF_7'),k1_tarski('#skF_5')) = k5_xboole_0(k2_tarski('#skF_6','#skF_7'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_402,c_20])).

tff(c_412,plain,(
    k2_xboole_0(k2_tarski('#skF_6','#skF_7'),k1_tarski('#skF_5')) = k2_tarski('#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_406])).

tff(c_668,plain,(
    k1_enumset1('#skF_6','#skF_7','#skF_5') = k2_tarski('#skF_6','#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_662,c_412])).

tff(c_24,plain,(
    ! [E_26,A_20,B_21] : r2_hidden(E_26,k1_enumset1(A_20,B_21,E_26)) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_696,plain,(
    r2_hidden('#skF_5',k2_tarski('#skF_6','#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_668,c_24])).

tff(c_491,plain,(
    ! [E_99,C_100,B_101,A_102] :
      ( E_99 = C_100
      | E_99 = B_101
      | E_99 = A_102
      | ~ r2_hidden(E_99,k1_enumset1(A_102,B_101,C_100)) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_498,plain,(
    ! [E_99,B_33,A_32] :
      ( E_99 = B_33
      | E_99 = A_32
      | E_99 = A_32
      | ~ r2_hidden(E_99,k2_tarski(A_32,B_33)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_491])).

tff(c_705,plain,
    ( '#skF_7' = '#skF_5'
    | '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_696,c_498])).

tff(c_709,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_58,c_56,c_705])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:21:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.57/1.39  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.57/1.39  
% 2.57/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.57/1.40  %$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_7 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_1
% 2.57/1.40  
% 2.57/1.40  %Foreground sorts:
% 2.57/1.40  
% 2.57/1.40  
% 2.57/1.40  %Background operators:
% 2.57/1.40  
% 2.57/1.40  
% 2.57/1.40  %Foreground operators:
% 2.57/1.40  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.57/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.57/1.40  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.57/1.40  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.57/1.40  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.57/1.40  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.57/1.40  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.57/1.40  tff('#skF_7', type, '#skF_7': $i).
% 2.57/1.40  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.57/1.40  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.57/1.40  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.57/1.40  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.57/1.40  tff('#skF_5', type, '#skF_5': $i).
% 2.57/1.40  tff('#skF_6', type, '#skF_6': $i).
% 2.57/1.40  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.57/1.40  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.57/1.40  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 2.57/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.57/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.57/1.40  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.57/1.40  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 2.57/1.40  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.57/1.40  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.57/1.40  
% 2.57/1.41  tff(f_98, negated_conjecture, ~(![A, B, C]: ~((r1_tarski(k1_tarski(A), k2_tarski(B, C)) & ~(A = B)) & ~(A = C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_zfmisc_1)).
% 2.57/1.41  tff(f_86, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 2.57/1.41  tff(f_84, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.57/1.41  tff(f_80, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_enumset1(A, B, C), k1_tarski(D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_enumset1)).
% 2.57/1.41  tff(f_59, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 2.57/1.41  tff(f_61, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.57/1.41  tff(f_49, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.57/1.41  tff(f_41, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.57/1.41  tff(f_51, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.57/1.41  tff(f_57, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.57/1.41  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 2.57/1.41  tff(f_55, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.57/1.41  tff(f_63, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 2.57/1.41  tff(f_78, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 2.57/1.41  tff(c_58, plain, ('#skF_5'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.57/1.41  tff(c_56, plain, ('#skF_7'!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.57/1.41  tff(c_52, plain, (![A_34, B_35, C_36]: (k2_enumset1(A_34, A_34, B_35, C_36)=k1_enumset1(A_34, B_35, C_36))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.57/1.41  tff(c_50, plain, (![A_32, B_33]: (k1_enumset1(A_32, A_32, B_33)=k2_tarski(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.57/1.41  tff(c_648, plain, (![A_114, B_115, C_116, D_117]: (k2_xboole_0(k1_enumset1(A_114, B_115, C_116), k1_tarski(D_117))=k2_enumset1(A_114, B_115, C_116, D_117))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.57/1.41  tff(c_657, plain, (![A_32, B_33, D_117]: (k2_xboole_0(k2_tarski(A_32, B_33), k1_tarski(D_117))=k2_enumset1(A_32, A_32, B_33, D_117))), inference(superposition, [status(thm), theory('equality')], [c_50, c_648])).
% 2.57/1.41  tff(c_662, plain, (![A_122, B_123, D_124]: (k2_xboole_0(k2_tarski(A_122, B_123), k1_tarski(D_124))=k1_enumset1(A_122, B_123, D_124))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_657])).
% 2.57/1.41  tff(c_16, plain, (![A_16]: (k5_xboole_0(A_16, k1_xboole_0)=A_16)), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.57/1.41  tff(c_18, plain, (![A_17]: (r1_xboole_0(A_17, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.57/1.41  tff(c_8, plain, (![A_8]: (r2_hidden('#skF_2'(A_8), A_8) | k1_xboole_0=A_8)), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.57/1.41  tff(c_158, plain, (![A_68, B_69, C_70]: (~r1_xboole_0(A_68, B_69) | ~r2_hidden(C_70, k3_xboole_0(A_68, B_69)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.57/1.41  tff(c_182, plain, (![A_74, B_75]: (~r1_xboole_0(A_74, B_75) | k3_xboole_0(A_74, B_75)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_158])).
% 2.57/1.41  tff(c_186, plain, (![A_17]: (k3_xboole_0(A_17, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_182])).
% 2.57/1.41  tff(c_209, plain, (![A_77, B_78]: (k5_xboole_0(A_77, k3_xboole_0(A_77, B_78))=k4_xboole_0(A_77, B_78))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.57/1.41  tff(c_218, plain, (![A_17]: (k5_xboole_0(A_17, k1_xboole_0)=k4_xboole_0(A_17, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_186, c_209])).
% 2.57/1.41  tff(c_228, plain, (![A_79]: (k4_xboole_0(A_79, k1_xboole_0)=A_79)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_218])).
% 2.57/1.41  tff(c_14, plain, (![A_14, B_15]: (k4_xboole_0(A_14, k4_xboole_0(A_14, B_15))=k3_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.57/1.41  tff(c_237, plain, (![A_79]: (k4_xboole_0(A_79, A_79)=k3_xboole_0(A_79, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_228, c_14])).
% 2.57/1.41  tff(c_242, plain, (![A_79]: (k4_xboole_0(A_79, A_79)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_186, c_237])).
% 2.57/1.41  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.57/1.41  tff(c_224, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k4_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_209])).
% 2.57/1.41  tff(c_279, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_242, c_224])).
% 2.57/1.41  tff(c_60, plain, (r1_tarski(k1_tarski('#skF_5'), k2_tarski('#skF_6', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.57/1.41  tff(c_117, plain, (![A_60, B_61]: (k3_xboole_0(A_60, B_61)=A_60 | ~r1_tarski(A_60, B_61))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.57/1.41  tff(c_121, plain, (k3_xboole_0(k1_tarski('#skF_5'), k2_tarski('#skF_6', '#skF_7'))=k1_tarski('#skF_5')), inference(resolution, [status(thm)], [c_60, c_117])).
% 2.57/1.41  tff(c_221, plain, (k5_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_5'))=k4_xboole_0(k1_tarski('#skF_5'), k2_tarski('#skF_6', '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_121, c_209])).
% 2.57/1.41  tff(c_402, plain, (k4_xboole_0(k1_tarski('#skF_5'), k2_tarski('#skF_6', '#skF_7'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_279, c_221])).
% 2.57/1.41  tff(c_20, plain, (![A_18, B_19]: (k5_xboole_0(A_18, k4_xboole_0(B_19, A_18))=k2_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.57/1.41  tff(c_406, plain, (k2_xboole_0(k2_tarski('#skF_6', '#skF_7'), k1_tarski('#skF_5'))=k5_xboole_0(k2_tarski('#skF_6', '#skF_7'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_402, c_20])).
% 2.57/1.41  tff(c_412, plain, (k2_xboole_0(k2_tarski('#skF_6', '#skF_7'), k1_tarski('#skF_5'))=k2_tarski('#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_406])).
% 2.57/1.41  tff(c_668, plain, (k1_enumset1('#skF_6', '#skF_7', '#skF_5')=k2_tarski('#skF_6', '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_662, c_412])).
% 2.57/1.41  tff(c_24, plain, (![E_26, A_20, B_21]: (r2_hidden(E_26, k1_enumset1(A_20, B_21, E_26)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.57/1.41  tff(c_696, plain, (r2_hidden('#skF_5', k2_tarski('#skF_6', '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_668, c_24])).
% 2.57/1.41  tff(c_491, plain, (![E_99, C_100, B_101, A_102]: (E_99=C_100 | E_99=B_101 | E_99=A_102 | ~r2_hidden(E_99, k1_enumset1(A_102, B_101, C_100)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.57/1.41  tff(c_498, plain, (![E_99, B_33, A_32]: (E_99=B_33 | E_99=A_32 | E_99=A_32 | ~r2_hidden(E_99, k2_tarski(A_32, B_33)))), inference(superposition, [status(thm), theory('equality')], [c_50, c_491])).
% 2.57/1.41  tff(c_705, plain, ('#skF_7'='#skF_5' | '#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_696, c_498])).
% 2.57/1.41  tff(c_709, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_58, c_56, c_705])).
% 2.57/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.57/1.41  
% 2.57/1.41  Inference rules
% 2.57/1.41  ----------------------
% 2.57/1.41  #Ref     : 0
% 2.57/1.41  #Sup     : 150
% 2.57/1.41  #Fact    : 0
% 2.57/1.41  #Define  : 0
% 2.57/1.41  #Split   : 1
% 2.57/1.41  #Chain   : 0
% 2.57/1.41  #Close   : 0
% 2.57/1.41  
% 2.57/1.41  Ordering : KBO
% 2.57/1.41  
% 2.57/1.41  Simplification rules
% 2.57/1.41  ----------------------
% 2.57/1.41  #Subsume      : 7
% 2.57/1.41  #Demod        : 66
% 2.57/1.41  #Tautology    : 103
% 2.57/1.41  #SimpNegUnit  : 4
% 2.57/1.41  #BackRed      : 1
% 2.57/1.41  
% 2.57/1.41  #Partial instantiations: 0
% 2.57/1.41  #Strategies tried      : 1
% 2.57/1.41  
% 2.57/1.41  Timing (in seconds)
% 2.57/1.41  ----------------------
% 2.57/1.41  Preprocessing        : 0.31
% 2.57/1.41  Parsing              : 0.16
% 2.57/1.41  CNF conversion       : 0.02
% 2.57/1.41  Main loop            : 0.29
% 2.57/1.41  Inferencing          : 0.11
% 2.57/1.41  Reduction            : 0.10
% 2.57/1.41  Demodulation         : 0.07
% 2.57/1.41  BG Simplification    : 0.02
% 2.57/1.41  Subsumption          : 0.05
% 2.57/1.41  Abstraction          : 0.01
% 2.57/1.41  MUC search           : 0.00
% 2.57/1.41  Cooper               : 0.00
% 2.57/1.41  Total                : 0.63
% 2.57/1.41  Index Insertion      : 0.00
% 2.57/1.41  Index Deletion       : 0.00
% 2.57/1.41  Index Matching       : 0.00
% 2.57/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
