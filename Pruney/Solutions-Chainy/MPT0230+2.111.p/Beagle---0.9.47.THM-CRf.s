%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:10 EST 2020

% Result     : Theorem 2.92s
% Output     : CNFRefutation 2.92s
% Verified   : 
% Statistics : Number of formulae       :   76 (  97 expanded)
%              Number of leaves         :   39 (  50 expanded)
%              Depth                    :   12
%              Number of atoms          :   73 ( 111 expanded)
%              Number of equality atoms :   52 (  75 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_7 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_1

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

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_102,negated_conjecture,(
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

tff(f_57,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

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

tff(f_59,axiom,(
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

tff(c_62,plain,(
    '#skF_5' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_60,plain,(
    '#skF_7' != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_52,plain,(
    ! [A_34,B_35,C_36] : k2_enumset1(A_34,A_34,B_35,C_36) = k1_enumset1(A_34,B_35,C_36) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_50,plain,(
    ! [A_32,B_33] : k1_enumset1(A_32,A_32,B_33) = k2_tarski(A_32,B_33) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_609,plain,(
    ! [A_120,B_121,C_122,D_123] : k2_xboole_0(k1_enumset1(A_120,B_121,C_122),k1_tarski(D_123)) = k2_enumset1(A_120,B_121,C_122,D_123) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_618,plain,(
    ! [A_32,B_33,D_123] : k2_xboole_0(k2_tarski(A_32,B_33),k1_tarski(D_123)) = k2_enumset1(A_32,A_32,B_33,D_123) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_609])).

tff(c_647,plain,(
    ! [A_125,B_126,D_127] : k2_xboole_0(k2_tarski(A_125,B_126),k1_tarski(D_127)) = k1_enumset1(A_125,B_126,D_127) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_618])).

tff(c_14,plain,(
    ! [A_14] : k4_xboole_0(A_14,k1_xboole_0) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_18,plain,(
    ! [A_17] : r1_xboole_0(A_17,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_8,plain,(
    ! [A_8] :
      ( r2_hidden('#skF_2'(A_8),A_8)
      | k1_xboole_0 = A_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_166,plain,(
    ! [A_78,B_79,C_80] :
      ( ~ r1_xboole_0(A_78,B_79)
      | ~ r2_hidden(C_80,k3_xboole_0(A_78,B_79)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_190,plain,(
    ! [A_84,B_85] :
      ( ~ r1_xboole_0(A_84,B_85)
      | k3_xboole_0(A_84,B_85) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_166])).

tff(c_194,plain,(
    ! [A_17] : k3_xboole_0(A_17,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_18,c_190])).

tff(c_290,plain,(
    ! [A_91,B_92] : k5_xboole_0(A_91,k3_xboole_0(A_91,B_92)) = k4_xboole_0(A_91,B_92) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_303,plain,(
    ! [A_17] : k5_xboole_0(A_17,k1_xboole_0) = k4_xboole_0(A_17,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_194,c_290])).

tff(c_316,plain,(
    ! [A_17] : k5_xboole_0(A_17,k1_xboole_0) = A_17 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_303])).

tff(c_217,plain,(
    ! [A_87,B_88] : k4_xboole_0(A_87,k4_xboole_0(A_87,B_88)) = k3_xboole_0(A_87,B_88) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_235,plain,(
    ! [A_14] : k4_xboole_0(A_14,A_14) = k3_xboole_0(A_14,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_217])).

tff(c_238,plain,(
    ! [A_14] : k4_xboole_0(A_14,A_14) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_194,c_235])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_313,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k4_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_290])).

tff(c_317,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_238,c_313])).

tff(c_64,plain,(
    r1_tarski(k1_tarski('#skF_5'),k2_tarski('#skF_6','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_121,plain,(
    ! [A_71,B_72] :
      ( k3_xboole_0(A_71,B_72) = A_71
      | ~ r1_tarski(A_71,B_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_125,plain,(
    k3_xboole_0(k1_tarski('#skF_5'),k2_tarski('#skF_6','#skF_7')) = k1_tarski('#skF_5') ),
    inference(resolution,[status(thm)],[c_64,c_121])).

tff(c_306,plain,(
    k5_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_5')) = k4_xboole_0(k1_tarski('#skF_5'),k2_tarski('#skF_6','#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_125,c_290])).

tff(c_397,plain,(
    k4_xboole_0(k1_tarski('#skF_5'),k2_tarski('#skF_6','#skF_7')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_317,c_306])).

tff(c_20,plain,(
    ! [A_18,B_19] : k5_xboole_0(A_18,k4_xboole_0(B_19,A_18)) = k2_xboole_0(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_404,plain,(
    k2_xboole_0(k2_tarski('#skF_6','#skF_7'),k1_tarski('#skF_5')) = k5_xboole_0(k2_tarski('#skF_6','#skF_7'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_397,c_20])).

tff(c_408,plain,(
    k2_xboole_0(k2_tarski('#skF_6','#skF_7'),k1_tarski('#skF_5')) = k2_tarski('#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_316,c_404])).

tff(c_653,plain,(
    k1_enumset1('#skF_6','#skF_7','#skF_5') = k2_tarski('#skF_6','#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_647,c_408])).

tff(c_24,plain,(
    ! [E_26,A_20,B_21] : r2_hidden(E_26,k1_enumset1(A_20,B_21,E_26)) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_681,plain,(
    r2_hidden('#skF_5',k2_tarski('#skF_6','#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_653,c_24])).

tff(c_536,plain,(
    ! [E_111,C_112,B_113,A_114] :
      ( E_111 = C_112
      | E_111 = B_113
      | E_111 = A_114
      | ~ r2_hidden(E_111,k1_enumset1(A_114,B_113,C_112)) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_543,plain,(
    ! [E_111,B_33,A_32] :
      ( E_111 = B_33
      | E_111 = A_32
      | E_111 = A_32
      | ~ r2_hidden(E_111,k2_tarski(A_32,B_33)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_536])).

tff(c_690,plain,
    ( '#skF_7' = '#skF_5'
    | '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_681,c_543])).

tff(c_694,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_62,c_60,c_690])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:14:37 EST 2020
% 0.20/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.92/1.39  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.92/1.40  
% 2.92/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.92/1.40  %$ r2_hidden > r1_xboole_0 > r1_tarski > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_7 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_1
% 2.92/1.40  
% 2.92/1.40  %Foreground sorts:
% 2.92/1.40  
% 2.92/1.40  
% 2.92/1.40  %Background operators:
% 2.92/1.40  
% 2.92/1.40  
% 2.92/1.40  %Foreground operators:
% 2.92/1.40  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.92/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.92/1.40  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.92/1.40  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.92/1.40  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.92/1.40  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.92/1.40  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.92/1.40  tff('#skF_7', type, '#skF_7': $i).
% 2.92/1.40  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.92/1.40  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.92/1.40  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.92/1.40  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.92/1.40  tff('#skF_5', type, '#skF_5': $i).
% 2.92/1.40  tff('#skF_6', type, '#skF_6': $i).
% 2.92/1.40  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.92/1.40  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.92/1.40  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.92/1.40  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 2.92/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.92/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.92/1.40  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.92/1.40  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 2.92/1.40  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.92/1.40  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.92/1.40  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.92/1.40  
% 2.92/1.41  tff(f_102, negated_conjecture, ~(![A, B, C]: ~((r1_tarski(k1_tarski(A), k2_tarski(B, C)) & ~(A = B)) & ~(A = C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_zfmisc_1)).
% 2.92/1.41  tff(f_86, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 2.92/1.41  tff(f_84, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.92/1.41  tff(f_80, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_enumset1(A, B, C), k1_tarski(D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_enumset1)).
% 2.92/1.41  tff(f_57, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 2.92/1.41  tff(f_61, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.92/1.41  tff(f_49, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.92/1.41  tff(f_41, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.92/1.41  tff(f_51, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.92/1.41  tff(f_59, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.92/1.41  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 2.92/1.41  tff(f_55, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.92/1.41  tff(f_63, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 2.92/1.41  tff(f_78, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 2.92/1.41  tff(c_62, plain, ('#skF_5'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.92/1.41  tff(c_60, plain, ('#skF_7'!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.92/1.41  tff(c_52, plain, (![A_34, B_35, C_36]: (k2_enumset1(A_34, A_34, B_35, C_36)=k1_enumset1(A_34, B_35, C_36))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.92/1.41  tff(c_50, plain, (![A_32, B_33]: (k1_enumset1(A_32, A_32, B_33)=k2_tarski(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.92/1.41  tff(c_609, plain, (![A_120, B_121, C_122, D_123]: (k2_xboole_0(k1_enumset1(A_120, B_121, C_122), k1_tarski(D_123))=k2_enumset1(A_120, B_121, C_122, D_123))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.92/1.41  tff(c_618, plain, (![A_32, B_33, D_123]: (k2_xboole_0(k2_tarski(A_32, B_33), k1_tarski(D_123))=k2_enumset1(A_32, A_32, B_33, D_123))), inference(superposition, [status(thm), theory('equality')], [c_50, c_609])).
% 2.92/1.41  tff(c_647, plain, (![A_125, B_126, D_127]: (k2_xboole_0(k2_tarski(A_125, B_126), k1_tarski(D_127))=k1_enumset1(A_125, B_126, D_127))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_618])).
% 2.92/1.41  tff(c_14, plain, (![A_14]: (k4_xboole_0(A_14, k1_xboole_0)=A_14)), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.92/1.41  tff(c_18, plain, (![A_17]: (r1_xboole_0(A_17, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.92/1.41  tff(c_8, plain, (![A_8]: (r2_hidden('#skF_2'(A_8), A_8) | k1_xboole_0=A_8)), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.92/1.41  tff(c_166, plain, (![A_78, B_79, C_80]: (~r1_xboole_0(A_78, B_79) | ~r2_hidden(C_80, k3_xboole_0(A_78, B_79)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.92/1.41  tff(c_190, plain, (![A_84, B_85]: (~r1_xboole_0(A_84, B_85) | k3_xboole_0(A_84, B_85)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_166])).
% 2.92/1.41  tff(c_194, plain, (![A_17]: (k3_xboole_0(A_17, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_190])).
% 2.92/1.41  tff(c_290, plain, (![A_91, B_92]: (k5_xboole_0(A_91, k3_xboole_0(A_91, B_92))=k4_xboole_0(A_91, B_92))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.92/1.41  tff(c_303, plain, (![A_17]: (k5_xboole_0(A_17, k1_xboole_0)=k4_xboole_0(A_17, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_194, c_290])).
% 2.92/1.41  tff(c_316, plain, (![A_17]: (k5_xboole_0(A_17, k1_xboole_0)=A_17)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_303])).
% 2.92/1.41  tff(c_217, plain, (![A_87, B_88]: (k4_xboole_0(A_87, k4_xboole_0(A_87, B_88))=k3_xboole_0(A_87, B_88))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.92/1.41  tff(c_235, plain, (![A_14]: (k4_xboole_0(A_14, A_14)=k3_xboole_0(A_14, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_14, c_217])).
% 2.92/1.41  tff(c_238, plain, (![A_14]: (k4_xboole_0(A_14, A_14)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_194, c_235])).
% 2.92/1.41  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.92/1.41  tff(c_313, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k4_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_290])).
% 2.92/1.41  tff(c_317, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_238, c_313])).
% 2.92/1.41  tff(c_64, plain, (r1_tarski(k1_tarski('#skF_5'), k2_tarski('#skF_6', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.92/1.41  tff(c_121, plain, (![A_71, B_72]: (k3_xboole_0(A_71, B_72)=A_71 | ~r1_tarski(A_71, B_72))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.92/1.41  tff(c_125, plain, (k3_xboole_0(k1_tarski('#skF_5'), k2_tarski('#skF_6', '#skF_7'))=k1_tarski('#skF_5')), inference(resolution, [status(thm)], [c_64, c_121])).
% 2.92/1.41  tff(c_306, plain, (k5_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_5'))=k4_xboole_0(k1_tarski('#skF_5'), k2_tarski('#skF_6', '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_125, c_290])).
% 2.92/1.41  tff(c_397, plain, (k4_xboole_0(k1_tarski('#skF_5'), k2_tarski('#skF_6', '#skF_7'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_317, c_306])).
% 2.92/1.41  tff(c_20, plain, (![A_18, B_19]: (k5_xboole_0(A_18, k4_xboole_0(B_19, A_18))=k2_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.92/1.41  tff(c_404, plain, (k2_xboole_0(k2_tarski('#skF_6', '#skF_7'), k1_tarski('#skF_5'))=k5_xboole_0(k2_tarski('#skF_6', '#skF_7'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_397, c_20])).
% 2.92/1.41  tff(c_408, plain, (k2_xboole_0(k2_tarski('#skF_6', '#skF_7'), k1_tarski('#skF_5'))=k2_tarski('#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_316, c_404])).
% 2.92/1.41  tff(c_653, plain, (k1_enumset1('#skF_6', '#skF_7', '#skF_5')=k2_tarski('#skF_6', '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_647, c_408])).
% 2.92/1.41  tff(c_24, plain, (![E_26, A_20, B_21]: (r2_hidden(E_26, k1_enumset1(A_20, B_21, E_26)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.92/1.41  tff(c_681, plain, (r2_hidden('#skF_5', k2_tarski('#skF_6', '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_653, c_24])).
% 2.92/1.41  tff(c_536, plain, (![E_111, C_112, B_113, A_114]: (E_111=C_112 | E_111=B_113 | E_111=A_114 | ~r2_hidden(E_111, k1_enumset1(A_114, B_113, C_112)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.92/1.41  tff(c_543, plain, (![E_111, B_33, A_32]: (E_111=B_33 | E_111=A_32 | E_111=A_32 | ~r2_hidden(E_111, k2_tarski(A_32, B_33)))), inference(superposition, [status(thm), theory('equality')], [c_50, c_536])).
% 2.92/1.41  tff(c_690, plain, ('#skF_7'='#skF_5' | '#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_681, c_543])).
% 2.92/1.41  tff(c_694, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_62, c_60, c_690])).
% 2.92/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.92/1.41  
% 2.92/1.41  Inference rules
% 2.92/1.41  ----------------------
% 2.92/1.41  #Ref     : 0
% 2.92/1.41  #Sup     : 147
% 2.92/1.41  #Fact    : 0
% 2.92/1.41  #Define  : 0
% 2.92/1.41  #Split   : 1
% 2.92/1.41  #Chain   : 0
% 2.92/1.41  #Close   : 0
% 2.92/1.41  
% 2.92/1.41  Ordering : KBO
% 2.92/1.41  
% 2.92/1.41  Simplification rules
% 2.92/1.41  ----------------------
% 2.92/1.41  #Subsume      : 5
% 2.92/1.41  #Demod        : 58
% 2.92/1.41  #Tautology    : 102
% 2.92/1.41  #SimpNegUnit  : 4
% 2.92/1.41  #BackRed      : 2
% 2.92/1.41  
% 2.92/1.41  #Partial instantiations: 0
% 2.92/1.41  #Strategies tried      : 1
% 2.92/1.41  
% 2.92/1.41  Timing (in seconds)
% 2.92/1.41  ----------------------
% 2.92/1.42  Preprocessing        : 0.34
% 2.92/1.42  Parsing              : 0.17
% 2.92/1.42  CNF conversion       : 0.02
% 2.92/1.42  Main loop            : 0.29
% 2.92/1.42  Inferencing          : 0.11
% 2.92/1.42  Reduction            : 0.10
% 2.92/1.42  Demodulation         : 0.07
% 2.92/1.42  BG Simplification    : 0.02
% 2.92/1.42  Subsumption          : 0.05
% 2.92/1.42  Abstraction          : 0.02
% 2.92/1.42  MUC search           : 0.00
% 2.92/1.42  Cooper               : 0.00
% 2.92/1.42  Total                : 0.66
% 2.92/1.42  Index Insertion      : 0.00
% 2.92/1.42  Index Deletion       : 0.00
% 2.92/1.42  Index Matching       : 0.00
% 2.92/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
