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
% DateTime   : Thu Dec  3 09:52:36 EST 2020

% Result     : Theorem 7.27s
% Output     : CNFRefutation 7.42s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 106 expanded)
%              Number of leaves         :   38 (  51 expanded)
%              Depth                    :    7
%              Number of atoms          :   97 ( 135 expanded)
%              Number of equality atoms :   41 (  61 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_4 > #skF_7 > #skF_3 > #skF_10 > #skF_2 > #skF_6 > #skF_9 > #skF_8 > #skF_5

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i > $i )).

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_107,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(A,k1_tarski(B)) = A
      <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_101,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_59,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_51,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_71,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_73,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_90,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_92,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_88,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(c_76,plain,
    ( ~ r2_hidden('#skF_8','#skF_7')
    | r2_hidden('#skF_10','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_93,plain,(
    ~ r2_hidden('#skF_8','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_76])).

tff(c_72,plain,(
    ! [A_43,B_44] :
      ( r1_xboole_0(k1_tarski(A_43),B_44)
      | r2_hidden(A_43,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_26,plain,(
    ! [A_14] :
      ( r2_hidden('#skF_4'(A_14),A_14)
      | k1_xboole_0 = A_14 ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_229,plain,(
    ! [A_79,B_80,C_81] :
      ( ~ r1_xboole_0(A_79,B_80)
      | ~ r2_hidden(C_81,k3_xboole_0(A_79,B_80)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_2193,plain,(
    ! [A_242,B_243,C_244] :
      ( ~ r1_xboole_0(A_242,B_243)
      | ~ r2_hidden(C_244,k3_xboole_0(B_243,A_242)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_229])).

tff(c_2231,plain,(
    ! [A_247,B_248] :
      ( ~ r1_xboole_0(A_247,B_248)
      | k3_xboole_0(B_248,A_247) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_26,c_2193])).

tff(c_2245,plain,(
    ! [B_44,A_43] :
      ( k3_xboole_0(B_44,k1_tarski(A_43)) = k1_xboole_0
      | r2_hidden(A_43,B_44) ) ),
    inference(resolution,[status(thm)],[c_72,c_2231])).

tff(c_36,plain,(
    ! [A_22,B_23] : r1_tarski(k4_xboole_0(A_22,B_23),A_22) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_129,plain,(
    ! [A_60,B_61] :
      ( k3_xboole_0(A_60,B_61) = A_60
      | ~ r1_tarski(A_60,B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_2421,plain,(
    ! [A_264,B_265] : k3_xboole_0(k4_xboole_0(A_264,B_265),A_264) = k4_xboole_0(A_264,B_265) ),
    inference(resolution,[status(thm)],[c_36,c_129])).

tff(c_2490,plain,(
    ! [B_2,B_265] : k3_xboole_0(B_2,k4_xboole_0(B_2,B_265)) = k4_xboole_0(B_2,B_265) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_2421])).

tff(c_38,plain,(
    ! [A_24,B_25] : k4_xboole_0(A_24,k4_xboole_0(A_24,B_25)) = k3_xboole_0(A_24,B_25) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_164,plain,(
    ! [A_71,B_72] :
      ( r1_tarski(A_71,B_72)
      | k4_xboole_0(A_71,B_72) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_34,plain,(
    ! [A_20,B_21] :
      ( k3_xboole_0(A_20,B_21) = A_20
      | ~ r1_tarski(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_2286,plain,(
    ! [A_257,B_258] :
      ( k3_xboole_0(A_257,B_258) = A_257
      | k4_xboole_0(A_257,B_258) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_164,c_34])).

tff(c_2298,plain,(
    ! [A_24,B_25] :
      ( k3_xboole_0(A_24,k4_xboole_0(A_24,B_25)) = A_24
      | k3_xboole_0(A_24,B_25) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_2286])).

tff(c_10231,plain,(
    ! [A_470,B_471] :
      ( k4_xboole_0(A_470,B_471) = A_470
      | k3_xboole_0(A_470,B_471) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2490,c_2298])).

tff(c_74,plain,
    ( k4_xboole_0('#skF_7',k1_tarski('#skF_8')) != '#skF_7'
    | r2_hidden('#skF_10','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_178,plain,(
    k4_xboole_0('#skF_7',k1_tarski('#skF_8')) != '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_74])).

tff(c_10393,plain,(
    k3_xboole_0('#skF_7',k1_tarski('#skF_8')) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_10231,c_178])).

tff(c_10411,plain,(
    r2_hidden('#skF_8','#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_2245,c_10393])).

tff(c_10415,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_93,c_10411])).

tff(c_10416,plain,(
    r2_hidden('#skF_10','#skF_9') ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_64,plain,(
    ! [A_33] : k2_tarski(A_33,A_33) = k1_tarski(A_33) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_134,plain,(
    ! [A_62,B_63] : k1_enumset1(A_62,A_62,B_63) = k2_tarski(A_62,B_63) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_42,plain,(
    ! [E_32,A_26,B_27] : r2_hidden(E_32,k1_enumset1(A_26,B_27,E_32)) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_152,plain,(
    ! [B_64,A_65] : r2_hidden(B_64,k2_tarski(A_65,B_64)) ),
    inference(superposition,[status(thm),theory(equality)],[c_134,c_42])).

tff(c_155,plain,(
    ! [A_33] : r2_hidden(A_33,k1_tarski(A_33)) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_152])).

tff(c_10417,plain,(
    k4_xboole_0('#skF_7',k1_tarski('#skF_8')) = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_78,plain,
    ( k4_xboole_0('#skF_7',k1_tarski('#skF_8')) != '#skF_7'
    | k4_xboole_0('#skF_9',k1_tarski('#skF_10')) = '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_10476,plain,(
    k4_xboole_0('#skF_9',k1_tarski('#skF_10')) = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10417,c_78])).

tff(c_10625,plain,(
    ! [D_478,B_479,A_480] :
      ( ~ r2_hidden(D_478,B_479)
      | ~ r2_hidden(D_478,k4_xboole_0(A_480,B_479)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_10658,plain,(
    ! [D_481] :
      ( ~ r2_hidden(D_481,k1_tarski('#skF_10'))
      | ~ r2_hidden(D_481,'#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10476,c_10625])).

tff(c_10662,plain,(
    ~ r2_hidden('#skF_10','#skF_9') ),
    inference(resolution,[status(thm)],[c_155,c_10658])).

tff(c_10670,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10416,c_10662])).

tff(c_10671,plain,(
    r2_hidden('#skF_10','#skF_9') ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_10771,plain,(
    ! [A_496,B_497] : k1_enumset1(A_496,A_496,B_497) = k2_tarski(A_496,B_497) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_44,plain,(
    ! [E_32,A_26,C_28] : r2_hidden(E_32,k1_enumset1(A_26,E_32,C_28)) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_10851,plain,(
    ! [A_501,B_502] : r2_hidden(A_501,k2_tarski(A_501,B_502)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10771,c_44])).

tff(c_10854,plain,(
    ! [A_33] : r2_hidden(A_33,k1_tarski(A_33)) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_10851])).

tff(c_10672,plain,(
    r2_hidden('#skF_8','#skF_7') ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_80,plain,
    ( ~ r2_hidden('#skF_8','#skF_7')
    | k4_xboole_0('#skF_9',k1_tarski('#skF_10')) = '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_10729,plain,(
    k4_xboole_0('#skF_9',k1_tarski('#skF_10')) = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10672,c_80])).

tff(c_10833,plain,(
    ! [D_498,B_499,A_500] :
      ( ~ r2_hidden(D_498,B_499)
      | ~ r2_hidden(D_498,k4_xboole_0(A_500,B_499)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_11135,plain,(
    ! [D_521] :
      ( ~ r2_hidden(D_521,k1_tarski('#skF_10'))
      | ~ r2_hidden(D_521,'#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10729,c_10833])).

tff(c_11139,plain,(
    ~ r2_hidden('#skF_10','#skF_9') ),
    inference(resolution,[status(thm)],[c_10854,c_11135])).

tff(c_11147,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10671,c_11139])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:46:41 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.27/2.58  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.27/2.58  
% 7.27/2.58  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.27/2.59  %$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_4 > #skF_7 > #skF_3 > #skF_10 > #skF_2 > #skF_6 > #skF_9 > #skF_8 > #skF_5
% 7.27/2.59  
% 7.27/2.59  %Foreground sorts:
% 7.27/2.59  
% 7.27/2.59  
% 7.27/2.59  %Background operators:
% 7.27/2.59  
% 7.27/2.59  
% 7.27/2.59  %Foreground operators:
% 7.27/2.59  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 7.27/2.59  tff('#skF_4', type, '#skF_4': $i > $i).
% 7.27/2.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.27/2.59  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.27/2.59  tff(k1_tarski, type, k1_tarski: $i > $i).
% 7.27/2.59  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.27/2.59  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.27/2.59  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 7.27/2.59  tff('#skF_7', type, '#skF_7': $i).
% 7.27/2.59  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 7.27/2.59  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 7.27/2.59  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.27/2.59  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 7.27/2.59  tff('#skF_10', type, '#skF_10': $i).
% 7.27/2.59  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.27/2.59  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 7.27/2.59  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 7.27/2.59  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 7.27/2.59  tff('#skF_6', type, '#skF_6': ($i * $i * $i * $i) > $i).
% 7.27/2.59  tff('#skF_9', type, '#skF_9': $i).
% 7.27/2.59  tff('#skF_8', type, '#skF_8': $i).
% 7.27/2.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.27/2.59  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i) > $i).
% 7.27/2.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.27/2.59  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.27/2.59  
% 7.42/2.60  tff(f_107, negated_conjecture, ~(![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 7.42/2.60  tff(f_101, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 7.42/2.60  tff(f_59, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 7.42/2.60  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 7.42/2.60  tff(f_51, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 7.42/2.60  tff(f_71, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 7.42/2.60  tff(f_69, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 7.42/2.60  tff(f_73, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 7.42/2.60  tff(f_63, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 7.42/2.60  tff(f_90, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 7.42/2.60  tff(f_92, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 7.42/2.60  tff(f_88, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 7.42/2.60  tff(f_37, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 7.42/2.60  tff(c_76, plain, (~r2_hidden('#skF_8', '#skF_7') | r2_hidden('#skF_10', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_107])).
% 7.42/2.60  tff(c_93, plain, (~r2_hidden('#skF_8', '#skF_7')), inference(splitLeft, [status(thm)], [c_76])).
% 7.42/2.60  tff(c_72, plain, (![A_43, B_44]: (r1_xboole_0(k1_tarski(A_43), B_44) | r2_hidden(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_101])).
% 7.42/2.60  tff(c_26, plain, (![A_14]: (r2_hidden('#skF_4'(A_14), A_14) | k1_xboole_0=A_14)), inference(cnfTransformation, [status(thm)], [f_59])).
% 7.42/2.60  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 7.42/2.60  tff(c_229, plain, (![A_79, B_80, C_81]: (~r1_xboole_0(A_79, B_80) | ~r2_hidden(C_81, k3_xboole_0(A_79, B_80)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 7.42/2.60  tff(c_2193, plain, (![A_242, B_243, C_244]: (~r1_xboole_0(A_242, B_243) | ~r2_hidden(C_244, k3_xboole_0(B_243, A_242)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_229])).
% 7.42/2.60  tff(c_2231, plain, (![A_247, B_248]: (~r1_xboole_0(A_247, B_248) | k3_xboole_0(B_248, A_247)=k1_xboole_0)), inference(resolution, [status(thm)], [c_26, c_2193])).
% 7.42/2.60  tff(c_2245, plain, (![B_44, A_43]: (k3_xboole_0(B_44, k1_tarski(A_43))=k1_xboole_0 | r2_hidden(A_43, B_44))), inference(resolution, [status(thm)], [c_72, c_2231])).
% 7.42/2.60  tff(c_36, plain, (![A_22, B_23]: (r1_tarski(k4_xboole_0(A_22, B_23), A_22))), inference(cnfTransformation, [status(thm)], [f_71])).
% 7.42/2.60  tff(c_129, plain, (![A_60, B_61]: (k3_xboole_0(A_60, B_61)=A_60 | ~r1_tarski(A_60, B_61))), inference(cnfTransformation, [status(thm)], [f_69])).
% 7.42/2.60  tff(c_2421, plain, (![A_264, B_265]: (k3_xboole_0(k4_xboole_0(A_264, B_265), A_264)=k4_xboole_0(A_264, B_265))), inference(resolution, [status(thm)], [c_36, c_129])).
% 7.42/2.60  tff(c_2490, plain, (![B_2, B_265]: (k3_xboole_0(B_2, k4_xboole_0(B_2, B_265))=k4_xboole_0(B_2, B_265))), inference(superposition, [status(thm), theory('equality')], [c_2, c_2421])).
% 7.42/2.60  tff(c_38, plain, (![A_24, B_25]: (k4_xboole_0(A_24, k4_xboole_0(A_24, B_25))=k3_xboole_0(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_73])).
% 7.42/2.60  tff(c_164, plain, (![A_71, B_72]: (r1_tarski(A_71, B_72) | k4_xboole_0(A_71, B_72)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_63])).
% 7.42/2.60  tff(c_34, plain, (![A_20, B_21]: (k3_xboole_0(A_20, B_21)=A_20 | ~r1_tarski(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_69])).
% 7.42/2.60  tff(c_2286, plain, (![A_257, B_258]: (k3_xboole_0(A_257, B_258)=A_257 | k4_xboole_0(A_257, B_258)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_164, c_34])).
% 7.42/2.60  tff(c_2298, plain, (![A_24, B_25]: (k3_xboole_0(A_24, k4_xboole_0(A_24, B_25))=A_24 | k3_xboole_0(A_24, B_25)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_38, c_2286])).
% 7.42/2.60  tff(c_10231, plain, (![A_470, B_471]: (k4_xboole_0(A_470, B_471)=A_470 | k3_xboole_0(A_470, B_471)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2490, c_2298])).
% 7.42/2.60  tff(c_74, plain, (k4_xboole_0('#skF_7', k1_tarski('#skF_8'))!='#skF_7' | r2_hidden('#skF_10', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_107])).
% 7.42/2.60  tff(c_178, plain, (k4_xboole_0('#skF_7', k1_tarski('#skF_8'))!='#skF_7'), inference(splitLeft, [status(thm)], [c_74])).
% 7.42/2.60  tff(c_10393, plain, (k3_xboole_0('#skF_7', k1_tarski('#skF_8'))!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_10231, c_178])).
% 7.42/2.60  tff(c_10411, plain, (r2_hidden('#skF_8', '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_2245, c_10393])).
% 7.42/2.60  tff(c_10415, plain, $false, inference(negUnitSimplification, [status(thm)], [c_93, c_10411])).
% 7.42/2.60  tff(c_10416, plain, (r2_hidden('#skF_10', '#skF_9')), inference(splitRight, [status(thm)], [c_74])).
% 7.42/2.60  tff(c_64, plain, (![A_33]: (k2_tarski(A_33, A_33)=k1_tarski(A_33))), inference(cnfTransformation, [status(thm)], [f_90])).
% 7.42/2.60  tff(c_134, plain, (![A_62, B_63]: (k1_enumset1(A_62, A_62, B_63)=k2_tarski(A_62, B_63))), inference(cnfTransformation, [status(thm)], [f_92])).
% 7.42/2.60  tff(c_42, plain, (![E_32, A_26, B_27]: (r2_hidden(E_32, k1_enumset1(A_26, B_27, E_32)))), inference(cnfTransformation, [status(thm)], [f_88])).
% 7.42/2.60  tff(c_152, plain, (![B_64, A_65]: (r2_hidden(B_64, k2_tarski(A_65, B_64)))), inference(superposition, [status(thm), theory('equality')], [c_134, c_42])).
% 7.42/2.60  tff(c_155, plain, (![A_33]: (r2_hidden(A_33, k1_tarski(A_33)))), inference(superposition, [status(thm), theory('equality')], [c_64, c_152])).
% 7.42/2.60  tff(c_10417, plain, (k4_xboole_0('#skF_7', k1_tarski('#skF_8'))='#skF_7'), inference(splitRight, [status(thm)], [c_74])).
% 7.42/2.60  tff(c_78, plain, (k4_xboole_0('#skF_7', k1_tarski('#skF_8'))!='#skF_7' | k4_xboole_0('#skF_9', k1_tarski('#skF_10'))='#skF_9'), inference(cnfTransformation, [status(thm)], [f_107])).
% 7.42/2.60  tff(c_10476, plain, (k4_xboole_0('#skF_9', k1_tarski('#skF_10'))='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_10417, c_78])).
% 7.42/2.60  tff(c_10625, plain, (![D_478, B_479, A_480]: (~r2_hidden(D_478, B_479) | ~r2_hidden(D_478, k4_xboole_0(A_480, B_479)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.42/2.60  tff(c_10658, plain, (![D_481]: (~r2_hidden(D_481, k1_tarski('#skF_10')) | ~r2_hidden(D_481, '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_10476, c_10625])).
% 7.42/2.60  tff(c_10662, plain, (~r2_hidden('#skF_10', '#skF_9')), inference(resolution, [status(thm)], [c_155, c_10658])).
% 7.42/2.60  tff(c_10670, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10416, c_10662])).
% 7.42/2.60  tff(c_10671, plain, (r2_hidden('#skF_10', '#skF_9')), inference(splitRight, [status(thm)], [c_76])).
% 7.42/2.60  tff(c_10771, plain, (![A_496, B_497]: (k1_enumset1(A_496, A_496, B_497)=k2_tarski(A_496, B_497))), inference(cnfTransformation, [status(thm)], [f_92])).
% 7.42/2.60  tff(c_44, plain, (![E_32, A_26, C_28]: (r2_hidden(E_32, k1_enumset1(A_26, E_32, C_28)))), inference(cnfTransformation, [status(thm)], [f_88])).
% 7.42/2.60  tff(c_10851, plain, (![A_501, B_502]: (r2_hidden(A_501, k2_tarski(A_501, B_502)))), inference(superposition, [status(thm), theory('equality')], [c_10771, c_44])).
% 7.42/2.60  tff(c_10854, plain, (![A_33]: (r2_hidden(A_33, k1_tarski(A_33)))), inference(superposition, [status(thm), theory('equality')], [c_64, c_10851])).
% 7.42/2.60  tff(c_10672, plain, (r2_hidden('#skF_8', '#skF_7')), inference(splitRight, [status(thm)], [c_76])).
% 7.42/2.60  tff(c_80, plain, (~r2_hidden('#skF_8', '#skF_7') | k4_xboole_0('#skF_9', k1_tarski('#skF_10'))='#skF_9'), inference(cnfTransformation, [status(thm)], [f_107])).
% 7.42/2.60  tff(c_10729, plain, (k4_xboole_0('#skF_9', k1_tarski('#skF_10'))='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_10672, c_80])).
% 7.42/2.60  tff(c_10833, plain, (![D_498, B_499, A_500]: (~r2_hidden(D_498, B_499) | ~r2_hidden(D_498, k4_xboole_0(A_500, B_499)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.42/2.60  tff(c_11135, plain, (![D_521]: (~r2_hidden(D_521, k1_tarski('#skF_10')) | ~r2_hidden(D_521, '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_10729, c_10833])).
% 7.42/2.60  tff(c_11139, plain, (~r2_hidden('#skF_10', '#skF_9')), inference(resolution, [status(thm)], [c_10854, c_11135])).
% 7.42/2.60  tff(c_11147, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10671, c_11139])).
% 7.42/2.60  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.42/2.60  
% 7.42/2.60  Inference rules
% 7.42/2.60  ----------------------
% 7.42/2.60  #Ref     : 0
% 7.42/2.60  #Sup     : 2754
% 7.42/2.60  #Fact    : 0
% 7.42/2.60  #Define  : 0
% 7.42/2.60  #Split   : 3
% 7.42/2.60  #Chain   : 0
% 7.42/2.60  #Close   : 0
% 7.42/2.60  
% 7.42/2.60  Ordering : KBO
% 7.42/2.60  
% 7.42/2.60  Simplification rules
% 7.42/2.60  ----------------------
% 7.42/2.60  #Subsume      : 514
% 7.42/2.60  #Demod        : 1883
% 7.42/2.60  #Tautology    : 1361
% 7.42/2.60  #SimpNegUnit  : 59
% 7.42/2.60  #BackRed      : 3
% 7.42/2.60  
% 7.42/2.60  #Partial instantiations: 0
% 7.42/2.60  #Strategies tried      : 1
% 7.42/2.60  
% 7.42/2.60  Timing (in seconds)
% 7.42/2.60  ----------------------
% 7.42/2.61  Preprocessing        : 0.33
% 7.42/2.61  Parsing              : 0.17
% 7.42/2.61  CNF conversion       : 0.03
% 7.42/2.61  Main loop            : 1.50
% 7.42/2.61  Inferencing          : 0.46
% 7.42/2.61  Reduction            : 0.60
% 7.42/2.61  Demodulation         : 0.48
% 7.42/2.61  BG Simplification    : 0.05
% 7.42/2.61  Subsumption          : 0.28
% 7.42/2.61  Abstraction          : 0.07
% 7.42/2.61  MUC search           : 0.00
% 7.42/2.61  Cooper               : 0.00
% 7.42/2.61  Total                : 1.86
% 7.42/2.61  Index Insertion      : 0.00
% 7.42/2.61  Index Deletion       : 0.00
% 7.42/2.61  Index Matching       : 0.00
% 7.42/2.61  BG Taut test         : 0.00
%------------------------------------------------------------------------------
