%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:34 EST 2020

% Result     : Theorem 4.45s
% Output     : CNFRefutation 4.45s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 353 expanded)
%              Number of leaves         :   37 ( 131 expanded)
%              Depth                    :   14
%              Number of atoms          :  119 ( 741 expanded)
%              Number of equality atoms :   66 ( 534 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_7 > #skF_5 > #skF_6 > #skF_4 > #skF_8 > #skF_3 > #skF_1

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

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

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

tff(f_90,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_84,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_125,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ~ ( r1_tarski(k2_tarski(A,B),k2_tarski(C,D))
          & A != C
          & A != D ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_zfmisc_1)).

tff(f_88,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_67,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_115,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_tarski(B,C))
    <=> ~ ( A != k1_xboole_0
          & A != k1_tarski(B)
          & A != k1_tarski(C)
          & A != k2_tarski(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l45_zfmisc_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(c_221,plain,(
    ! [A_98,B_99] : k1_enumset1(A_98,A_98,B_99) = k2_tarski(A_98,B_99) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_28,plain,(
    ! [E_31,A_25,B_26] : r2_hidden(E_31,k1_enumset1(A_25,B_26,E_31)) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_233,plain,(
    ! [B_99,A_98] : r2_hidden(B_99,k2_tarski(A_98,B_99)) ),
    inference(superposition,[status(thm),theory(equality)],[c_221,c_28])).

tff(c_76,plain,(
    '#skF_5' != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_52,plain,(
    ! [A_36] : k2_tarski(A_36,A_36) = k1_tarski(A_36) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_78,plain,(
    '#skF_7' != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_22,plain,(
    ! [A_22] : r1_xboole_0(A_22,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_4,plain,(
    ! [A_3] : k3_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_375,plain,(
    ! [A_116,B_117,C_118] :
      ( ~ r1_xboole_0(A_116,B_117)
      | ~ r2_hidden(C_118,k3_xboole_0(A_116,B_117)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_399,plain,(
    ! [A_119,C_120] :
      ( ~ r1_xboole_0(A_119,A_119)
      | ~ r2_hidden(C_120,A_119) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_375])).

tff(c_403,plain,(
    ! [C_120] : ~ r2_hidden(C_120,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_22,c_399])).

tff(c_80,plain,(
    r1_tarski(k2_tarski('#skF_5','#skF_6'),k2_tarski('#skF_7','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_1981,plain,(
    ! [B_253,C_254,A_255] :
      ( k2_tarski(B_253,C_254) = A_255
      | k1_tarski(C_254) = A_255
      | k1_tarski(B_253) = A_255
      | k1_xboole_0 = A_255
      | ~ r1_tarski(A_255,k2_tarski(B_253,C_254)) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_2018,plain,
    ( k2_tarski('#skF_7','#skF_8') = k2_tarski('#skF_5','#skF_6')
    | k2_tarski('#skF_5','#skF_6') = k1_tarski('#skF_8')
    | k2_tarski('#skF_5','#skF_6') = k1_tarski('#skF_7')
    | k2_tarski('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_80,c_1981])).

tff(c_2022,plain,(
    k2_tarski('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_2018])).

tff(c_160,plain,(
    ! [A_91,B_92] :
      ( k3_xboole_0(A_91,B_92) = A_91
      | ~ r1_tarski(A_91,B_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_183,plain,(
    k3_xboole_0(k2_tarski('#skF_5','#skF_6'),k2_tarski('#skF_7','#skF_8')) = k2_tarski('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_80,c_160])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_872,plain,(
    ! [A_151,B_152,C_153] :
      ( ~ r1_xboole_0(A_151,B_152)
      | ~ r2_hidden(C_153,k3_xboole_0(B_152,A_151)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_375])).

tff(c_888,plain,(
    ! [C_153] :
      ( ~ r1_xboole_0(k2_tarski('#skF_7','#skF_8'),k2_tarski('#skF_5','#skF_6'))
      | ~ r2_hidden(C_153,k2_tarski('#skF_5','#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_183,c_872])).

tff(c_1165,plain,(
    ~ r1_xboole_0(k2_tarski('#skF_7','#skF_8'),k2_tarski('#skF_5','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_888])).

tff(c_702,plain,(
    ! [A_138,B_139] :
      ( r2_hidden('#skF_1'(A_138,B_139),k3_xboole_0(A_138,B_139))
      | r1_xboole_0(A_138,B_139) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1245,plain,(
    ! [B_190,A_191] :
      ( r2_hidden('#skF_1'(B_190,A_191),k3_xboole_0(A_191,B_190))
      | r1_xboole_0(B_190,A_191) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_702])).

tff(c_1266,plain,
    ( r2_hidden('#skF_1'(k2_tarski('#skF_7','#skF_8'),k2_tarski('#skF_5','#skF_6')),k2_tarski('#skF_5','#skF_6'))
    | r1_xboole_0(k2_tarski('#skF_7','#skF_8'),k2_tarski('#skF_5','#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_183,c_1245])).

tff(c_1282,plain,(
    r2_hidden('#skF_1'(k2_tarski('#skF_7','#skF_8'),k2_tarski('#skF_5','#skF_6')),k2_tarski('#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_1165,c_1266])).

tff(c_2024,plain,(
    r2_hidden('#skF_1'(k2_tarski('#skF_7','#skF_8'),k1_xboole_0),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2022,c_2022,c_1282])).

tff(c_2035,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_403,c_2024])).

tff(c_2036,plain,
    ( k2_tarski('#skF_5','#skF_6') = k1_tarski('#skF_7')
    | k2_tarski('#skF_5','#skF_6') = k1_tarski('#skF_8')
    | k2_tarski('#skF_7','#skF_8') = k2_tarski('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_2018])).

tff(c_2109,plain,(
    k2_tarski('#skF_7','#skF_8') = k2_tarski('#skF_5','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_2036])).

tff(c_2174,plain,(
    r2_hidden('#skF_8',k2_tarski('#skF_5','#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2109,c_233])).

tff(c_54,plain,(
    ! [A_37,B_38] : k1_enumset1(A_37,A_37,B_38) = k2_tarski(A_37,B_38) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_1107,plain,(
    ! [E_174,C_175,B_176,A_177] :
      ( E_174 = C_175
      | E_174 = B_176
      | E_174 = A_177
      | ~ r2_hidden(E_174,k1_enumset1(A_177,B_176,C_175)) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_1114,plain,(
    ! [E_174,B_38,A_37] :
      ( E_174 = B_38
      | E_174 = A_37
      | E_174 = A_37
      | ~ r2_hidden(E_174,k2_tarski(A_37,B_38)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_1107])).

tff(c_2204,plain,
    ( '#skF_6' = '#skF_8'
    | '#skF_5' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_2174,c_1114])).

tff(c_2207,plain,(
    '#skF_6' = '#skF_8' ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_76,c_2204])).

tff(c_32,plain,(
    ! [E_31,B_26,C_27] : r2_hidden(E_31,k1_enumset1(E_31,B_26,C_27)) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_227,plain,(
    ! [A_98,B_99] : r2_hidden(A_98,k2_tarski(A_98,B_99)) ),
    inference(superposition,[status(thm),theory(equality)],[c_221,c_32])).

tff(c_2177,plain,(
    r2_hidden('#skF_7',k2_tarski('#skF_5','#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2109,c_227])).

tff(c_2216,plain,(
    r2_hidden('#skF_7',k2_tarski('#skF_5','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2207,c_2177])).

tff(c_2219,plain,
    ( '#skF_7' = '#skF_8'
    | '#skF_7' = '#skF_5' ),
    inference(resolution,[status(thm)],[c_2216,c_1114])).

tff(c_2222,plain,(
    '#skF_7' = '#skF_8' ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_78,c_2219])).

tff(c_2209,plain,(
    k2_tarski('#skF_7','#skF_8') = k2_tarski('#skF_5','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2207,c_2109])).

tff(c_2267,plain,(
    k2_tarski('#skF_5','#skF_8') = k1_tarski('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_2222,c_2209])).

tff(c_2320,plain,(
    r2_hidden('#skF_5',k1_tarski('#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2267,c_227])).

tff(c_2042,plain,(
    ! [E_256,B_257,A_258] :
      ( E_256 = B_257
      | E_256 = A_258
      | E_256 = A_258
      | ~ r2_hidden(E_256,k2_tarski(A_258,B_257)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_1107])).

tff(c_2065,plain,(
    ! [E_256,A_36] :
      ( E_256 = A_36
      | E_256 = A_36
      | E_256 = A_36
      | ~ r2_hidden(E_256,k1_tarski(A_36)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_2042])).

tff(c_2351,plain,(
    '#skF_5' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_2320,c_2065])).

tff(c_2355,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_76,c_76,c_2351])).

tff(c_2356,plain,
    ( k2_tarski('#skF_5','#skF_6') = k1_tarski('#skF_8')
    | k2_tarski('#skF_5','#skF_6') = k1_tarski('#skF_7') ),
    inference(splitRight,[status(thm)],[c_2036])).

tff(c_2358,plain,(
    k2_tarski('#skF_5','#skF_6') = k1_tarski('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_2356])).

tff(c_2424,plain,(
    r2_hidden('#skF_6',k1_tarski('#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2358,c_233])).

tff(c_2455,plain,(
    '#skF_7' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_2424,c_2065])).

tff(c_2460,plain,(
    '#skF_5' != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2455,c_78])).

tff(c_2427,plain,(
    r2_hidden('#skF_5',k1_tarski('#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2358,c_227])).

tff(c_2466,plain,(
    r2_hidden('#skF_5',k1_tarski('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2455,c_2427])).

tff(c_2469,plain,(
    '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_2466,c_2065])).

tff(c_2473,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2460,c_2460,c_2460,c_2469])).

tff(c_2474,plain,(
    k2_tarski('#skF_5','#skF_6') = k1_tarski('#skF_8') ),
    inference(splitRight,[status(thm)],[c_2356])).

tff(c_2545,plain,(
    r2_hidden('#skF_5',k1_tarski('#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2474,c_227])).

tff(c_2584,plain,(
    '#skF_5' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_2545,c_2065])).

tff(c_2588,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_76,c_76,c_2584])).

tff(c_2591,plain,(
    ! [C_281] : ~ r2_hidden(C_281,k2_tarski('#skF_5','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_888])).

tff(c_2608,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_233,c_2591])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 16:30:14 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.45/1.82  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.45/1.83  
% 4.45/1.83  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.45/1.83  %$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_7 > #skF_5 > #skF_6 > #skF_4 > #skF_8 > #skF_3 > #skF_1
% 4.45/1.83  
% 4.45/1.83  %Foreground sorts:
% 4.45/1.83  
% 4.45/1.83  
% 4.45/1.83  %Background operators:
% 4.45/1.83  
% 4.45/1.83  
% 4.45/1.83  %Foreground operators:
% 4.45/1.83  tff('#skF_2', type, '#skF_2': $i > $i).
% 4.45/1.83  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.45/1.83  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.45/1.83  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.45/1.83  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.45/1.83  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.45/1.83  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.45/1.83  tff('#skF_7', type, '#skF_7': $i).
% 4.45/1.83  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.45/1.83  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.45/1.83  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.45/1.83  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.45/1.83  tff('#skF_5', type, '#skF_5': $i).
% 4.45/1.83  tff('#skF_6', type, '#skF_6': $i).
% 4.45/1.83  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.45/1.83  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.45/1.83  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.45/1.83  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 4.45/1.83  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 4.45/1.83  tff('#skF_8', type, '#skF_8': $i).
% 4.45/1.83  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.45/1.83  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.45/1.83  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.45/1.83  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 4.45/1.83  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.45/1.83  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 4.45/1.83  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.45/1.83  
% 4.45/1.85  tff(f_90, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 4.45/1.85  tff(f_84, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 4.45/1.85  tff(f_125, negated_conjecture, ~(![A, B, C, D]: ~((r1_tarski(k2_tarski(A, B), k2_tarski(C, D)) & ~(A = C)) & ~(A = D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_zfmisc_1)).
% 4.45/1.85  tff(f_88, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 4.45/1.85  tff(f_67, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 4.45/1.85  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 4.45/1.85  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 4.45/1.85  tff(f_115, axiom, (![A, B, C]: (r1_tarski(A, k2_tarski(B, C)) <=> ~(((~(A = k1_xboole_0) & ~(A = k1_tarski(B))) & ~(A = k1_tarski(C))) & ~(A = k2_tarski(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l45_zfmisc_1)).
% 4.45/1.85  tff(f_61, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 4.45/1.85  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 4.45/1.85  tff(c_221, plain, (![A_98, B_99]: (k1_enumset1(A_98, A_98, B_99)=k2_tarski(A_98, B_99))), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.45/1.85  tff(c_28, plain, (![E_31, A_25, B_26]: (r2_hidden(E_31, k1_enumset1(A_25, B_26, E_31)))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.45/1.85  tff(c_233, plain, (![B_99, A_98]: (r2_hidden(B_99, k2_tarski(A_98, B_99)))), inference(superposition, [status(thm), theory('equality')], [c_221, c_28])).
% 4.45/1.85  tff(c_76, plain, ('#skF_5'!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_125])).
% 4.45/1.85  tff(c_52, plain, (![A_36]: (k2_tarski(A_36, A_36)=k1_tarski(A_36))), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.45/1.85  tff(c_78, plain, ('#skF_7'!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_125])).
% 4.45/1.85  tff(c_22, plain, (![A_22]: (r1_xboole_0(A_22, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.45/1.85  tff(c_4, plain, (![A_3]: (k3_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.45/1.85  tff(c_375, plain, (![A_116, B_117, C_118]: (~r1_xboole_0(A_116, B_117) | ~r2_hidden(C_118, k3_xboole_0(A_116, B_117)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.45/1.85  tff(c_399, plain, (![A_119, C_120]: (~r1_xboole_0(A_119, A_119) | ~r2_hidden(C_120, A_119))), inference(superposition, [status(thm), theory('equality')], [c_4, c_375])).
% 4.45/1.85  tff(c_403, plain, (![C_120]: (~r2_hidden(C_120, k1_xboole_0))), inference(resolution, [status(thm)], [c_22, c_399])).
% 4.45/1.85  tff(c_80, plain, (r1_tarski(k2_tarski('#skF_5', '#skF_6'), k2_tarski('#skF_7', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_125])).
% 4.45/1.85  tff(c_1981, plain, (![B_253, C_254, A_255]: (k2_tarski(B_253, C_254)=A_255 | k1_tarski(C_254)=A_255 | k1_tarski(B_253)=A_255 | k1_xboole_0=A_255 | ~r1_tarski(A_255, k2_tarski(B_253, C_254)))), inference(cnfTransformation, [status(thm)], [f_115])).
% 4.45/1.85  tff(c_2018, plain, (k2_tarski('#skF_7', '#skF_8')=k2_tarski('#skF_5', '#skF_6') | k2_tarski('#skF_5', '#skF_6')=k1_tarski('#skF_8') | k2_tarski('#skF_5', '#skF_6')=k1_tarski('#skF_7') | k2_tarski('#skF_5', '#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_80, c_1981])).
% 4.45/1.85  tff(c_2022, plain, (k2_tarski('#skF_5', '#skF_6')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_2018])).
% 4.45/1.85  tff(c_160, plain, (![A_91, B_92]: (k3_xboole_0(A_91, B_92)=A_91 | ~r1_tarski(A_91, B_92))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.45/1.85  tff(c_183, plain, (k3_xboole_0(k2_tarski('#skF_5', '#skF_6'), k2_tarski('#skF_7', '#skF_8'))=k2_tarski('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_80, c_160])).
% 4.45/1.85  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.45/1.85  tff(c_872, plain, (![A_151, B_152, C_153]: (~r1_xboole_0(A_151, B_152) | ~r2_hidden(C_153, k3_xboole_0(B_152, A_151)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_375])).
% 4.45/1.85  tff(c_888, plain, (![C_153]: (~r1_xboole_0(k2_tarski('#skF_7', '#skF_8'), k2_tarski('#skF_5', '#skF_6')) | ~r2_hidden(C_153, k2_tarski('#skF_5', '#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_183, c_872])).
% 4.45/1.85  tff(c_1165, plain, (~r1_xboole_0(k2_tarski('#skF_7', '#skF_8'), k2_tarski('#skF_5', '#skF_6'))), inference(splitLeft, [status(thm)], [c_888])).
% 4.45/1.85  tff(c_702, plain, (![A_138, B_139]: (r2_hidden('#skF_1'(A_138, B_139), k3_xboole_0(A_138, B_139)) | r1_xboole_0(A_138, B_139))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.45/1.85  tff(c_1245, plain, (![B_190, A_191]: (r2_hidden('#skF_1'(B_190, A_191), k3_xboole_0(A_191, B_190)) | r1_xboole_0(B_190, A_191))), inference(superposition, [status(thm), theory('equality')], [c_2, c_702])).
% 4.45/1.85  tff(c_1266, plain, (r2_hidden('#skF_1'(k2_tarski('#skF_7', '#skF_8'), k2_tarski('#skF_5', '#skF_6')), k2_tarski('#skF_5', '#skF_6')) | r1_xboole_0(k2_tarski('#skF_7', '#skF_8'), k2_tarski('#skF_5', '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_183, c_1245])).
% 4.45/1.85  tff(c_1282, plain, (r2_hidden('#skF_1'(k2_tarski('#skF_7', '#skF_8'), k2_tarski('#skF_5', '#skF_6')), k2_tarski('#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_1165, c_1266])).
% 4.45/1.85  tff(c_2024, plain, (r2_hidden('#skF_1'(k2_tarski('#skF_7', '#skF_8'), k1_xboole_0), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2022, c_2022, c_1282])).
% 4.45/1.85  tff(c_2035, plain, $false, inference(negUnitSimplification, [status(thm)], [c_403, c_2024])).
% 4.45/1.85  tff(c_2036, plain, (k2_tarski('#skF_5', '#skF_6')=k1_tarski('#skF_7') | k2_tarski('#skF_5', '#skF_6')=k1_tarski('#skF_8') | k2_tarski('#skF_7', '#skF_8')=k2_tarski('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_2018])).
% 4.45/1.85  tff(c_2109, plain, (k2_tarski('#skF_7', '#skF_8')=k2_tarski('#skF_5', '#skF_6')), inference(splitLeft, [status(thm)], [c_2036])).
% 4.45/1.85  tff(c_2174, plain, (r2_hidden('#skF_8', k2_tarski('#skF_5', '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_2109, c_233])).
% 4.45/1.85  tff(c_54, plain, (![A_37, B_38]: (k1_enumset1(A_37, A_37, B_38)=k2_tarski(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.45/1.85  tff(c_1107, plain, (![E_174, C_175, B_176, A_177]: (E_174=C_175 | E_174=B_176 | E_174=A_177 | ~r2_hidden(E_174, k1_enumset1(A_177, B_176, C_175)))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.45/1.85  tff(c_1114, plain, (![E_174, B_38, A_37]: (E_174=B_38 | E_174=A_37 | E_174=A_37 | ~r2_hidden(E_174, k2_tarski(A_37, B_38)))), inference(superposition, [status(thm), theory('equality')], [c_54, c_1107])).
% 4.45/1.85  tff(c_2204, plain, ('#skF_6'='#skF_8' | '#skF_5'='#skF_8'), inference(resolution, [status(thm)], [c_2174, c_1114])).
% 4.45/1.85  tff(c_2207, plain, ('#skF_6'='#skF_8'), inference(negUnitSimplification, [status(thm)], [c_76, c_76, c_2204])).
% 4.45/1.85  tff(c_32, plain, (![E_31, B_26, C_27]: (r2_hidden(E_31, k1_enumset1(E_31, B_26, C_27)))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.45/1.85  tff(c_227, plain, (![A_98, B_99]: (r2_hidden(A_98, k2_tarski(A_98, B_99)))), inference(superposition, [status(thm), theory('equality')], [c_221, c_32])).
% 4.45/1.85  tff(c_2177, plain, (r2_hidden('#skF_7', k2_tarski('#skF_5', '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_2109, c_227])).
% 4.45/1.85  tff(c_2216, plain, (r2_hidden('#skF_7', k2_tarski('#skF_5', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_2207, c_2177])).
% 4.45/1.85  tff(c_2219, plain, ('#skF_7'='#skF_8' | '#skF_7'='#skF_5'), inference(resolution, [status(thm)], [c_2216, c_1114])).
% 4.45/1.85  tff(c_2222, plain, ('#skF_7'='#skF_8'), inference(negUnitSimplification, [status(thm)], [c_78, c_78, c_2219])).
% 4.45/1.85  tff(c_2209, plain, (k2_tarski('#skF_7', '#skF_8')=k2_tarski('#skF_5', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_2207, c_2109])).
% 4.45/1.85  tff(c_2267, plain, (k2_tarski('#skF_5', '#skF_8')=k1_tarski('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_2222, c_2209])).
% 4.45/1.85  tff(c_2320, plain, (r2_hidden('#skF_5', k1_tarski('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_2267, c_227])).
% 4.45/1.85  tff(c_2042, plain, (![E_256, B_257, A_258]: (E_256=B_257 | E_256=A_258 | E_256=A_258 | ~r2_hidden(E_256, k2_tarski(A_258, B_257)))), inference(superposition, [status(thm), theory('equality')], [c_54, c_1107])).
% 4.45/1.85  tff(c_2065, plain, (![E_256, A_36]: (E_256=A_36 | E_256=A_36 | E_256=A_36 | ~r2_hidden(E_256, k1_tarski(A_36)))), inference(superposition, [status(thm), theory('equality')], [c_52, c_2042])).
% 4.45/1.85  tff(c_2351, plain, ('#skF_5'='#skF_8'), inference(resolution, [status(thm)], [c_2320, c_2065])).
% 4.45/1.85  tff(c_2355, plain, $false, inference(negUnitSimplification, [status(thm)], [c_76, c_76, c_76, c_2351])).
% 4.45/1.85  tff(c_2356, plain, (k2_tarski('#skF_5', '#skF_6')=k1_tarski('#skF_8') | k2_tarski('#skF_5', '#skF_6')=k1_tarski('#skF_7')), inference(splitRight, [status(thm)], [c_2036])).
% 4.45/1.85  tff(c_2358, plain, (k2_tarski('#skF_5', '#skF_6')=k1_tarski('#skF_7')), inference(splitLeft, [status(thm)], [c_2356])).
% 4.45/1.85  tff(c_2424, plain, (r2_hidden('#skF_6', k1_tarski('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_2358, c_233])).
% 4.45/1.85  tff(c_2455, plain, ('#skF_7'='#skF_6'), inference(resolution, [status(thm)], [c_2424, c_2065])).
% 4.45/1.85  tff(c_2460, plain, ('#skF_5'!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_2455, c_78])).
% 4.45/1.85  tff(c_2427, plain, (r2_hidden('#skF_5', k1_tarski('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_2358, c_227])).
% 4.45/1.85  tff(c_2466, plain, (r2_hidden('#skF_5', k1_tarski('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_2455, c_2427])).
% 4.45/1.85  tff(c_2469, plain, ('#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_2466, c_2065])).
% 4.45/1.85  tff(c_2473, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2460, c_2460, c_2460, c_2469])).
% 4.45/1.85  tff(c_2474, plain, (k2_tarski('#skF_5', '#skF_6')=k1_tarski('#skF_8')), inference(splitRight, [status(thm)], [c_2356])).
% 4.45/1.85  tff(c_2545, plain, (r2_hidden('#skF_5', k1_tarski('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_2474, c_227])).
% 4.45/1.85  tff(c_2584, plain, ('#skF_5'='#skF_8'), inference(resolution, [status(thm)], [c_2545, c_2065])).
% 4.45/1.85  tff(c_2588, plain, $false, inference(negUnitSimplification, [status(thm)], [c_76, c_76, c_76, c_2584])).
% 4.45/1.85  tff(c_2591, plain, (![C_281]: (~r2_hidden(C_281, k2_tarski('#skF_5', '#skF_6')))), inference(splitRight, [status(thm)], [c_888])).
% 4.45/1.85  tff(c_2608, plain, $false, inference(resolution, [status(thm)], [c_233, c_2591])).
% 4.45/1.85  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.45/1.85  
% 4.45/1.85  Inference rules
% 4.45/1.85  ----------------------
% 4.45/1.85  #Ref     : 0
% 4.45/1.85  #Sup     : 613
% 4.45/1.85  #Fact    : 0
% 4.45/1.85  #Define  : 0
% 4.45/1.85  #Split   : 6
% 4.45/1.85  #Chain   : 0
% 4.45/1.85  #Close   : 0
% 4.45/1.85  
% 4.45/1.85  Ordering : KBO
% 4.45/1.85  
% 4.45/1.85  Simplification rules
% 4.45/1.85  ----------------------
% 4.45/1.85  #Subsume      : 78
% 4.45/1.85  #Demod        : 486
% 4.45/1.85  #Tautology    : 348
% 4.45/1.85  #SimpNegUnit  : 12
% 4.45/1.85  #BackRed      : 62
% 4.45/1.85  
% 4.45/1.85  #Partial instantiations: 0
% 4.45/1.85  #Strategies tried      : 1
% 4.45/1.85  
% 4.45/1.85  Timing (in seconds)
% 4.45/1.85  ----------------------
% 4.45/1.85  Preprocessing        : 0.38
% 4.45/1.85  Parsing              : 0.19
% 4.45/1.85  CNF conversion       : 0.03
% 4.45/1.85  Main loop            : 0.70
% 4.45/1.85  Inferencing          : 0.22
% 4.45/1.85  Reduction            : 0.28
% 4.45/1.85  Demodulation         : 0.22
% 4.45/1.85  BG Simplification    : 0.03
% 4.45/1.85  Subsumption          : 0.11
% 4.45/1.85  Abstraction          : 0.03
% 4.45/1.85  MUC search           : 0.00
% 4.45/1.85  Cooper               : 0.00
% 4.45/1.85  Total                : 1.11
% 4.45/1.85  Index Insertion      : 0.00
% 4.45/1.85  Index Deletion       : 0.00
% 4.45/1.85  Index Matching       : 0.00
% 4.45/1.85  BG Taut test         : 0.00
%------------------------------------------------------------------------------
