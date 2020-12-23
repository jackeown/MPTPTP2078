%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:53 EST 2020

% Result     : Theorem 10.18s
% Output     : CNFRefutation 10.18s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 147 expanded)
%              Number of leaves         :   40 (  66 expanded)
%              Depth                    :   10
%              Number of atoms          :   99 ( 177 expanded)
%              Number of equality atoms :   43 (  85 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_4 > #skF_3 > #skF_1

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

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_127,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),B) = k1_tarski(A)
      <=> ~ r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_zfmisc_1)).

tff(f_117,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_75,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_119,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_61,axiom,(
    ! [A,B] : k2_xboole_0(A,k2_xboole_0(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_xboole_1)).

tff(f_57,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_59,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_67,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => k4_xboole_0(k2_xboole_0(A,B),B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_xboole_1)).

tff(f_100,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_102,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_90,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(c_90,plain,
    ( ~ r2_hidden('#skF_4','#skF_5')
    | r2_hidden('#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_174,plain,(
    ~ r2_hidden('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_90])).

tff(c_82,plain,(
    ! [A_92,B_93] :
      ( r1_xboole_0(k1_tarski(A_92),B_93)
      | r2_hidden(A_92,B_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_34,plain,(
    ! [B_33,A_32] : k2_tarski(B_33,A_32) = k2_tarski(A_32,B_33) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_264,plain,(
    ! [A_128,B_129] : k3_tarski(k2_tarski(A_128,B_129)) = k2_xboole_0(A_128,B_129) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_306,plain,(
    ! [A_133,B_134] : k3_tarski(k2_tarski(A_133,B_134)) = k2_xboole_0(B_134,A_133) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_264])).

tff(c_84,plain,(
    ! [A_94,B_95] : k3_tarski(k2_tarski(A_94,B_95)) = k2_xboole_0(A_94,B_95) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_312,plain,(
    ! [B_134,A_133] : k2_xboole_0(B_134,A_133) = k2_xboole_0(A_133,B_134) ),
    inference(superposition,[status(thm),theory(equality)],[c_306,c_84])).

tff(c_436,plain,(
    ! [A_142,B_143] : k2_xboole_0(A_142,k2_xboole_0(A_142,B_143)) = k2_xboole_0(A_142,B_143) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_465,plain,(
    ! [B_134,A_133] : k2_xboole_0(B_134,k2_xboole_0(A_133,B_134)) = k2_xboole_0(B_134,A_133) ),
    inference(superposition,[status(thm),theory(equality)],[c_312,c_436])).

tff(c_18,plain,(
    ! [A_15,B_16] : k2_xboole_0(A_15,k4_xboole_0(B_16,A_15)) = k2_xboole_0(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_20,plain,(
    ! [A_17,B_18,C_19] : k2_xboole_0(k2_xboole_0(A_17,B_18),C_19) = k2_xboole_0(A_17,k2_xboole_0(B_18,C_19)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_24,plain,(
    ! [A_22,B_23] : r1_xboole_0(k4_xboole_0(A_22,B_23),B_23) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_209,plain,(
    ! [B_117,A_118] :
      ( r1_xboole_0(B_117,A_118)
      | ~ r1_xboole_0(A_118,B_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_212,plain,(
    ! [B_23,A_22] : r1_xboole_0(B_23,k4_xboole_0(A_22,B_23)) ),
    inference(resolution,[status(thm)],[c_24,c_209])).

tff(c_577,plain,(
    ! [A_154,B_155] :
      ( k4_xboole_0(k2_xboole_0(A_154,B_155),B_155) = A_154
      | ~ r1_xboole_0(A_154,B_155) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_603,plain,(
    ! [A_15,B_16] :
      ( k4_xboole_0(k2_xboole_0(A_15,B_16),k4_xboole_0(B_16,A_15)) = A_15
      | ~ r1_xboole_0(A_15,k4_xboole_0(B_16,A_15)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_577])).

tff(c_733,plain,(
    ! [A_161,B_162] : k4_xboole_0(k2_xboole_0(A_161,B_162),k4_xboole_0(B_162,A_161)) = A_161 ),
    inference(demodulation,[status(thm),theory(equality)],[c_212,c_603])).

tff(c_775,plain,(
    ! [B_134,A_133] : k4_xboole_0(k2_xboole_0(B_134,A_133),k4_xboole_0(B_134,A_133)) = A_133 ),
    inference(superposition,[status(thm),theory(equality)],[c_312,c_733])).

tff(c_2642,plain,(
    ! [B_252,A_253] : k4_xboole_0(k2_xboole_0(B_252,A_253),k4_xboole_0(B_252,A_253)) = A_253 ),
    inference(superposition,[status(thm),theory(equality)],[c_312,c_733])).

tff(c_2679,plain,(
    ! [B_134,A_133] : k4_xboole_0(k2_xboole_0(k2_xboole_0(B_134,A_133),k4_xboole_0(B_134,A_133)),A_133) = k4_xboole_0(B_134,A_133) ),
    inference(superposition,[status(thm),theory(equality)],[c_775,c_2642])).

tff(c_2737,plain,(
    ! [B_134,A_133] : k4_xboole_0(k2_xboole_0(B_134,A_133),A_133) = k4_xboole_0(B_134,A_133) ),
    inference(demodulation,[status(thm),theory(equality)],[c_465,c_18,c_20,c_2679])).

tff(c_26,plain,(
    ! [A_24,B_25] :
      ( k4_xboole_0(k2_xboole_0(A_24,B_25),B_25) = A_24
      | ~ r1_xboole_0(A_24,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_3429,plain,(
    ! [A_289,B_290] :
      ( k4_xboole_0(A_289,B_290) = A_289
      | ~ r1_xboole_0(A_289,B_290) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2737,c_26])).

tff(c_18125,plain,(
    ! [A_26110,B_26111] :
      ( k4_xboole_0(k1_tarski(A_26110),B_26111) = k1_tarski(A_26110)
      | r2_hidden(A_26110,B_26111) ) ),
    inference(resolution,[status(thm)],[c_82,c_3429])).

tff(c_88,plain,
    ( k4_xboole_0(k1_tarski('#skF_4'),'#skF_5') != k1_tarski('#skF_4')
    | r2_hidden('#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_248,plain,(
    k4_xboole_0(k1_tarski('#skF_4'),'#skF_5') != k1_tarski('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_88])).

tff(c_18244,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_18125,c_248])).

tff(c_18319,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_174,c_18244])).

tff(c_18320,plain,(
    r2_hidden('#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_88])).

tff(c_68,plain,(
    ! [A_64] : k2_tarski(A_64,A_64) = k1_tarski(A_64) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_218,plain,(
    ! [A_121,B_122] : k1_enumset1(A_121,A_121,B_122) = k2_tarski(A_121,B_122) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_42,plain,(
    ! [E_40,B_35,C_36] : r2_hidden(E_40,k1_enumset1(E_40,B_35,C_36)) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_236,plain,(
    ! [A_123,B_124] : r2_hidden(A_123,k2_tarski(A_123,B_124)) ),
    inference(superposition,[status(thm),theory(equality)],[c_218,c_42])).

tff(c_245,plain,(
    ! [A_64] : r2_hidden(A_64,k1_tarski(A_64)) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_236])).

tff(c_18321,plain,(
    k4_xboole_0(k1_tarski('#skF_4'),'#skF_5') = k1_tarski('#skF_4') ),
    inference(splitRight,[status(thm)],[c_88])).

tff(c_92,plain,
    ( k4_xboole_0(k1_tarski('#skF_4'),'#skF_5') != k1_tarski('#skF_4')
    | k4_xboole_0(k1_tarski('#skF_6'),'#skF_7') = k1_tarski('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_18429,plain,(
    k4_xboole_0(k1_tarski('#skF_6'),'#skF_7') = k1_tarski('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18321,c_92])).

tff(c_18436,plain,(
    r1_xboole_0(k1_tarski('#skF_6'),'#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_18429,c_24])).

tff(c_18766,plain,(
    ! [A_26307,B_26308,C_26309] :
      ( ~ r1_xboole_0(A_26307,B_26308)
      | ~ r2_hidden(C_26309,B_26308)
      | ~ r2_hidden(C_26309,A_26307) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_18935,plain,(
    ! [C_26317] :
      ( ~ r2_hidden(C_26317,'#skF_7')
      | ~ r2_hidden(C_26317,k1_tarski('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_18436,c_18766])).

tff(c_18947,plain,(
    ~ r2_hidden('#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_245,c_18935])).

tff(c_18953,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18320,c_18947])).

tff(c_18954,plain,(
    r2_hidden('#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_90])).

tff(c_18994,plain,(
    ! [A_26325,B_26326] : k1_enumset1(A_26325,A_26325,B_26326) = k2_tarski(A_26325,B_26326) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_19017,plain,(
    ! [A_26329,B_26330] : r2_hidden(A_26329,k2_tarski(A_26329,B_26330)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18994,c_42])).

tff(c_19026,plain,(
    ! [A_64] : r2_hidden(A_64,k1_tarski(A_64)) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_19017])).

tff(c_18955,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_90])).

tff(c_94,plain,
    ( ~ r2_hidden('#skF_4','#skF_5')
    | k4_xboole_0(k1_tarski('#skF_6'),'#skF_7') = k1_tarski('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_19162,plain,(
    k4_xboole_0(k1_tarski('#skF_6'),'#skF_7') = k1_tarski('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18955,c_94])).

tff(c_19169,plain,(
    r1_xboole_0(k1_tarski('#skF_6'),'#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_19162,c_24])).

tff(c_19453,plain,(
    ! [A_26362,B_26363,C_26364] :
      ( ~ r1_xboole_0(A_26362,B_26363)
      | ~ r2_hidden(C_26364,B_26363)
      | ~ r2_hidden(C_26364,A_26362) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_19577,plain,(
    ! [C_26370] :
      ( ~ r2_hidden(C_26370,'#skF_7')
      | ~ r2_hidden(C_26370,k1_tarski('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_19169,c_19453])).

tff(c_19589,plain,(
    ~ r2_hidden('#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_19026,c_19577])).

tff(c_19595,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18954,c_19589])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:44:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.18/3.65  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.18/3.66  
% 10.18/3.66  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.18/3.66  %$ r2_hidden > r1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_4 > #skF_3 > #skF_1
% 10.18/3.66  
% 10.18/3.66  %Foreground sorts:
% 10.18/3.66  
% 10.18/3.66  
% 10.18/3.66  %Background operators:
% 10.18/3.66  
% 10.18/3.66  
% 10.18/3.66  %Foreground operators:
% 10.18/3.66  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.18/3.66  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 10.18/3.66  tff(k1_tarski, type, k1_tarski: $i > $i).
% 10.18/3.66  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 10.18/3.66  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 10.18/3.66  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 10.18/3.66  tff('#skF_7', type, '#skF_7': $i).
% 10.18/3.66  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 10.18/3.66  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 10.18/3.66  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 10.18/3.66  tff('#skF_5', type, '#skF_5': $i).
% 10.18/3.66  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 10.18/3.66  tff('#skF_6', type, '#skF_6': $i).
% 10.18/3.66  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 10.18/3.66  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 10.18/3.66  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 10.18/3.66  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 10.18/3.66  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.18/3.66  tff(k3_tarski, type, k3_tarski: $i > $i).
% 10.18/3.66  tff('#skF_4', type, '#skF_4': $i).
% 10.18/3.66  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.18/3.66  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 10.18/3.66  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 10.18/3.66  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 10.18/3.66  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 10.18/3.66  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 10.18/3.66  
% 10.18/3.68  tff(f_127, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_tarski(A)) <=> ~r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_zfmisc_1)).
% 10.18/3.68  tff(f_117, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 10.18/3.68  tff(f_75, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 10.18/3.68  tff(f_119, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 10.18/3.68  tff(f_61, axiom, (![A, B]: (k2_xboole_0(A, k2_xboole_0(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_xboole_1)).
% 10.18/3.68  tff(f_57, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 10.18/3.68  tff(f_59, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_1)).
% 10.18/3.68  tff(f_63, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 10.18/3.68  tff(f_33, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 10.18/3.68  tff(f_67, axiom, (![A, B]: (r1_xboole_0(A, B) => (k4_xboole_0(k2_xboole_0(A, B), B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_xboole_1)).
% 10.18/3.68  tff(f_100, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 10.18/3.68  tff(f_102, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 10.18/3.68  tff(f_90, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 10.18/3.68  tff(f_51, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 10.18/3.68  tff(c_90, plain, (~r2_hidden('#skF_4', '#skF_5') | r2_hidden('#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_127])).
% 10.18/3.68  tff(c_174, plain, (~r2_hidden('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_90])).
% 10.18/3.68  tff(c_82, plain, (![A_92, B_93]: (r1_xboole_0(k1_tarski(A_92), B_93) | r2_hidden(A_92, B_93))), inference(cnfTransformation, [status(thm)], [f_117])).
% 10.18/3.68  tff(c_34, plain, (![B_33, A_32]: (k2_tarski(B_33, A_32)=k2_tarski(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_75])).
% 10.18/3.68  tff(c_264, plain, (![A_128, B_129]: (k3_tarski(k2_tarski(A_128, B_129))=k2_xboole_0(A_128, B_129))), inference(cnfTransformation, [status(thm)], [f_119])).
% 10.18/3.68  tff(c_306, plain, (![A_133, B_134]: (k3_tarski(k2_tarski(A_133, B_134))=k2_xboole_0(B_134, A_133))), inference(superposition, [status(thm), theory('equality')], [c_34, c_264])).
% 10.18/3.68  tff(c_84, plain, (![A_94, B_95]: (k3_tarski(k2_tarski(A_94, B_95))=k2_xboole_0(A_94, B_95))), inference(cnfTransformation, [status(thm)], [f_119])).
% 10.18/3.68  tff(c_312, plain, (![B_134, A_133]: (k2_xboole_0(B_134, A_133)=k2_xboole_0(A_133, B_134))), inference(superposition, [status(thm), theory('equality')], [c_306, c_84])).
% 10.18/3.68  tff(c_436, plain, (![A_142, B_143]: (k2_xboole_0(A_142, k2_xboole_0(A_142, B_143))=k2_xboole_0(A_142, B_143))), inference(cnfTransformation, [status(thm)], [f_61])).
% 10.18/3.68  tff(c_465, plain, (![B_134, A_133]: (k2_xboole_0(B_134, k2_xboole_0(A_133, B_134))=k2_xboole_0(B_134, A_133))), inference(superposition, [status(thm), theory('equality')], [c_312, c_436])).
% 10.18/3.68  tff(c_18, plain, (![A_15, B_16]: (k2_xboole_0(A_15, k4_xboole_0(B_16, A_15))=k2_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_57])).
% 10.18/3.68  tff(c_20, plain, (![A_17, B_18, C_19]: (k2_xboole_0(k2_xboole_0(A_17, B_18), C_19)=k2_xboole_0(A_17, k2_xboole_0(B_18, C_19)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 10.18/3.68  tff(c_24, plain, (![A_22, B_23]: (r1_xboole_0(k4_xboole_0(A_22, B_23), B_23))), inference(cnfTransformation, [status(thm)], [f_63])).
% 10.18/3.68  tff(c_209, plain, (![B_117, A_118]: (r1_xboole_0(B_117, A_118) | ~r1_xboole_0(A_118, B_117))), inference(cnfTransformation, [status(thm)], [f_33])).
% 10.18/3.68  tff(c_212, plain, (![B_23, A_22]: (r1_xboole_0(B_23, k4_xboole_0(A_22, B_23)))), inference(resolution, [status(thm)], [c_24, c_209])).
% 10.18/3.68  tff(c_577, plain, (![A_154, B_155]: (k4_xboole_0(k2_xboole_0(A_154, B_155), B_155)=A_154 | ~r1_xboole_0(A_154, B_155))), inference(cnfTransformation, [status(thm)], [f_67])).
% 10.18/3.68  tff(c_603, plain, (![A_15, B_16]: (k4_xboole_0(k2_xboole_0(A_15, B_16), k4_xboole_0(B_16, A_15))=A_15 | ~r1_xboole_0(A_15, k4_xboole_0(B_16, A_15)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_577])).
% 10.18/3.68  tff(c_733, plain, (![A_161, B_162]: (k4_xboole_0(k2_xboole_0(A_161, B_162), k4_xboole_0(B_162, A_161))=A_161)), inference(demodulation, [status(thm), theory('equality')], [c_212, c_603])).
% 10.18/3.68  tff(c_775, plain, (![B_134, A_133]: (k4_xboole_0(k2_xboole_0(B_134, A_133), k4_xboole_0(B_134, A_133))=A_133)), inference(superposition, [status(thm), theory('equality')], [c_312, c_733])).
% 10.18/3.68  tff(c_2642, plain, (![B_252, A_253]: (k4_xboole_0(k2_xboole_0(B_252, A_253), k4_xboole_0(B_252, A_253))=A_253)), inference(superposition, [status(thm), theory('equality')], [c_312, c_733])).
% 10.18/3.68  tff(c_2679, plain, (![B_134, A_133]: (k4_xboole_0(k2_xboole_0(k2_xboole_0(B_134, A_133), k4_xboole_0(B_134, A_133)), A_133)=k4_xboole_0(B_134, A_133))), inference(superposition, [status(thm), theory('equality')], [c_775, c_2642])).
% 10.18/3.68  tff(c_2737, plain, (![B_134, A_133]: (k4_xboole_0(k2_xboole_0(B_134, A_133), A_133)=k4_xboole_0(B_134, A_133))), inference(demodulation, [status(thm), theory('equality')], [c_465, c_18, c_20, c_2679])).
% 10.18/3.68  tff(c_26, plain, (![A_24, B_25]: (k4_xboole_0(k2_xboole_0(A_24, B_25), B_25)=A_24 | ~r1_xboole_0(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_67])).
% 10.18/3.68  tff(c_3429, plain, (![A_289, B_290]: (k4_xboole_0(A_289, B_290)=A_289 | ~r1_xboole_0(A_289, B_290))), inference(demodulation, [status(thm), theory('equality')], [c_2737, c_26])).
% 10.18/3.68  tff(c_18125, plain, (![A_26110, B_26111]: (k4_xboole_0(k1_tarski(A_26110), B_26111)=k1_tarski(A_26110) | r2_hidden(A_26110, B_26111))), inference(resolution, [status(thm)], [c_82, c_3429])).
% 10.18/3.68  tff(c_88, plain, (k4_xboole_0(k1_tarski('#skF_4'), '#skF_5')!=k1_tarski('#skF_4') | r2_hidden('#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_127])).
% 10.18/3.68  tff(c_248, plain, (k4_xboole_0(k1_tarski('#skF_4'), '#skF_5')!=k1_tarski('#skF_4')), inference(splitLeft, [status(thm)], [c_88])).
% 10.18/3.68  tff(c_18244, plain, (r2_hidden('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_18125, c_248])).
% 10.18/3.68  tff(c_18319, plain, $false, inference(negUnitSimplification, [status(thm)], [c_174, c_18244])).
% 10.18/3.68  tff(c_18320, plain, (r2_hidden('#skF_6', '#skF_7')), inference(splitRight, [status(thm)], [c_88])).
% 10.18/3.68  tff(c_68, plain, (![A_64]: (k2_tarski(A_64, A_64)=k1_tarski(A_64))), inference(cnfTransformation, [status(thm)], [f_100])).
% 10.18/3.68  tff(c_218, plain, (![A_121, B_122]: (k1_enumset1(A_121, A_121, B_122)=k2_tarski(A_121, B_122))), inference(cnfTransformation, [status(thm)], [f_102])).
% 10.18/3.68  tff(c_42, plain, (![E_40, B_35, C_36]: (r2_hidden(E_40, k1_enumset1(E_40, B_35, C_36)))), inference(cnfTransformation, [status(thm)], [f_90])).
% 10.18/3.68  tff(c_236, plain, (![A_123, B_124]: (r2_hidden(A_123, k2_tarski(A_123, B_124)))), inference(superposition, [status(thm), theory('equality')], [c_218, c_42])).
% 10.18/3.68  tff(c_245, plain, (![A_64]: (r2_hidden(A_64, k1_tarski(A_64)))), inference(superposition, [status(thm), theory('equality')], [c_68, c_236])).
% 10.18/3.68  tff(c_18321, plain, (k4_xboole_0(k1_tarski('#skF_4'), '#skF_5')=k1_tarski('#skF_4')), inference(splitRight, [status(thm)], [c_88])).
% 10.18/3.68  tff(c_92, plain, (k4_xboole_0(k1_tarski('#skF_4'), '#skF_5')!=k1_tarski('#skF_4') | k4_xboole_0(k1_tarski('#skF_6'), '#skF_7')=k1_tarski('#skF_6')), inference(cnfTransformation, [status(thm)], [f_127])).
% 10.18/3.68  tff(c_18429, plain, (k4_xboole_0(k1_tarski('#skF_6'), '#skF_7')=k1_tarski('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_18321, c_92])).
% 10.18/3.68  tff(c_18436, plain, (r1_xboole_0(k1_tarski('#skF_6'), '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_18429, c_24])).
% 10.18/3.68  tff(c_18766, plain, (![A_26307, B_26308, C_26309]: (~r1_xboole_0(A_26307, B_26308) | ~r2_hidden(C_26309, B_26308) | ~r2_hidden(C_26309, A_26307))), inference(cnfTransformation, [status(thm)], [f_51])).
% 10.18/3.68  tff(c_18935, plain, (![C_26317]: (~r2_hidden(C_26317, '#skF_7') | ~r2_hidden(C_26317, k1_tarski('#skF_6')))), inference(resolution, [status(thm)], [c_18436, c_18766])).
% 10.18/3.68  tff(c_18947, plain, (~r2_hidden('#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_245, c_18935])).
% 10.18/3.68  tff(c_18953, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18320, c_18947])).
% 10.18/3.68  tff(c_18954, plain, (r2_hidden('#skF_6', '#skF_7')), inference(splitRight, [status(thm)], [c_90])).
% 10.18/3.68  tff(c_18994, plain, (![A_26325, B_26326]: (k1_enumset1(A_26325, A_26325, B_26326)=k2_tarski(A_26325, B_26326))), inference(cnfTransformation, [status(thm)], [f_102])).
% 10.18/3.68  tff(c_19017, plain, (![A_26329, B_26330]: (r2_hidden(A_26329, k2_tarski(A_26329, B_26330)))), inference(superposition, [status(thm), theory('equality')], [c_18994, c_42])).
% 10.18/3.68  tff(c_19026, plain, (![A_64]: (r2_hidden(A_64, k1_tarski(A_64)))), inference(superposition, [status(thm), theory('equality')], [c_68, c_19017])).
% 10.18/3.68  tff(c_18955, plain, (r2_hidden('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_90])).
% 10.18/3.68  tff(c_94, plain, (~r2_hidden('#skF_4', '#skF_5') | k4_xboole_0(k1_tarski('#skF_6'), '#skF_7')=k1_tarski('#skF_6')), inference(cnfTransformation, [status(thm)], [f_127])).
% 10.18/3.68  tff(c_19162, plain, (k4_xboole_0(k1_tarski('#skF_6'), '#skF_7')=k1_tarski('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_18955, c_94])).
% 10.18/3.68  tff(c_19169, plain, (r1_xboole_0(k1_tarski('#skF_6'), '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_19162, c_24])).
% 10.18/3.68  tff(c_19453, plain, (![A_26362, B_26363, C_26364]: (~r1_xboole_0(A_26362, B_26363) | ~r2_hidden(C_26364, B_26363) | ~r2_hidden(C_26364, A_26362))), inference(cnfTransformation, [status(thm)], [f_51])).
% 10.18/3.68  tff(c_19577, plain, (![C_26370]: (~r2_hidden(C_26370, '#skF_7') | ~r2_hidden(C_26370, k1_tarski('#skF_6')))), inference(resolution, [status(thm)], [c_19169, c_19453])).
% 10.18/3.68  tff(c_19589, plain, (~r2_hidden('#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_19026, c_19577])).
% 10.18/3.68  tff(c_19595, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18954, c_19589])).
% 10.18/3.68  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.18/3.68  
% 10.18/3.68  Inference rules
% 10.18/3.68  ----------------------
% 10.18/3.68  #Ref     : 0
% 10.18/3.68  #Sup     : 4265
% 10.18/3.68  #Fact    : 18
% 10.18/3.68  #Define  : 0
% 10.18/3.68  #Split   : 2
% 10.18/3.68  #Chain   : 0
% 10.18/3.68  #Close   : 0
% 10.18/3.68  
% 10.18/3.68  Ordering : KBO
% 10.18/3.68  
% 10.18/3.68  Simplification rules
% 10.18/3.68  ----------------------
% 10.18/3.68  #Subsume      : 373
% 10.18/3.68  #Demod        : 4446
% 10.18/3.68  #Tautology    : 2581
% 10.18/3.68  #SimpNegUnit  : 17
% 10.18/3.68  #BackRed      : 6
% 10.18/3.68  
% 10.18/3.68  #Partial instantiations: 9828
% 10.18/3.68  #Strategies tried      : 1
% 10.18/3.68  
% 10.18/3.68  Timing (in seconds)
% 10.18/3.68  ----------------------
% 10.18/3.68  Preprocessing        : 0.36
% 10.18/3.68  Parsing              : 0.19
% 10.18/3.68  CNF conversion       : 0.03
% 10.18/3.68  Main loop            : 2.47
% 10.18/3.68  Inferencing          : 0.82
% 10.18/3.68  Reduction            : 1.14
% 10.18/3.68  Demodulation         : 0.99
% 10.18/3.68  BG Simplification    : 0.08
% 10.18/3.68  Subsumption          : 0.31
% 10.18/3.68  Abstraction          : 0.11
% 10.18/3.68  MUC search           : 0.00
% 10.18/3.68  Cooper               : 0.00
% 10.18/3.68  Total                : 2.87
% 10.18/3.68  Index Insertion      : 0.00
% 10.18/3.68  Index Deletion       : 0.00
% 10.18/3.68  Index Matching       : 0.00
% 10.18/3.68  BG Taut test         : 0.00
%------------------------------------------------------------------------------
