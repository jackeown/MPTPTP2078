%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:55 EST 2020

% Result     : Theorem 7.08s
% Output     : CNFRefutation 7.08s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 111 expanded)
%              Number of leaves         :   32 (  51 expanded)
%              Depth                    :   10
%              Number of atoms          :   78 ( 136 expanded)
%              Number of equality atoms :   35 (  60 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_1

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_95,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),B) = k1_tarski(A)
      <=> ~ r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_zfmisc_1)).

tff(f_59,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_82,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_53,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_55,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_89,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k4_xboole_0(B,k1_tarski(C)))
    <=> ( r2_hidden(A,B)
        & A != C ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).

tff(c_48,plain,
    ( ~ r2_hidden('#skF_3','#skF_4')
    | r2_hidden('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_82,plain,(
    ~ r2_hidden('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_18,plain,(
    ! [A_18] : k5_xboole_0(A_18,k1_xboole_0) = A_18 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_38,plain,(
    ! [A_52,B_53] :
      ( r1_xboole_0(k1_tarski(A_52),B_53)
      | r2_hidden(A_52,B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_12,plain,(
    ! [A_12] :
      ( r2_hidden('#skF_2'(A_12),A_12)
      | k1_xboole_0 = A_12 ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_214,plain,(
    ! [A_74,B_75,C_76] :
      ( ~ r1_xboole_0(A_74,B_75)
      | ~ r2_hidden(C_76,k3_xboole_0(A_74,B_75)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_235,plain,(
    ! [A_79,B_80] :
      ( ~ r1_xboole_0(A_79,B_80)
      | k3_xboole_0(A_79,B_80) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_12,c_214])).

tff(c_2580,plain,(
    ! [A_191,B_192] :
      ( k3_xboole_0(k1_tarski(A_191),B_192) = k1_xboole_0
      | r2_hidden(A_191,B_192) ) ),
    inference(resolution,[status(thm)],[c_38,c_235])).

tff(c_14,plain,(
    ! [A_14,B_15] : k5_xboole_0(A_14,k3_xboole_0(A_14,B_15)) = k4_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_2617,plain,(
    ! [A_191,B_192] :
      ( k5_xboole_0(k1_tarski(A_191),k1_xboole_0) = k4_xboole_0(k1_tarski(A_191),B_192)
      | r2_hidden(A_191,B_192) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2580,c_14])).

tff(c_11746,plain,(
    ! [A_300,B_301] :
      ( k4_xboole_0(k1_tarski(A_300),B_301) = k1_tarski(A_300)
      | r2_hidden(A_300,B_301) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_2617])).

tff(c_46,plain,
    ( k4_xboole_0(k1_tarski('#skF_3'),'#skF_4') != k1_tarski('#skF_3')
    | r2_hidden('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_234,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),'#skF_4') != k1_tarski('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_11870,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_11746,c_234])).

tff(c_11935,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_11870])).

tff(c_11936,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_11937,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),'#skF_4') = k1_tarski('#skF_3') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_50,plain,
    ( k4_xboole_0(k1_tarski('#skF_3'),'#skF_4') != k1_tarski('#skF_3')
    | k4_xboole_0(k1_tarski('#skF_5'),'#skF_6') = k1_tarski('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_11938,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),'#skF_4') != k1_tarski('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_11947,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_11937,c_11938])).

tff(c_11948,plain,(
    k4_xboole_0(k1_tarski('#skF_5'),'#skF_6') = k1_tarski('#skF_5') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_20,plain,(
    ! [A_19,B_20] : r1_xboole_0(k4_xboole_0(A_19,B_20),B_20) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_11960,plain,(
    r1_xboole_0(k1_tarski('#skF_5'),'#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_11948,c_20])).

tff(c_11965,plain,(
    ! [A_302,B_303] :
      ( ~ r1_xboole_0(A_302,B_303)
      | k3_xboole_0(A_302,B_303) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_12,c_214])).

tff(c_11978,plain,(
    k3_xboole_0(k1_tarski('#skF_5'),'#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_11960,c_11965])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_11988,plain,(
    k3_xboole_0('#skF_6',k1_tarski('#skF_5')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_11978,c_2])).

tff(c_12145,plain,(
    ! [A_309,B_310] : k5_xboole_0(A_309,k3_xboole_0(A_309,B_310)) = k4_xboole_0(A_309,B_310) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_12167,plain,(
    k4_xboole_0('#skF_6',k1_tarski('#skF_5')) = k5_xboole_0('#skF_6',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_11988,c_12145])).

tff(c_12192,plain,(
    k4_xboole_0('#skF_6',k1_tarski('#skF_5')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_12167])).

tff(c_42,plain,(
    ! [C_56,B_55] : ~ r2_hidden(C_56,k4_xboole_0(B_55,k1_tarski(C_56))) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_12409,plain,(
    ~ r2_hidden('#skF_5','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_12192,c_42])).

tff(c_12419,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_11936,c_12409])).

tff(c_12420,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_12421,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_52,plain,
    ( ~ r2_hidden('#skF_3','#skF_4')
    | k4_xboole_0(k1_tarski('#skF_5'),'#skF_6') = k1_tarski('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_12624,plain,(
    k4_xboole_0(k1_tarski('#skF_5'),'#skF_6') = k1_tarski('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12421,c_52])).

tff(c_12634,plain,(
    r1_xboole_0(k1_tarski('#skF_5'),'#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_12624,c_20])).

tff(c_12585,plain,(
    ! [A_332,B_333,C_334] :
      ( ~ r1_xboole_0(A_332,B_333)
      | ~ r2_hidden(C_334,k3_xboole_0(A_332,B_333)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_12599,plain,(
    ! [A_332,B_333] :
      ( ~ r1_xboole_0(A_332,B_333)
      | k3_xboole_0(A_332,B_333) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_12,c_12585])).

tff(c_12643,plain,(
    k3_xboole_0(k1_tarski('#skF_5'),'#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12634,c_12599])).

tff(c_12663,plain,(
    k3_xboole_0('#skF_6',k1_tarski('#skF_5')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_12643])).

tff(c_12690,plain,(
    ! [A_341,B_342] : k5_xboole_0(A_341,k3_xboole_0(A_341,B_342)) = k4_xboole_0(A_341,B_342) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_12703,plain,(
    k4_xboole_0('#skF_6',k1_tarski('#skF_5')) = k5_xboole_0('#skF_6',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_12663,c_12690])).

tff(c_12722,plain,(
    k4_xboole_0('#skF_6',k1_tarski('#skF_5')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_12703])).

tff(c_12753,plain,(
    ~ r2_hidden('#skF_5','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_12722,c_42])).

tff(c_12763,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12420,c_12753])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:25:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.08/2.64  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.08/2.64  
% 7.08/2.64  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.08/2.64  %$ r2_hidden > r1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_1
% 7.08/2.64  
% 7.08/2.64  %Foreground sorts:
% 7.08/2.64  
% 7.08/2.64  
% 7.08/2.64  %Background operators:
% 7.08/2.64  
% 7.08/2.64  
% 7.08/2.64  %Foreground operators:
% 7.08/2.64  tff('#skF_2', type, '#skF_2': $i > $i).
% 7.08/2.64  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.08/2.64  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.08/2.64  tff(k1_tarski, type, k1_tarski: $i > $i).
% 7.08/2.64  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.08/2.64  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.08/2.64  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 7.08/2.64  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 7.08/2.64  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 7.08/2.64  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.08/2.64  tff('#skF_5', type, '#skF_5': $i).
% 7.08/2.64  tff('#skF_6', type, '#skF_6': $i).
% 7.08/2.64  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 7.08/2.64  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 7.08/2.64  tff('#skF_3', type, '#skF_3': $i).
% 7.08/2.64  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 7.08/2.64  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 7.08/2.64  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.08/2.64  tff('#skF_4', type, '#skF_4': $i).
% 7.08/2.64  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.08/2.64  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.08/2.64  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 7.08/2.64  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 7.08/2.64  
% 7.08/2.66  tff(f_95, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_tarski(A)) <=> ~r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_zfmisc_1)).
% 7.08/2.66  tff(f_59, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 7.08/2.66  tff(f_82, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 7.08/2.66  tff(f_53, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 7.08/2.66  tff(f_45, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 7.08/2.66  tff(f_55, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 7.08/2.66  tff(f_61, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 7.08/2.66  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 7.08/2.66  tff(f_89, axiom, (![A, B, C]: (r2_hidden(A, k4_xboole_0(B, k1_tarski(C))) <=> (r2_hidden(A, B) & ~(A = C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 7.08/2.66  tff(c_48, plain, (~r2_hidden('#skF_3', '#skF_4') | r2_hidden('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_95])).
% 7.08/2.66  tff(c_82, plain, (~r2_hidden('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_48])).
% 7.08/2.66  tff(c_18, plain, (![A_18]: (k5_xboole_0(A_18, k1_xboole_0)=A_18)), inference(cnfTransformation, [status(thm)], [f_59])).
% 7.08/2.66  tff(c_38, plain, (![A_52, B_53]: (r1_xboole_0(k1_tarski(A_52), B_53) | r2_hidden(A_52, B_53))), inference(cnfTransformation, [status(thm)], [f_82])).
% 7.08/2.66  tff(c_12, plain, (![A_12]: (r2_hidden('#skF_2'(A_12), A_12) | k1_xboole_0=A_12)), inference(cnfTransformation, [status(thm)], [f_53])).
% 7.08/2.66  tff(c_214, plain, (![A_74, B_75, C_76]: (~r1_xboole_0(A_74, B_75) | ~r2_hidden(C_76, k3_xboole_0(A_74, B_75)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.08/2.66  tff(c_235, plain, (![A_79, B_80]: (~r1_xboole_0(A_79, B_80) | k3_xboole_0(A_79, B_80)=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_214])).
% 7.08/2.66  tff(c_2580, plain, (![A_191, B_192]: (k3_xboole_0(k1_tarski(A_191), B_192)=k1_xboole_0 | r2_hidden(A_191, B_192))), inference(resolution, [status(thm)], [c_38, c_235])).
% 7.08/2.66  tff(c_14, plain, (![A_14, B_15]: (k5_xboole_0(A_14, k3_xboole_0(A_14, B_15))=k4_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_55])).
% 7.08/2.66  tff(c_2617, plain, (![A_191, B_192]: (k5_xboole_0(k1_tarski(A_191), k1_xboole_0)=k4_xboole_0(k1_tarski(A_191), B_192) | r2_hidden(A_191, B_192))), inference(superposition, [status(thm), theory('equality')], [c_2580, c_14])).
% 7.08/2.66  tff(c_11746, plain, (![A_300, B_301]: (k4_xboole_0(k1_tarski(A_300), B_301)=k1_tarski(A_300) | r2_hidden(A_300, B_301))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_2617])).
% 7.08/2.66  tff(c_46, plain, (k4_xboole_0(k1_tarski('#skF_3'), '#skF_4')!=k1_tarski('#skF_3') | r2_hidden('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_95])).
% 7.08/2.66  tff(c_234, plain, (k4_xboole_0(k1_tarski('#skF_3'), '#skF_4')!=k1_tarski('#skF_3')), inference(splitLeft, [status(thm)], [c_46])).
% 7.08/2.66  tff(c_11870, plain, (r2_hidden('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_11746, c_234])).
% 7.08/2.66  tff(c_11935, plain, $false, inference(negUnitSimplification, [status(thm)], [c_82, c_11870])).
% 7.08/2.66  tff(c_11936, plain, (r2_hidden('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_46])).
% 7.08/2.66  tff(c_11937, plain, (k4_xboole_0(k1_tarski('#skF_3'), '#skF_4')=k1_tarski('#skF_3')), inference(splitRight, [status(thm)], [c_46])).
% 7.08/2.66  tff(c_50, plain, (k4_xboole_0(k1_tarski('#skF_3'), '#skF_4')!=k1_tarski('#skF_3') | k4_xboole_0(k1_tarski('#skF_5'), '#skF_6')=k1_tarski('#skF_5')), inference(cnfTransformation, [status(thm)], [f_95])).
% 7.08/2.66  tff(c_11938, plain, (k4_xboole_0(k1_tarski('#skF_3'), '#skF_4')!=k1_tarski('#skF_3')), inference(splitLeft, [status(thm)], [c_50])).
% 7.08/2.66  tff(c_11947, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_11937, c_11938])).
% 7.08/2.66  tff(c_11948, plain, (k4_xboole_0(k1_tarski('#skF_5'), '#skF_6')=k1_tarski('#skF_5')), inference(splitRight, [status(thm)], [c_50])).
% 7.08/2.66  tff(c_20, plain, (![A_19, B_20]: (r1_xboole_0(k4_xboole_0(A_19, B_20), B_20))), inference(cnfTransformation, [status(thm)], [f_61])).
% 7.08/2.66  tff(c_11960, plain, (r1_xboole_0(k1_tarski('#skF_5'), '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_11948, c_20])).
% 7.08/2.66  tff(c_11965, plain, (![A_302, B_303]: (~r1_xboole_0(A_302, B_303) | k3_xboole_0(A_302, B_303)=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_214])).
% 7.08/2.66  tff(c_11978, plain, (k3_xboole_0(k1_tarski('#skF_5'), '#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_11960, c_11965])).
% 7.08/2.66  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 7.08/2.66  tff(c_11988, plain, (k3_xboole_0('#skF_6', k1_tarski('#skF_5'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_11978, c_2])).
% 7.08/2.66  tff(c_12145, plain, (![A_309, B_310]: (k5_xboole_0(A_309, k3_xboole_0(A_309, B_310))=k4_xboole_0(A_309, B_310))), inference(cnfTransformation, [status(thm)], [f_55])).
% 7.08/2.66  tff(c_12167, plain, (k4_xboole_0('#skF_6', k1_tarski('#skF_5'))=k5_xboole_0('#skF_6', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_11988, c_12145])).
% 7.08/2.66  tff(c_12192, plain, (k4_xboole_0('#skF_6', k1_tarski('#skF_5'))='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_18, c_12167])).
% 7.08/2.66  tff(c_42, plain, (![C_56, B_55]: (~r2_hidden(C_56, k4_xboole_0(B_55, k1_tarski(C_56))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 7.08/2.66  tff(c_12409, plain, (~r2_hidden('#skF_5', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_12192, c_42])).
% 7.08/2.66  tff(c_12419, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_11936, c_12409])).
% 7.08/2.66  tff(c_12420, plain, (r2_hidden('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_48])).
% 7.08/2.66  tff(c_12421, plain, (r2_hidden('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_48])).
% 7.08/2.66  tff(c_52, plain, (~r2_hidden('#skF_3', '#skF_4') | k4_xboole_0(k1_tarski('#skF_5'), '#skF_6')=k1_tarski('#skF_5')), inference(cnfTransformation, [status(thm)], [f_95])).
% 7.08/2.66  tff(c_12624, plain, (k4_xboole_0(k1_tarski('#skF_5'), '#skF_6')=k1_tarski('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_12421, c_52])).
% 7.08/2.66  tff(c_12634, plain, (r1_xboole_0(k1_tarski('#skF_5'), '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_12624, c_20])).
% 7.08/2.66  tff(c_12585, plain, (![A_332, B_333, C_334]: (~r1_xboole_0(A_332, B_333) | ~r2_hidden(C_334, k3_xboole_0(A_332, B_333)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.08/2.66  tff(c_12599, plain, (![A_332, B_333]: (~r1_xboole_0(A_332, B_333) | k3_xboole_0(A_332, B_333)=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_12585])).
% 7.08/2.66  tff(c_12643, plain, (k3_xboole_0(k1_tarski('#skF_5'), '#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_12634, c_12599])).
% 7.08/2.66  tff(c_12663, plain, (k3_xboole_0('#skF_6', k1_tarski('#skF_5'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_2, c_12643])).
% 7.08/2.66  tff(c_12690, plain, (![A_341, B_342]: (k5_xboole_0(A_341, k3_xboole_0(A_341, B_342))=k4_xboole_0(A_341, B_342))), inference(cnfTransformation, [status(thm)], [f_55])).
% 7.08/2.66  tff(c_12703, plain, (k4_xboole_0('#skF_6', k1_tarski('#skF_5'))=k5_xboole_0('#skF_6', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_12663, c_12690])).
% 7.08/2.66  tff(c_12722, plain, (k4_xboole_0('#skF_6', k1_tarski('#skF_5'))='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_18, c_12703])).
% 7.08/2.66  tff(c_12753, plain, (~r2_hidden('#skF_5', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_12722, c_42])).
% 7.08/2.66  tff(c_12763, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12420, c_12753])).
% 7.08/2.66  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.08/2.66  
% 7.08/2.66  Inference rules
% 7.08/2.66  ----------------------
% 7.08/2.66  #Ref     : 0
% 7.08/2.66  #Sup     : 3151
% 7.08/2.66  #Fact    : 0
% 7.08/2.66  #Define  : 0
% 7.08/2.66  #Split   : 3
% 7.08/2.66  #Chain   : 0
% 7.08/2.66  #Close   : 0
% 7.08/2.66  
% 7.08/2.66  Ordering : KBO
% 7.08/2.66  
% 7.08/2.66  Simplification rules
% 7.08/2.66  ----------------------
% 7.08/2.66  #Subsume      : 308
% 7.08/2.66  #Demod        : 3388
% 7.08/2.66  #Tautology    : 1997
% 7.08/2.66  #SimpNegUnit  : 51
% 7.08/2.66  #BackRed      : 10
% 7.08/2.66  
% 7.08/2.66  #Partial instantiations: 0
% 7.08/2.66  #Strategies tried      : 1
% 7.08/2.66  
% 7.08/2.66  Timing (in seconds)
% 7.08/2.66  ----------------------
% 7.08/2.66  Preprocessing        : 0.32
% 7.08/2.66  Parsing              : 0.17
% 7.08/2.66  CNF conversion       : 0.02
% 7.08/2.66  Main loop            : 1.55
% 7.08/2.66  Inferencing          : 0.41
% 7.08/2.66  Reduction            : 0.81
% 7.08/2.66  Demodulation         : 0.69
% 7.08/2.66  BG Simplification    : 0.05
% 7.08/2.66  Subsumption          : 0.20
% 7.08/2.66  Abstraction          : 0.08
% 7.08/2.66  MUC search           : 0.00
% 7.08/2.66  Cooper               : 0.00
% 7.08/2.66  Total                : 1.90
% 7.08/2.66  Index Insertion      : 0.00
% 7.08/2.66  Index Deletion       : 0.00
% 7.08/2.66  Index Matching       : 0.00
% 7.08/2.66  BG Taut test         : 0.00
%------------------------------------------------------------------------------
