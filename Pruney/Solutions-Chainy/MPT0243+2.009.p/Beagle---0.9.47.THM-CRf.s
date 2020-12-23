%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:55 EST 2020

% Result     : Theorem 2.87s
% Output     : CNFRefutation 2.87s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 159 expanded)
%              Number of leaves         :   25 (  59 expanded)
%              Depth                    :    8
%              Number of atoms          :   98 ( 285 expanded)
%              Number of equality atoms :    8 (  20 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_9 > #skF_8 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_70,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(k2_tarski(A,B),C)
      <=> ( r2_hidden(A,C)
          & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_59,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_53,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_63,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_55,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_38,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).

tff(c_46,plain,
    ( r2_hidden('#skF_5','#skF_6')
    | ~ r2_hidden('#skF_8','#skF_9')
    | ~ r2_hidden('#skF_7','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_149,plain,(
    ~ r2_hidden('#skF_7','#skF_9') ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_52,plain,
    ( r2_hidden('#skF_5','#skF_6')
    | r1_tarski(k2_tarski('#skF_7','#skF_8'),'#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_96,plain,(
    r1_tarski(k2_tarski('#skF_7','#skF_8'),'#skF_9') ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_67,plain,(
    ! [A_33,B_34] : k1_enumset1(A_33,A_33,B_34) = k2_tarski(A_33,B_34) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_16,plain,(
    ! [E_15,B_10,C_11] : r2_hidden(E_15,k1_enumset1(E_15,B_10,C_11)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_79,plain,(
    ! [A_33,B_34] : r2_hidden(A_33,k2_tarski(A_33,B_34)) ),
    inference(superposition,[status(thm),theory(equality)],[c_67,c_16])).

tff(c_127,plain,(
    ! [C_51,B_52,A_53] :
      ( r2_hidden(C_51,B_52)
      | ~ r2_hidden(C_51,A_53)
      | ~ r1_tarski(A_53,B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_150,plain,(
    ! [A_54,B_55,B_56] :
      ( r2_hidden(A_54,B_55)
      | ~ r1_tarski(k2_tarski(A_54,B_56),B_55) ) ),
    inference(resolution,[status(thm)],[c_79,c_127])).

tff(c_157,plain,(
    r2_hidden('#skF_7','#skF_9') ),
    inference(resolution,[status(thm)],[c_96,c_150])).

tff(c_166,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_149,c_157])).

tff(c_167,plain,
    ( ~ r2_hidden('#skF_8','#skF_9')
    | r2_hidden('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_172,plain,(
    ~ r2_hidden('#skF_8','#skF_9') ),
    inference(splitLeft,[status(thm)],[c_167])).

tff(c_12,plain,(
    ! [E_15,A_9,B_10] : r2_hidden(E_15,k1_enumset1(A_9,B_10,E_15)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_73,plain,(
    ! [B_34,A_33] : r2_hidden(B_34,k2_tarski(A_33,B_34)) ),
    inference(superposition,[status(thm),theory(equality)],[c_67,c_12])).

tff(c_179,plain,(
    ! [B_58,B_59,A_60] :
      ( r2_hidden(B_58,B_59)
      | ~ r1_tarski(k2_tarski(A_60,B_58),B_59) ) ),
    inference(resolution,[status(thm)],[c_73,c_127])).

tff(c_186,plain,(
    r2_hidden('#skF_8','#skF_9') ),
    inference(resolution,[status(thm)],[c_96,c_179])).

tff(c_195,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_172,c_186])).

tff(c_196,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_167])).

tff(c_42,plain,(
    ! [A_21,B_22] :
      ( r1_tarski(k1_tarski(A_21),B_22)
      | ~ r2_hidden(A_21,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_197,plain,(
    r2_hidden('#skF_8','#skF_9') ),
    inference(splitRight,[status(thm)],[c_167])).

tff(c_168,plain,(
    r2_hidden('#skF_7','#skF_9') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_48,plain,
    ( r2_hidden('#skF_4','#skF_6')
    | ~ r2_hidden('#skF_8','#skF_9')
    | ~ r2_hidden('#skF_7','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_202,plain,
    ( r2_hidden('#skF_4','#skF_6')
    | ~ r2_hidden('#skF_8','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_168,c_48])).

tff(c_203,plain,(
    ~ r2_hidden('#skF_8','#skF_9') ),
    inference(splitLeft,[status(thm)],[c_202])).

tff(c_208,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_197,c_203])).

tff(c_209,plain,(
    r2_hidden('#skF_4','#skF_6') ),
    inference(splitRight,[status(thm)],[c_202])).

tff(c_34,plain,(
    ! [A_16,B_17] : k2_xboole_0(k1_tarski(A_16),k1_tarski(B_17)) = k2_tarski(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_287,plain,(
    ! [A_79,C_80,B_81] :
      ( r1_tarski(k2_xboole_0(A_79,C_80),B_81)
      | ~ r1_tarski(C_80,B_81)
      | ~ r1_tarski(A_79,B_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_593,plain,(
    ! [A_161,B_162,B_163] :
      ( r1_tarski(k2_tarski(A_161,B_162),B_163)
      | ~ r1_tarski(k1_tarski(B_162),B_163)
      | ~ r1_tarski(k1_tarski(A_161),B_163) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_287])).

tff(c_44,plain,
    ( ~ r1_tarski(k2_tarski('#skF_4','#skF_5'),'#skF_6')
    | ~ r2_hidden('#skF_8','#skF_9')
    | ~ r2_hidden('#skF_7','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_232,plain,(
    ~ r1_tarski(k2_tarski('#skF_4','#skF_5'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_168,c_197,c_44])).

tff(c_624,plain,
    ( ~ r1_tarski(k1_tarski('#skF_5'),'#skF_6')
    | ~ r1_tarski(k1_tarski('#skF_4'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_593,c_232])).

tff(c_625,plain,(
    ~ r1_tarski(k1_tarski('#skF_4'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_624])).

tff(c_631,plain,(
    ~ r2_hidden('#skF_4','#skF_6') ),
    inference(resolution,[status(thm)],[c_42,c_625])).

tff(c_636,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_209,c_631])).

tff(c_637,plain,(
    ~ r1_tarski(k1_tarski('#skF_5'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_624])).

tff(c_645,plain,(
    ~ r2_hidden('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_42,c_637])).

tff(c_650,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_196,c_645])).

tff(c_651,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_652,plain,(
    ~ r1_tarski(k2_tarski('#skF_7','#skF_8'),'#skF_9') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_54,plain,
    ( r2_hidden('#skF_4','#skF_6')
    | r1_tarski(k2_tarski('#skF_7','#skF_8'),'#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_653,plain,(
    r2_hidden('#skF_4','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_652,c_54])).

tff(c_788,plain,(
    ! [A_208,C_209,B_210] :
      ( r1_tarski(k2_xboole_0(A_208,C_209),B_210)
      | ~ r1_tarski(C_209,B_210)
      | ~ r1_tarski(A_208,B_210) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_975,plain,(
    ! [A_254,B_255,B_256] :
      ( r1_tarski(k2_tarski(A_254,B_255),B_256)
      | ~ r1_tarski(k1_tarski(B_255),B_256)
      | ~ r1_tarski(k1_tarski(A_254),B_256) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_788])).

tff(c_50,plain,
    ( ~ r1_tarski(k2_tarski('#skF_4','#skF_5'),'#skF_6')
    | r1_tarski(k2_tarski('#skF_7','#skF_8'),'#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_761,plain,(
    ~ r1_tarski(k2_tarski('#skF_4','#skF_5'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_652,c_50])).

tff(c_1001,plain,
    ( ~ r1_tarski(k1_tarski('#skF_5'),'#skF_6')
    | ~ r1_tarski(k1_tarski('#skF_4'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_975,c_761])).

tff(c_1005,plain,(
    ~ r1_tarski(k1_tarski('#skF_4'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_1001])).

tff(c_1011,plain,(
    ~ r2_hidden('#skF_4','#skF_6') ),
    inference(resolution,[status(thm)],[c_42,c_1005])).

tff(c_1016,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_653,c_1011])).

tff(c_1017,plain,(
    ~ r1_tarski(k1_tarski('#skF_5'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_1001])).

tff(c_1024,plain,(
    ~ r2_hidden('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_42,c_1017])).

tff(c_1029,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_651,c_1024])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.08  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.08  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.07/0.27  % Computer   : n011.cluster.edu
% 0.07/0.27  % Model      : x86_64 x86_64
% 0.07/0.27  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.07/0.27  % Memory     : 8042.1875MB
% 0.07/0.27  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.07/0.27  % CPULimit   : 60
% 0.07/0.27  % DateTime   : Tue Dec  1 15:16:42 EST 2020
% 0.07/0.27  % CPUTime    : 
% 0.07/0.27  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.87/1.39  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.87/1.39  
% 2.87/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.87/1.40  %$ r2_hidden > r1_tarski > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_9 > #skF_8 > #skF_4 > #skF_3 > #skF_1
% 2.87/1.40  
% 2.87/1.40  %Foreground sorts:
% 2.87/1.40  
% 2.87/1.40  
% 2.87/1.40  %Background operators:
% 2.87/1.40  
% 2.87/1.40  
% 2.87/1.40  %Foreground operators:
% 2.87/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.87/1.40  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.87/1.40  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.87/1.40  tff('#skF_7', type, '#skF_7': $i).
% 2.87/1.40  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.87/1.40  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.87/1.40  tff('#skF_5', type, '#skF_5': $i).
% 2.87/1.40  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.87/1.40  tff('#skF_6', type, '#skF_6': $i).
% 2.87/1.40  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.87/1.40  tff('#skF_9', type, '#skF_9': $i).
% 2.87/1.40  tff('#skF_8', type, '#skF_8': $i).
% 2.87/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.87/1.40  tff('#skF_4', type, '#skF_4': $i).
% 2.87/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.87/1.40  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 2.87/1.40  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.87/1.40  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.87/1.40  
% 2.87/1.41  tff(f_70, negated_conjecture, ~(![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 2.87/1.41  tff(f_59, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.87/1.41  tff(f_53, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 2.87/1.41  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.87/1.41  tff(f_63, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 2.87/1.41  tff(f_55, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 2.87/1.41  tff(f_38, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_xboole_1)).
% 2.87/1.41  tff(c_46, plain, (r2_hidden('#skF_5', '#skF_6') | ~r2_hidden('#skF_8', '#skF_9') | ~r2_hidden('#skF_7', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.87/1.41  tff(c_149, plain, (~r2_hidden('#skF_7', '#skF_9')), inference(splitLeft, [status(thm)], [c_46])).
% 2.87/1.41  tff(c_52, plain, (r2_hidden('#skF_5', '#skF_6') | r1_tarski(k2_tarski('#skF_7', '#skF_8'), '#skF_9')), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.87/1.41  tff(c_96, plain, (r1_tarski(k2_tarski('#skF_7', '#skF_8'), '#skF_9')), inference(splitLeft, [status(thm)], [c_52])).
% 2.87/1.41  tff(c_67, plain, (![A_33, B_34]: (k1_enumset1(A_33, A_33, B_34)=k2_tarski(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.87/1.41  tff(c_16, plain, (![E_15, B_10, C_11]: (r2_hidden(E_15, k1_enumset1(E_15, B_10, C_11)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.87/1.41  tff(c_79, plain, (![A_33, B_34]: (r2_hidden(A_33, k2_tarski(A_33, B_34)))), inference(superposition, [status(thm), theory('equality')], [c_67, c_16])).
% 2.87/1.41  tff(c_127, plain, (![C_51, B_52, A_53]: (r2_hidden(C_51, B_52) | ~r2_hidden(C_51, A_53) | ~r1_tarski(A_53, B_52))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.87/1.41  tff(c_150, plain, (![A_54, B_55, B_56]: (r2_hidden(A_54, B_55) | ~r1_tarski(k2_tarski(A_54, B_56), B_55))), inference(resolution, [status(thm)], [c_79, c_127])).
% 2.87/1.41  tff(c_157, plain, (r2_hidden('#skF_7', '#skF_9')), inference(resolution, [status(thm)], [c_96, c_150])).
% 2.87/1.41  tff(c_166, plain, $false, inference(negUnitSimplification, [status(thm)], [c_149, c_157])).
% 2.87/1.41  tff(c_167, plain, (~r2_hidden('#skF_8', '#skF_9') | r2_hidden('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_46])).
% 2.87/1.41  tff(c_172, plain, (~r2_hidden('#skF_8', '#skF_9')), inference(splitLeft, [status(thm)], [c_167])).
% 2.87/1.41  tff(c_12, plain, (![E_15, A_9, B_10]: (r2_hidden(E_15, k1_enumset1(A_9, B_10, E_15)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.87/1.41  tff(c_73, plain, (![B_34, A_33]: (r2_hidden(B_34, k2_tarski(A_33, B_34)))), inference(superposition, [status(thm), theory('equality')], [c_67, c_12])).
% 2.87/1.41  tff(c_179, plain, (![B_58, B_59, A_60]: (r2_hidden(B_58, B_59) | ~r1_tarski(k2_tarski(A_60, B_58), B_59))), inference(resolution, [status(thm)], [c_73, c_127])).
% 2.87/1.41  tff(c_186, plain, (r2_hidden('#skF_8', '#skF_9')), inference(resolution, [status(thm)], [c_96, c_179])).
% 2.87/1.41  tff(c_195, plain, $false, inference(negUnitSimplification, [status(thm)], [c_172, c_186])).
% 2.87/1.41  tff(c_196, plain, (r2_hidden('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_167])).
% 2.87/1.41  tff(c_42, plain, (![A_21, B_22]: (r1_tarski(k1_tarski(A_21), B_22) | ~r2_hidden(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.87/1.41  tff(c_197, plain, (r2_hidden('#skF_8', '#skF_9')), inference(splitRight, [status(thm)], [c_167])).
% 2.87/1.41  tff(c_168, plain, (r2_hidden('#skF_7', '#skF_9')), inference(splitRight, [status(thm)], [c_46])).
% 2.87/1.41  tff(c_48, plain, (r2_hidden('#skF_4', '#skF_6') | ~r2_hidden('#skF_8', '#skF_9') | ~r2_hidden('#skF_7', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.87/1.41  tff(c_202, plain, (r2_hidden('#skF_4', '#skF_6') | ~r2_hidden('#skF_8', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_168, c_48])).
% 2.87/1.41  tff(c_203, plain, (~r2_hidden('#skF_8', '#skF_9')), inference(splitLeft, [status(thm)], [c_202])).
% 2.87/1.41  tff(c_208, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_197, c_203])).
% 2.87/1.41  tff(c_209, plain, (r2_hidden('#skF_4', '#skF_6')), inference(splitRight, [status(thm)], [c_202])).
% 2.87/1.41  tff(c_34, plain, (![A_16, B_17]: (k2_xboole_0(k1_tarski(A_16), k1_tarski(B_17))=k2_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.87/1.41  tff(c_287, plain, (![A_79, C_80, B_81]: (r1_tarski(k2_xboole_0(A_79, C_80), B_81) | ~r1_tarski(C_80, B_81) | ~r1_tarski(A_79, B_81))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.87/1.41  tff(c_593, plain, (![A_161, B_162, B_163]: (r1_tarski(k2_tarski(A_161, B_162), B_163) | ~r1_tarski(k1_tarski(B_162), B_163) | ~r1_tarski(k1_tarski(A_161), B_163))), inference(superposition, [status(thm), theory('equality')], [c_34, c_287])).
% 2.87/1.41  tff(c_44, plain, (~r1_tarski(k2_tarski('#skF_4', '#skF_5'), '#skF_6') | ~r2_hidden('#skF_8', '#skF_9') | ~r2_hidden('#skF_7', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.87/1.41  tff(c_232, plain, (~r1_tarski(k2_tarski('#skF_4', '#skF_5'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_168, c_197, c_44])).
% 2.87/1.41  tff(c_624, plain, (~r1_tarski(k1_tarski('#skF_5'), '#skF_6') | ~r1_tarski(k1_tarski('#skF_4'), '#skF_6')), inference(resolution, [status(thm)], [c_593, c_232])).
% 2.87/1.41  tff(c_625, plain, (~r1_tarski(k1_tarski('#skF_4'), '#skF_6')), inference(splitLeft, [status(thm)], [c_624])).
% 2.87/1.41  tff(c_631, plain, (~r2_hidden('#skF_4', '#skF_6')), inference(resolution, [status(thm)], [c_42, c_625])).
% 2.87/1.41  tff(c_636, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_209, c_631])).
% 2.87/1.41  tff(c_637, plain, (~r1_tarski(k1_tarski('#skF_5'), '#skF_6')), inference(splitRight, [status(thm)], [c_624])).
% 2.87/1.41  tff(c_645, plain, (~r2_hidden('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_42, c_637])).
% 2.87/1.41  tff(c_650, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_196, c_645])).
% 2.87/1.41  tff(c_651, plain, (r2_hidden('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_52])).
% 2.87/1.41  tff(c_652, plain, (~r1_tarski(k2_tarski('#skF_7', '#skF_8'), '#skF_9')), inference(splitRight, [status(thm)], [c_52])).
% 2.87/1.41  tff(c_54, plain, (r2_hidden('#skF_4', '#skF_6') | r1_tarski(k2_tarski('#skF_7', '#skF_8'), '#skF_9')), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.87/1.41  tff(c_653, plain, (r2_hidden('#skF_4', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_652, c_54])).
% 2.87/1.41  tff(c_788, plain, (![A_208, C_209, B_210]: (r1_tarski(k2_xboole_0(A_208, C_209), B_210) | ~r1_tarski(C_209, B_210) | ~r1_tarski(A_208, B_210))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.87/1.41  tff(c_975, plain, (![A_254, B_255, B_256]: (r1_tarski(k2_tarski(A_254, B_255), B_256) | ~r1_tarski(k1_tarski(B_255), B_256) | ~r1_tarski(k1_tarski(A_254), B_256))), inference(superposition, [status(thm), theory('equality')], [c_34, c_788])).
% 2.87/1.41  tff(c_50, plain, (~r1_tarski(k2_tarski('#skF_4', '#skF_5'), '#skF_6') | r1_tarski(k2_tarski('#skF_7', '#skF_8'), '#skF_9')), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.87/1.41  tff(c_761, plain, (~r1_tarski(k2_tarski('#skF_4', '#skF_5'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_652, c_50])).
% 2.87/1.41  tff(c_1001, plain, (~r1_tarski(k1_tarski('#skF_5'), '#skF_6') | ~r1_tarski(k1_tarski('#skF_4'), '#skF_6')), inference(resolution, [status(thm)], [c_975, c_761])).
% 2.87/1.41  tff(c_1005, plain, (~r1_tarski(k1_tarski('#skF_4'), '#skF_6')), inference(splitLeft, [status(thm)], [c_1001])).
% 2.87/1.41  tff(c_1011, plain, (~r2_hidden('#skF_4', '#skF_6')), inference(resolution, [status(thm)], [c_42, c_1005])).
% 2.87/1.41  tff(c_1016, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_653, c_1011])).
% 2.87/1.41  tff(c_1017, plain, (~r1_tarski(k1_tarski('#skF_5'), '#skF_6')), inference(splitRight, [status(thm)], [c_1001])).
% 2.87/1.41  tff(c_1024, plain, (~r2_hidden('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_42, c_1017])).
% 2.87/1.41  tff(c_1029, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_651, c_1024])).
% 2.87/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.87/1.41  
% 2.87/1.41  Inference rules
% 2.87/1.41  ----------------------
% 2.87/1.41  #Ref     : 0
% 2.87/1.41  #Sup     : 212
% 2.87/1.41  #Fact    : 0
% 2.87/1.41  #Define  : 0
% 2.87/1.41  #Split   : 7
% 2.87/1.41  #Chain   : 0
% 2.87/1.41  #Close   : 0
% 2.87/1.41  
% 2.87/1.41  Ordering : KBO
% 2.87/1.41  
% 2.87/1.41  Simplification rules
% 2.87/1.41  ----------------------
% 2.87/1.41  #Subsume      : 43
% 2.87/1.41  #Demod        : 37
% 2.87/1.41  #Tautology    : 58
% 2.87/1.41  #SimpNegUnit  : 4
% 2.87/1.41  #BackRed      : 0
% 2.87/1.41  
% 2.87/1.41  #Partial instantiations: 0
% 2.87/1.41  #Strategies tried      : 1
% 2.87/1.41  
% 2.87/1.41  Timing (in seconds)
% 2.87/1.41  ----------------------
% 2.87/1.41  Preprocessing        : 0.32
% 2.87/1.41  Parsing              : 0.16
% 2.87/1.41  CNF conversion       : 0.02
% 2.87/1.41  Main loop            : 0.41
% 2.87/1.41  Inferencing          : 0.16
% 2.87/1.41  Reduction            : 0.11
% 2.87/1.41  Demodulation         : 0.08
% 2.87/1.41  BG Simplification    : 0.02
% 2.87/1.41  Subsumption          : 0.09
% 2.87/1.41  Abstraction          : 0.02
% 2.87/1.41  MUC search           : 0.00
% 2.87/1.41  Cooper               : 0.00
% 2.87/1.41  Total                : 0.75
% 2.87/1.41  Index Insertion      : 0.00
% 2.87/1.41  Index Deletion       : 0.00
% 2.87/1.41  Index Matching       : 0.00
% 2.87/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
