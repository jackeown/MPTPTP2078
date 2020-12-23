%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:41 EST 2020

% Result     : Theorem 3.99s
% Output     : CNFRefutation 4.24s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 118 expanded)
%              Number of leaves         :   33 (  54 expanded)
%              Depth                    :   14
%              Number of atoms          :   98 ( 170 expanded)
%              Number of equality atoms :   45 (  77 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_4 > #skF_3 > #skF_1

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_93,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(A,k1_tarski(B)) = A
      <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_51,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_47,axiom,(
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

tff(f_70,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_72,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_68,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_49,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(c_58,plain,
    ( k4_xboole_0('#skF_4',k1_tarski('#skF_5')) != '#skF_4'
    | r2_hidden('#skF_7','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_93,plain,(
    k4_xboole_0('#skF_4',k1_tarski('#skF_5')) != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_14,plain,(
    ! [A_10] : k5_xboole_0(A_10,k1_xboole_0) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_60,plain,
    ( ~ r2_hidden('#skF_5','#skF_4')
    | r2_hidden('#skF_7','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_87,plain,(
    ~ r2_hidden('#skF_5','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),B_4)
      | r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_42,plain,(
    ! [A_20] : k2_tarski(A_20,A_20) = k1_tarski(A_20) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_44,plain,(
    ! [A_21,B_22] : k1_enumset1(A_21,A_21,B_22) = k2_tarski(A_21,B_22) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_355,plain,(
    ! [E_121,C_122,B_123,A_124] :
      ( E_121 = C_122
      | E_121 = B_123
      | E_121 = A_124
      | ~ r2_hidden(E_121,k1_enumset1(A_124,B_123,C_122)) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_592,plain,(
    ! [E_195,B_196,A_197] :
      ( E_195 = B_196
      | E_195 = A_197
      | E_195 = A_197
      | ~ r2_hidden(E_195,k2_tarski(A_197,B_196)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_355])).

tff(c_617,plain,(
    ! [E_202,A_203] :
      ( E_202 = A_203
      | E_202 = A_203
      | E_202 = A_203
      | ~ r2_hidden(E_202,k1_tarski(A_203)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_592])).

tff(c_641,plain,(
    ! [A_206,A_207] :
      ( '#skF_1'(A_206,k1_tarski(A_207)) = A_207
      | r1_xboole_0(A_206,k1_tarski(A_207)) ) ),
    inference(resolution,[status(thm)],[c_8,c_617])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_703,plain,(
    ! [A_214,A_215] :
      ( k3_xboole_0(A_214,k1_tarski(A_215)) = k1_xboole_0
      | '#skF_1'(A_214,k1_tarski(A_215)) = A_215 ) ),
    inference(resolution,[status(thm)],[c_641,c_2])).

tff(c_12,plain,(
    ! [A_8,B_9] : k5_xboole_0(A_8,k3_xboole_0(A_8,B_9)) = k4_xboole_0(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_720,plain,(
    ! [A_214,A_215] :
      ( k4_xboole_0(A_214,k1_tarski(A_215)) = k5_xboole_0(A_214,k1_xboole_0)
      | '#skF_1'(A_214,k1_tarski(A_215)) = A_215 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_703,c_12])).

tff(c_790,plain,(
    ! [A_220,A_221] :
      ( k4_xboole_0(A_220,k1_tarski(A_221)) = A_220
      | '#skF_1'(A_220,k1_tarski(A_221)) = A_221 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_720])).

tff(c_835,plain,(
    '#skF_1'('#skF_4',k1_tarski('#skF_5')) = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_790,c_93])).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),A_3)
      | r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_846,plain,
    ( r2_hidden('#skF_5','#skF_4')
    | r1_xboole_0('#skF_4',k1_tarski('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_835,c_10])).

tff(c_855,plain,(
    r1_xboole_0('#skF_4',k1_tarski('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_87,c_846])).

tff(c_864,plain,(
    k3_xboole_0('#skF_4',k1_tarski('#skF_5')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_855,c_2])).

tff(c_874,plain,(
    k4_xboole_0('#skF_4',k1_tarski('#skF_5')) = k5_xboole_0('#skF_4',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_864,c_12])).

tff(c_883,plain,(
    k4_xboole_0('#skF_4',k1_tarski('#skF_5')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_874])).

tff(c_885,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_93,c_883])).

tff(c_886,plain,(
    r2_hidden('#skF_7','#skF_6') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_919,plain,(
    ! [A_230,B_231] : k1_enumset1(A_230,A_230,B_231) = k2_tarski(A_230,B_231) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_20,plain,(
    ! [E_19,A_13,B_14] : r2_hidden(E_19,k1_enumset1(A_13,B_14,E_19)) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_937,plain,(
    ! [B_232,A_233] : r2_hidden(B_232,k2_tarski(A_233,B_232)) ),
    inference(superposition,[status(thm),theory(equality)],[c_919,c_20])).

tff(c_940,plain,(
    ! [A_20] : r2_hidden(A_20,k1_tarski(A_20)) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_937])).

tff(c_887,plain,(
    k4_xboole_0('#skF_4',k1_tarski('#skF_5')) = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_62,plain,
    ( k4_xboole_0('#skF_4',k1_tarski('#skF_5')) != '#skF_4'
    | k4_xboole_0('#skF_6',k1_tarski('#skF_7')) = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_943,plain,(
    k4_xboole_0('#skF_6',k1_tarski('#skF_7')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_887,c_62])).

tff(c_16,plain,(
    ! [A_11,B_12] : r1_xboole_0(k4_xboole_0(A_11,B_12),B_12) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_950,plain,(
    r1_xboole_0('#skF_6',k1_tarski('#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_943,c_16])).

tff(c_997,plain,(
    ! [A_245,B_246,C_247] :
      ( ~ r1_xboole_0(A_245,B_246)
      | ~ r2_hidden(C_247,B_246)
      | ~ r2_hidden(C_247,A_245) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1013,plain,(
    ! [C_248] :
      ( ~ r2_hidden(C_248,k1_tarski('#skF_7'))
      | ~ r2_hidden(C_248,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_950,c_997])).

tff(c_1025,plain,(
    ~ r2_hidden('#skF_7','#skF_6') ),
    inference(resolution,[status(thm)],[c_940,c_1013])).

tff(c_1031,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_886,c_1025])).

tff(c_1032,plain,(
    r2_hidden('#skF_7','#skF_6') ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_1046,plain,(
    ! [A_253,B_254] : k1_enumset1(A_253,A_253,B_254) = k2_tarski(A_253,B_254) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1064,plain,(
    ! [B_255,A_256] : r2_hidden(B_255,k2_tarski(A_256,B_255)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1046,c_20])).

tff(c_1067,plain,(
    ! [A_20] : r2_hidden(A_20,k1_tarski(A_20)) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_1064])).

tff(c_1033,plain,(
    r2_hidden('#skF_5','#skF_4') ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_64,plain,
    ( ~ r2_hidden('#skF_5','#skF_4')
    | k4_xboole_0('#skF_6',k1_tarski('#skF_7')) = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_1101,plain,(
    k4_xboole_0('#skF_6',k1_tarski('#skF_7')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1033,c_64])).

tff(c_1108,plain,(
    r1_xboole_0('#skF_6',k1_tarski('#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1101,c_16])).

tff(c_1169,plain,(
    ! [A_274,B_275,C_276] :
      ( ~ r1_xboole_0(A_274,B_275)
      | ~ r2_hidden(C_276,B_275)
      | ~ r2_hidden(C_276,A_274) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1182,plain,(
    ! [C_277] :
      ( ~ r2_hidden(C_277,k1_tarski('#skF_7'))
      | ~ r2_hidden(C_277,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_1108,c_1169])).

tff(c_1194,plain,(
    ~ r2_hidden('#skF_7','#skF_6') ),
    inference(resolution,[status(thm)],[c_1067,c_1182])).

tff(c_1200,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1032,c_1194])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:01:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.99/2.23  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.24/2.24  
% 4.24/2.24  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.24/2.24  %$ r2_hidden > r1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_4 > #skF_3 > #skF_1
% 4.24/2.24  
% 4.24/2.24  %Foreground sorts:
% 4.24/2.24  
% 4.24/2.24  
% 4.24/2.24  %Background operators:
% 4.24/2.24  
% 4.24/2.24  
% 4.24/2.24  %Foreground operators:
% 4.24/2.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.24/2.24  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.24/2.24  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.24/2.24  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.24/2.24  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.24/2.24  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.24/2.24  tff('#skF_7', type, '#skF_7': $i).
% 4.24/2.24  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.24/2.24  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.24/2.24  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.24/2.24  tff('#skF_5', type, '#skF_5': $i).
% 4.24/2.24  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 4.24/2.24  tff('#skF_6', type, '#skF_6': $i).
% 4.24/2.24  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.24/2.24  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.24/2.24  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.24/2.24  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 4.24/2.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.24/2.24  tff('#skF_4', type, '#skF_4': $i).
% 4.24/2.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.24/2.24  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.24/2.24  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 4.24/2.24  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 4.24/2.24  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.24/2.24  
% 4.24/2.26  tff(f_93, negated_conjecture, ~(![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 4.24/2.26  tff(f_51, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 4.24/2.26  tff(f_47, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 4.24/2.26  tff(f_70, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 4.24/2.26  tff(f_72, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 4.24/2.26  tff(f_68, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 4.24/2.26  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 4.24/2.26  tff(f_49, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 4.24/2.26  tff(f_53, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 4.24/2.26  tff(c_58, plain, (k4_xboole_0('#skF_4', k1_tarski('#skF_5'))!='#skF_4' | r2_hidden('#skF_7', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_93])).
% 4.24/2.26  tff(c_93, plain, (k4_xboole_0('#skF_4', k1_tarski('#skF_5'))!='#skF_4'), inference(splitLeft, [status(thm)], [c_58])).
% 4.24/2.26  tff(c_14, plain, (![A_10]: (k5_xboole_0(A_10, k1_xboole_0)=A_10)), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.24/2.26  tff(c_60, plain, (~r2_hidden('#skF_5', '#skF_4') | r2_hidden('#skF_7', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_93])).
% 4.24/2.26  tff(c_87, plain, (~r2_hidden('#skF_5', '#skF_4')), inference(splitLeft, [status(thm)], [c_60])).
% 4.24/2.26  tff(c_8, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), B_4) | r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.24/2.26  tff(c_42, plain, (![A_20]: (k2_tarski(A_20, A_20)=k1_tarski(A_20))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.24/2.26  tff(c_44, plain, (![A_21, B_22]: (k1_enumset1(A_21, A_21, B_22)=k2_tarski(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.24/2.26  tff(c_355, plain, (![E_121, C_122, B_123, A_124]: (E_121=C_122 | E_121=B_123 | E_121=A_124 | ~r2_hidden(E_121, k1_enumset1(A_124, B_123, C_122)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.24/2.26  tff(c_592, plain, (![E_195, B_196, A_197]: (E_195=B_196 | E_195=A_197 | E_195=A_197 | ~r2_hidden(E_195, k2_tarski(A_197, B_196)))), inference(superposition, [status(thm), theory('equality')], [c_44, c_355])).
% 4.24/2.26  tff(c_617, plain, (![E_202, A_203]: (E_202=A_203 | E_202=A_203 | E_202=A_203 | ~r2_hidden(E_202, k1_tarski(A_203)))), inference(superposition, [status(thm), theory('equality')], [c_42, c_592])).
% 4.24/2.26  tff(c_641, plain, (![A_206, A_207]: ('#skF_1'(A_206, k1_tarski(A_207))=A_207 | r1_xboole_0(A_206, k1_tarski(A_207)))), inference(resolution, [status(thm)], [c_8, c_617])).
% 4.24/2.26  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.24/2.26  tff(c_703, plain, (![A_214, A_215]: (k3_xboole_0(A_214, k1_tarski(A_215))=k1_xboole_0 | '#skF_1'(A_214, k1_tarski(A_215))=A_215)), inference(resolution, [status(thm)], [c_641, c_2])).
% 4.24/2.26  tff(c_12, plain, (![A_8, B_9]: (k5_xboole_0(A_8, k3_xboole_0(A_8, B_9))=k4_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.24/2.26  tff(c_720, plain, (![A_214, A_215]: (k4_xboole_0(A_214, k1_tarski(A_215))=k5_xboole_0(A_214, k1_xboole_0) | '#skF_1'(A_214, k1_tarski(A_215))=A_215)), inference(superposition, [status(thm), theory('equality')], [c_703, c_12])).
% 4.24/2.26  tff(c_790, plain, (![A_220, A_221]: (k4_xboole_0(A_220, k1_tarski(A_221))=A_220 | '#skF_1'(A_220, k1_tarski(A_221))=A_221)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_720])).
% 4.24/2.26  tff(c_835, plain, ('#skF_1'('#skF_4', k1_tarski('#skF_5'))='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_790, c_93])).
% 4.24/2.26  tff(c_10, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), A_3) | r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.24/2.26  tff(c_846, plain, (r2_hidden('#skF_5', '#skF_4') | r1_xboole_0('#skF_4', k1_tarski('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_835, c_10])).
% 4.24/2.26  tff(c_855, plain, (r1_xboole_0('#skF_4', k1_tarski('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_87, c_846])).
% 4.24/2.26  tff(c_864, plain, (k3_xboole_0('#skF_4', k1_tarski('#skF_5'))=k1_xboole_0), inference(resolution, [status(thm)], [c_855, c_2])).
% 4.24/2.26  tff(c_874, plain, (k4_xboole_0('#skF_4', k1_tarski('#skF_5'))=k5_xboole_0('#skF_4', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_864, c_12])).
% 4.24/2.26  tff(c_883, plain, (k4_xboole_0('#skF_4', k1_tarski('#skF_5'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_14, c_874])).
% 4.24/2.26  tff(c_885, plain, $false, inference(negUnitSimplification, [status(thm)], [c_93, c_883])).
% 4.24/2.26  tff(c_886, plain, (r2_hidden('#skF_7', '#skF_6')), inference(splitRight, [status(thm)], [c_58])).
% 4.24/2.26  tff(c_919, plain, (![A_230, B_231]: (k1_enumset1(A_230, A_230, B_231)=k2_tarski(A_230, B_231))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.24/2.26  tff(c_20, plain, (![E_19, A_13, B_14]: (r2_hidden(E_19, k1_enumset1(A_13, B_14, E_19)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.24/2.26  tff(c_937, plain, (![B_232, A_233]: (r2_hidden(B_232, k2_tarski(A_233, B_232)))), inference(superposition, [status(thm), theory('equality')], [c_919, c_20])).
% 4.24/2.26  tff(c_940, plain, (![A_20]: (r2_hidden(A_20, k1_tarski(A_20)))), inference(superposition, [status(thm), theory('equality')], [c_42, c_937])).
% 4.24/2.26  tff(c_887, plain, (k4_xboole_0('#skF_4', k1_tarski('#skF_5'))='#skF_4'), inference(splitRight, [status(thm)], [c_58])).
% 4.24/2.26  tff(c_62, plain, (k4_xboole_0('#skF_4', k1_tarski('#skF_5'))!='#skF_4' | k4_xboole_0('#skF_6', k1_tarski('#skF_7'))='#skF_6'), inference(cnfTransformation, [status(thm)], [f_93])).
% 4.24/2.26  tff(c_943, plain, (k4_xboole_0('#skF_6', k1_tarski('#skF_7'))='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_887, c_62])).
% 4.24/2.26  tff(c_16, plain, (![A_11, B_12]: (r1_xboole_0(k4_xboole_0(A_11, B_12), B_12))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.24/2.26  tff(c_950, plain, (r1_xboole_0('#skF_6', k1_tarski('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_943, c_16])).
% 4.24/2.26  tff(c_997, plain, (![A_245, B_246, C_247]: (~r1_xboole_0(A_245, B_246) | ~r2_hidden(C_247, B_246) | ~r2_hidden(C_247, A_245))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.24/2.26  tff(c_1013, plain, (![C_248]: (~r2_hidden(C_248, k1_tarski('#skF_7')) | ~r2_hidden(C_248, '#skF_6'))), inference(resolution, [status(thm)], [c_950, c_997])).
% 4.24/2.26  tff(c_1025, plain, (~r2_hidden('#skF_7', '#skF_6')), inference(resolution, [status(thm)], [c_940, c_1013])).
% 4.24/2.26  tff(c_1031, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_886, c_1025])).
% 4.24/2.26  tff(c_1032, plain, (r2_hidden('#skF_7', '#skF_6')), inference(splitRight, [status(thm)], [c_60])).
% 4.24/2.26  tff(c_1046, plain, (![A_253, B_254]: (k1_enumset1(A_253, A_253, B_254)=k2_tarski(A_253, B_254))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.24/2.26  tff(c_1064, plain, (![B_255, A_256]: (r2_hidden(B_255, k2_tarski(A_256, B_255)))), inference(superposition, [status(thm), theory('equality')], [c_1046, c_20])).
% 4.24/2.26  tff(c_1067, plain, (![A_20]: (r2_hidden(A_20, k1_tarski(A_20)))), inference(superposition, [status(thm), theory('equality')], [c_42, c_1064])).
% 4.24/2.26  tff(c_1033, plain, (r2_hidden('#skF_5', '#skF_4')), inference(splitRight, [status(thm)], [c_60])).
% 4.24/2.26  tff(c_64, plain, (~r2_hidden('#skF_5', '#skF_4') | k4_xboole_0('#skF_6', k1_tarski('#skF_7'))='#skF_6'), inference(cnfTransformation, [status(thm)], [f_93])).
% 4.24/2.26  tff(c_1101, plain, (k4_xboole_0('#skF_6', k1_tarski('#skF_7'))='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_1033, c_64])).
% 4.24/2.26  tff(c_1108, plain, (r1_xboole_0('#skF_6', k1_tarski('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_1101, c_16])).
% 4.24/2.26  tff(c_1169, plain, (![A_274, B_275, C_276]: (~r1_xboole_0(A_274, B_275) | ~r2_hidden(C_276, B_275) | ~r2_hidden(C_276, A_274))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.24/2.26  tff(c_1182, plain, (![C_277]: (~r2_hidden(C_277, k1_tarski('#skF_7')) | ~r2_hidden(C_277, '#skF_6'))), inference(resolution, [status(thm)], [c_1108, c_1169])).
% 4.24/2.26  tff(c_1194, plain, (~r2_hidden('#skF_7', '#skF_6')), inference(resolution, [status(thm)], [c_1067, c_1182])).
% 4.24/2.26  tff(c_1200, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1032, c_1194])).
% 4.24/2.26  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.24/2.26  
% 4.24/2.26  Inference rules
% 4.24/2.27  ----------------------
% 4.24/2.27  #Ref     : 0
% 4.24/2.27  #Sup     : 271
% 4.24/2.27  #Fact    : 0
% 4.24/2.27  #Define  : 0
% 4.24/2.27  #Split   : 2
% 4.24/2.27  #Chain   : 0
% 4.24/2.27  #Close   : 0
% 4.24/2.27  
% 4.24/2.27  Ordering : KBO
% 4.24/2.27  
% 4.24/2.27  Simplification rules
% 4.24/2.27  ----------------------
% 4.24/2.27  #Subsume      : 42
% 4.24/2.27  #Demod        : 53
% 4.24/2.27  #Tautology    : 124
% 4.24/2.27  #SimpNegUnit  : 2
% 4.24/2.27  #BackRed      : 0
% 4.24/2.27  
% 4.24/2.27  #Partial instantiations: 0
% 4.24/2.27  #Strategies tried      : 1
% 4.24/2.27  
% 4.24/2.27  Timing (in seconds)
% 4.24/2.27  ----------------------
% 4.24/2.27  Preprocessing        : 0.57
% 4.24/2.27  Parsing              : 0.28
% 4.24/2.27  CNF conversion       : 0.05
% 4.24/2.27  Main loop            : 0.72
% 4.24/2.27  Inferencing          : 0.28
% 4.24/2.27  Reduction            : 0.21
% 4.24/2.27  Demodulation         : 0.15
% 4.24/2.27  BG Simplification    : 0.04
% 4.24/2.27  Subsumption          : 0.12
% 4.24/2.27  Abstraction          : 0.04
% 4.24/2.27  MUC search           : 0.00
% 4.24/2.27  Cooper               : 0.00
% 4.24/2.27  Total                : 1.35
% 4.24/2.27  Index Insertion      : 0.00
% 4.24/2.27  Index Deletion       : 0.00
% 4.24/2.27  Index Matching       : 0.00
% 4.24/2.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
