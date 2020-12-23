%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:40 EST 2020

% Result     : Theorem 2.31s
% Output     : CNFRefutation 2.31s
% Verified   : 
% Statistics : Number of formulae       :   55 (  70 expanded)
%              Number of leaves         :   25 (  35 expanded)
%              Depth                    :    8
%              Number of atoms          :   64 (  96 expanded)
%              Number of equality atoms :   16 (  27 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_75,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(A,k1_tarski(B)) = A
      <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => ( r2_hidden(C,A)
        | r1_tarski(A,k4_xboole_0(B,k1_tarski(C))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l2_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k4_xboole_0(B,k1_tarski(C)))
    <=> ( r2_hidden(A,B)
        & A != C ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).

tff(c_50,plain,
    ( ~ r2_hidden('#skF_5','#skF_4')
    | r2_hidden('#skF_7','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_66,plain,(
    ~ r2_hidden('#skF_5','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_30,plain,(
    ! [B_13] : r1_tarski(B_13,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_40,plain,(
    ! [A_22,B_23,C_24] :
      ( r1_tarski(A_22,k4_xboole_0(B_23,k1_tarski(C_24)))
      | r2_hidden(C_24,A_22)
      | ~ r1_tarski(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_86,plain,(
    ! [D_38,A_39,B_40] :
      ( r2_hidden(D_38,A_39)
      | ~ r2_hidden(D_38,k4_xboole_0(A_39,B_40)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_239,plain,(
    ! [A_76,B_77,B_78] :
      ( r2_hidden('#skF_1'(k4_xboole_0(A_76,B_77),B_78),A_76)
      | r1_tarski(k4_xboole_0(A_76,B_77),B_78) ) ),
    inference(resolution,[status(thm)],[c_6,c_86])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_265,plain,(
    ! [A_79,B_80] : r1_tarski(k4_xboole_0(A_79,B_80),A_79) ),
    inference(resolution,[status(thm)],[c_239,c_4])).

tff(c_26,plain,(
    ! [B_13,A_12] :
      ( B_13 = A_12
      | ~ r1_tarski(B_13,A_12)
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_269,plain,(
    ! [A_81,B_82] :
      ( k4_xboole_0(A_81,B_82) = A_81
      | ~ r1_tarski(A_81,k4_xboole_0(A_81,B_82)) ) ),
    inference(resolution,[status(thm)],[c_265,c_26])).

tff(c_273,plain,(
    ! [B_23,C_24] :
      ( k4_xboole_0(B_23,k1_tarski(C_24)) = B_23
      | r2_hidden(C_24,B_23)
      | ~ r1_tarski(B_23,B_23) ) ),
    inference(resolution,[status(thm)],[c_40,c_269])).

tff(c_318,plain,(
    ! [B_86,C_87] :
      ( k4_xboole_0(B_86,k1_tarski(C_87)) = B_86
      | r2_hidden(C_87,B_86) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_273])).

tff(c_48,plain,
    ( k4_xboole_0('#skF_4',k1_tarski('#skF_5')) != '#skF_4'
    | r2_hidden('#skF_7','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_85,plain,(
    k4_xboole_0('#skF_4',k1_tarski('#skF_5')) != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_352,plain,(
    r2_hidden('#skF_5','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_318,c_85])).

tff(c_366,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_352])).

tff(c_367,plain,(
    r2_hidden('#skF_7','#skF_6') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_368,plain,(
    k4_xboole_0('#skF_4',k1_tarski('#skF_5')) = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_52,plain,
    ( k4_xboole_0('#skF_4',k1_tarski('#skF_5')) != '#skF_4'
    | k4_xboole_0('#skF_6',k1_tarski('#skF_7')) = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_417,plain,(
    k4_xboole_0('#skF_6',k1_tarski('#skF_7')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_368,c_52])).

tff(c_44,plain,(
    ! [C_27,B_26] : ~ r2_hidden(C_27,k4_xboole_0(B_26,k1_tarski(C_27))) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_427,plain,(
    ~ r2_hidden('#skF_7','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_417,c_44])).

tff(c_432,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_367,c_427])).

tff(c_433,plain,(
    r2_hidden('#skF_7','#skF_6') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_434,plain,(
    r2_hidden('#skF_5','#skF_4') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_54,plain,
    ( ~ r2_hidden('#skF_5','#skF_4')
    | k4_xboole_0('#skF_6',k1_tarski('#skF_7')) = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_465,plain,(
    k4_xboole_0('#skF_6',k1_tarski('#skF_7')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_434,c_54])).

tff(c_472,plain,(
    ~ r2_hidden('#skF_7','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_465,c_44])).

tff(c_477,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_433,c_472])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:07:00 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.31/1.41  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.31/1.41  
% 2.31/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.31/1.42  %$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 2.31/1.42  
% 2.31/1.42  %Foreground sorts:
% 2.31/1.42  
% 2.31/1.42  
% 2.31/1.42  %Background operators:
% 2.31/1.42  
% 2.31/1.42  
% 2.31/1.42  %Foreground operators:
% 2.31/1.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.31/1.42  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.31/1.42  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.31/1.42  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.31/1.42  tff('#skF_7', type, '#skF_7': $i).
% 2.31/1.42  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.31/1.42  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.31/1.42  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.31/1.42  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.31/1.42  tff('#skF_5', type, '#skF_5': $i).
% 2.31/1.42  tff('#skF_6', type, '#skF_6': $i).
% 2.31/1.42  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.31/1.42  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.31/1.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.31/1.42  tff('#skF_4', type, '#skF_4': $i).
% 2.31/1.42  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.31/1.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.31/1.42  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.31/1.42  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.31/1.42  
% 2.31/1.43  tff(f_75, negated_conjecture, ~(![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 2.31/1.43  tff(f_48, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.31/1.43  tff(f_62, axiom, (![A, B, C]: (r1_tarski(A, B) => (r2_hidden(C, A) | r1_tarski(A, k4_xboole_0(B, k1_tarski(C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l2_zfmisc_1)).
% 2.31/1.43  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.31/1.43  tff(f_42, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 2.31/1.43  tff(f_69, axiom, (![A, B, C]: (r2_hidden(A, k4_xboole_0(B, k1_tarski(C))) <=> (r2_hidden(A, B) & ~(A = C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 2.31/1.43  tff(c_50, plain, (~r2_hidden('#skF_5', '#skF_4') | r2_hidden('#skF_7', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.31/1.43  tff(c_66, plain, (~r2_hidden('#skF_5', '#skF_4')), inference(splitLeft, [status(thm)], [c_50])).
% 2.31/1.43  tff(c_30, plain, (![B_13]: (r1_tarski(B_13, B_13))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.31/1.43  tff(c_40, plain, (![A_22, B_23, C_24]: (r1_tarski(A_22, k4_xboole_0(B_23, k1_tarski(C_24))) | r2_hidden(C_24, A_22) | ~r1_tarski(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.31/1.43  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.31/1.43  tff(c_86, plain, (![D_38, A_39, B_40]: (r2_hidden(D_38, A_39) | ~r2_hidden(D_38, k4_xboole_0(A_39, B_40)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.31/1.43  tff(c_239, plain, (![A_76, B_77, B_78]: (r2_hidden('#skF_1'(k4_xboole_0(A_76, B_77), B_78), A_76) | r1_tarski(k4_xboole_0(A_76, B_77), B_78))), inference(resolution, [status(thm)], [c_6, c_86])).
% 2.31/1.43  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.31/1.43  tff(c_265, plain, (![A_79, B_80]: (r1_tarski(k4_xboole_0(A_79, B_80), A_79))), inference(resolution, [status(thm)], [c_239, c_4])).
% 2.31/1.43  tff(c_26, plain, (![B_13, A_12]: (B_13=A_12 | ~r1_tarski(B_13, A_12) | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.31/1.43  tff(c_269, plain, (![A_81, B_82]: (k4_xboole_0(A_81, B_82)=A_81 | ~r1_tarski(A_81, k4_xboole_0(A_81, B_82)))), inference(resolution, [status(thm)], [c_265, c_26])).
% 2.31/1.43  tff(c_273, plain, (![B_23, C_24]: (k4_xboole_0(B_23, k1_tarski(C_24))=B_23 | r2_hidden(C_24, B_23) | ~r1_tarski(B_23, B_23))), inference(resolution, [status(thm)], [c_40, c_269])).
% 2.31/1.43  tff(c_318, plain, (![B_86, C_87]: (k4_xboole_0(B_86, k1_tarski(C_87))=B_86 | r2_hidden(C_87, B_86))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_273])).
% 2.31/1.43  tff(c_48, plain, (k4_xboole_0('#skF_4', k1_tarski('#skF_5'))!='#skF_4' | r2_hidden('#skF_7', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.31/1.43  tff(c_85, plain, (k4_xboole_0('#skF_4', k1_tarski('#skF_5'))!='#skF_4'), inference(splitLeft, [status(thm)], [c_48])).
% 2.31/1.43  tff(c_352, plain, (r2_hidden('#skF_5', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_318, c_85])).
% 2.31/1.43  tff(c_366, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_352])).
% 2.31/1.43  tff(c_367, plain, (r2_hidden('#skF_7', '#skF_6')), inference(splitRight, [status(thm)], [c_48])).
% 2.31/1.43  tff(c_368, plain, (k4_xboole_0('#skF_4', k1_tarski('#skF_5'))='#skF_4'), inference(splitRight, [status(thm)], [c_48])).
% 2.31/1.43  tff(c_52, plain, (k4_xboole_0('#skF_4', k1_tarski('#skF_5'))!='#skF_4' | k4_xboole_0('#skF_6', k1_tarski('#skF_7'))='#skF_6'), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.31/1.43  tff(c_417, plain, (k4_xboole_0('#skF_6', k1_tarski('#skF_7'))='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_368, c_52])).
% 2.31/1.43  tff(c_44, plain, (![C_27, B_26]: (~r2_hidden(C_27, k4_xboole_0(B_26, k1_tarski(C_27))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.31/1.43  tff(c_427, plain, (~r2_hidden('#skF_7', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_417, c_44])).
% 2.31/1.43  tff(c_432, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_367, c_427])).
% 2.31/1.43  tff(c_433, plain, (r2_hidden('#skF_7', '#skF_6')), inference(splitRight, [status(thm)], [c_50])).
% 2.31/1.43  tff(c_434, plain, (r2_hidden('#skF_5', '#skF_4')), inference(splitRight, [status(thm)], [c_50])).
% 2.31/1.43  tff(c_54, plain, (~r2_hidden('#skF_5', '#skF_4') | k4_xboole_0('#skF_6', k1_tarski('#skF_7'))='#skF_6'), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.31/1.43  tff(c_465, plain, (k4_xboole_0('#skF_6', k1_tarski('#skF_7'))='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_434, c_54])).
% 2.31/1.43  tff(c_472, plain, (~r2_hidden('#skF_7', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_465, c_44])).
% 2.31/1.43  tff(c_477, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_433, c_472])).
% 2.31/1.43  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.31/1.43  
% 2.31/1.43  Inference rules
% 2.31/1.43  ----------------------
% 2.31/1.43  #Ref     : 0
% 2.31/1.43  #Sup     : 95
% 2.31/1.43  #Fact    : 0
% 2.31/1.43  #Define  : 0
% 2.31/1.43  #Split   : 2
% 2.31/1.43  #Chain   : 0
% 2.31/1.43  #Close   : 0
% 2.31/1.43  
% 2.31/1.43  Ordering : KBO
% 2.31/1.43  
% 2.31/1.43  Simplification rules
% 2.31/1.43  ----------------------
% 2.31/1.43  #Subsume      : 12
% 2.31/1.43  #Demod        : 13
% 2.31/1.43  #Tautology    : 39
% 2.31/1.43  #SimpNegUnit  : 1
% 2.31/1.43  #BackRed      : 0
% 2.31/1.43  
% 2.31/1.43  #Partial instantiations: 0
% 2.31/1.43  #Strategies tried      : 1
% 2.31/1.43  
% 2.31/1.43  Timing (in seconds)
% 2.31/1.43  ----------------------
% 2.31/1.43  Preprocessing        : 0.34
% 2.31/1.43  Parsing              : 0.18
% 2.31/1.43  CNF conversion       : 0.03
% 2.31/1.43  Main loop            : 0.24
% 2.31/1.43  Inferencing          : 0.09
% 2.31/1.43  Reduction            : 0.06
% 2.31/1.43  Demodulation         : 0.04
% 2.31/1.43  BG Simplification    : 0.02
% 2.31/1.43  Subsumption          : 0.05
% 2.31/1.43  Abstraction          : 0.02
% 2.31/1.43  MUC search           : 0.00
% 2.31/1.43  Cooper               : 0.00
% 2.31/1.43  Total                : 0.61
% 2.31/1.43  Index Insertion      : 0.00
% 2.31/1.43  Index Deletion       : 0.00
% 2.31/1.43  Index Matching       : 0.00
% 2.31/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
