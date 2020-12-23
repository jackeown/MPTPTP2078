%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:40 EST 2020

% Result     : Theorem 2.62s
% Output     : CNFRefutation 2.62s
% Verified   : 
% Statistics : Number of formulae       :   60 (  85 expanded)
%              Number of leaves         :   25 (  41 expanded)
%              Depth                    :    8
%              Number of atoms          :   70 ( 132 expanded)
%              Number of equality atoms :   24 (  45 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_2 > #skF_6 > #skF_9 > #skF_8 > #skF_3 > #skF_1 > #skF_5 > #skF_4

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

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_9',type,(
    '#skF_9': $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_83,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(A,k1_tarski(B)) = A
      <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_43,axiom,(
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

tff(f_71,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_49,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(c_56,plain,
    ( k4_xboole_0('#skF_6',k1_tarski('#skF_7')) != '#skF_6'
    | r2_hidden('#skF_9','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_127,plain,(
    k4_xboole_0('#skF_6',k1_tarski('#skF_7')) != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_58,plain,
    ( ~ r2_hidden('#skF_7','#skF_6')
    | r2_hidden('#skF_9','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_75,plain,(
    ~ r2_hidden('#skF_7','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_134,plain,(
    ! [A_55,B_56] :
      ( r2_hidden('#skF_1'(A_55,B_56),B_56)
      | r1_xboole_0(A_55,B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_38,plain,(
    ! [C_21,A_17] :
      ( C_21 = A_17
      | ~ r2_hidden(C_21,k1_tarski(A_17)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_153,plain,(
    ! [A_63,A_64] :
      ( '#skF_1'(A_63,k1_tarski(A_64)) = A_64
      | r1_xboole_0(A_63,k1_tarski(A_64)) ) ),
    inference(resolution,[status(thm)],[c_134,c_38])).

tff(c_10,plain,(
    ! [A_8,B_9] :
      ( k4_xboole_0(A_8,B_9) = A_8
      | ~ r1_xboole_0(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_234,plain,(
    ! [A_84,A_85] :
      ( k4_xboole_0(A_84,k1_tarski(A_85)) = A_84
      | '#skF_1'(A_84,k1_tarski(A_85)) = A_85 ) ),
    inference(resolution,[status(thm)],[c_153,c_10])).

tff(c_249,plain,(
    '#skF_1'('#skF_6',k1_tarski('#skF_7')) = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_234,c_127])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_257,plain,
    ( r2_hidden('#skF_7','#skF_6')
    | r1_xboole_0('#skF_6',k1_tarski('#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_249,c_6])).

tff(c_261,plain,(
    r1_xboole_0('#skF_6',k1_tarski('#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_257])).

tff(c_267,plain,(
    k4_xboole_0('#skF_6',k1_tarski('#skF_7')) = '#skF_6' ),
    inference(resolution,[status(thm)],[c_261,c_10])).

tff(c_272,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_127,c_267])).

tff(c_273,plain,(
    r2_hidden('#skF_9','#skF_8') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_274,plain,(
    k4_xboole_0('#skF_6',k1_tarski('#skF_7')) = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_60,plain,
    ( k4_xboole_0('#skF_6',k1_tarski('#skF_7')) != '#skF_6'
    | k4_xboole_0('#skF_8',k1_tarski('#skF_9')) = '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_296,plain,(
    k4_xboole_0('#skF_8',k1_tarski('#skF_9')) = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_274,c_60])).

tff(c_40,plain,(
    ! [C_21] : r2_hidden(C_21,k1_tarski(C_21)) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_12,plain,(
    ! [A_8,B_9] :
      ( r1_xboole_0(A_8,B_9)
      | k4_xboole_0(A_8,B_9) != A_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_291,plain,(
    ! [A_90,B_91,C_92] :
      ( ~ r1_xboole_0(A_90,B_91)
      | ~ r2_hidden(C_92,B_91)
      | ~ r2_hidden(C_92,A_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_326,plain,(
    ! [C_100,B_101,A_102] :
      ( ~ r2_hidden(C_100,B_101)
      | ~ r2_hidden(C_100,A_102)
      | k4_xboole_0(A_102,B_101) != A_102 ) ),
    inference(resolution,[status(thm)],[c_12,c_291])).

tff(c_390,plain,(
    ! [C_106,A_107] :
      ( ~ r2_hidden(C_106,A_107)
      | k4_xboole_0(A_107,k1_tarski(C_106)) != A_107 ) ),
    inference(resolution,[status(thm)],[c_40,c_326])).

tff(c_393,plain,(
    ~ r2_hidden('#skF_9','#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_296,c_390])).

tff(c_400,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_273,c_393])).

tff(c_401,plain,(
    r2_hidden('#skF_9','#skF_8') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_402,plain,(
    r2_hidden('#skF_7','#skF_6') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_62,plain,
    ( ~ r2_hidden('#skF_7','#skF_6')
    | k4_xboole_0('#skF_8',k1_tarski('#skF_9')) = '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_441,plain,(
    k4_xboole_0('#skF_8',k1_tarski('#skF_9')) = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_402,c_62])).

tff(c_473,plain,(
    ! [A_129,B_130,C_131] :
      ( ~ r1_xboole_0(A_129,B_130)
      | ~ r2_hidden(C_131,B_130)
      | ~ r2_hidden(C_131,A_129) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_503,plain,(
    ! [C_139,B_140,A_141] :
      ( ~ r2_hidden(C_139,B_140)
      | ~ r2_hidden(C_139,A_141)
      | k4_xboole_0(A_141,B_140) != A_141 ) ),
    inference(resolution,[status(thm)],[c_12,c_473])).

tff(c_605,plain,(
    ! [C_146,A_147] :
      ( ~ r2_hidden(C_146,A_147)
      | k4_xboole_0(A_147,k1_tarski(C_146)) != A_147 ) ),
    inference(resolution,[status(thm)],[c_40,c_503])).

tff(c_608,plain,(
    ~ r2_hidden('#skF_9','#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_441,c_605])).

tff(c_612,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_401,c_608])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n021.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:40:49 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.62/1.33  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.62/1.33  
% 2.62/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.62/1.34  %$ r2_hidden > r1_xboole_0 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_2 > #skF_6 > #skF_9 > #skF_8 > #skF_3 > #skF_1 > #skF_5 > #skF_4
% 2.62/1.34  
% 2.62/1.34  %Foreground sorts:
% 2.62/1.34  
% 2.62/1.34  
% 2.62/1.34  %Background operators:
% 2.62/1.34  
% 2.62/1.34  
% 2.62/1.34  %Foreground operators:
% 2.62/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.62/1.34  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.62/1.34  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.62/1.34  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.62/1.34  tff('#skF_7', type, '#skF_7': $i).
% 2.62/1.34  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.62/1.34  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.62/1.34  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.62/1.34  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.62/1.34  tff('#skF_6', type, '#skF_6': $i).
% 2.62/1.34  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.62/1.34  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.62/1.34  tff('#skF_9', type, '#skF_9': $i).
% 2.62/1.34  tff('#skF_8', type, '#skF_8': $i).
% 2.62/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.62/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.62/1.34  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.62/1.34  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 2.62/1.34  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.62/1.34  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 2.62/1.34  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.62/1.34  
% 2.62/1.35  tff(f_83, negated_conjecture, ~(![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 2.62/1.35  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.62/1.35  tff(f_71, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 2.62/1.35  tff(f_49, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.62/1.35  tff(c_56, plain, (k4_xboole_0('#skF_6', k1_tarski('#skF_7'))!='#skF_6' | r2_hidden('#skF_9', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.62/1.35  tff(c_127, plain, (k4_xboole_0('#skF_6', k1_tarski('#skF_7'))!='#skF_6'), inference(splitLeft, [status(thm)], [c_56])).
% 2.62/1.35  tff(c_58, plain, (~r2_hidden('#skF_7', '#skF_6') | r2_hidden('#skF_9', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.62/1.35  tff(c_75, plain, (~r2_hidden('#skF_7', '#skF_6')), inference(splitLeft, [status(thm)], [c_58])).
% 2.62/1.35  tff(c_134, plain, (![A_55, B_56]: (r2_hidden('#skF_1'(A_55, B_56), B_56) | r1_xboole_0(A_55, B_56))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.62/1.35  tff(c_38, plain, (![C_21, A_17]: (C_21=A_17 | ~r2_hidden(C_21, k1_tarski(A_17)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.62/1.35  tff(c_153, plain, (![A_63, A_64]: ('#skF_1'(A_63, k1_tarski(A_64))=A_64 | r1_xboole_0(A_63, k1_tarski(A_64)))), inference(resolution, [status(thm)], [c_134, c_38])).
% 2.62/1.35  tff(c_10, plain, (![A_8, B_9]: (k4_xboole_0(A_8, B_9)=A_8 | ~r1_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.62/1.35  tff(c_234, plain, (![A_84, A_85]: (k4_xboole_0(A_84, k1_tarski(A_85))=A_84 | '#skF_1'(A_84, k1_tarski(A_85))=A_85)), inference(resolution, [status(thm)], [c_153, c_10])).
% 2.62/1.35  tff(c_249, plain, ('#skF_1'('#skF_6', k1_tarski('#skF_7'))='#skF_7'), inference(superposition, [status(thm), theory('equality')], [c_234, c_127])).
% 2.62/1.35  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.62/1.35  tff(c_257, plain, (r2_hidden('#skF_7', '#skF_6') | r1_xboole_0('#skF_6', k1_tarski('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_249, c_6])).
% 2.62/1.35  tff(c_261, plain, (r1_xboole_0('#skF_6', k1_tarski('#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_75, c_257])).
% 2.62/1.35  tff(c_267, plain, (k4_xboole_0('#skF_6', k1_tarski('#skF_7'))='#skF_6'), inference(resolution, [status(thm)], [c_261, c_10])).
% 2.62/1.35  tff(c_272, plain, $false, inference(negUnitSimplification, [status(thm)], [c_127, c_267])).
% 2.62/1.35  tff(c_273, plain, (r2_hidden('#skF_9', '#skF_8')), inference(splitRight, [status(thm)], [c_56])).
% 2.62/1.35  tff(c_274, plain, (k4_xboole_0('#skF_6', k1_tarski('#skF_7'))='#skF_6'), inference(splitRight, [status(thm)], [c_56])).
% 2.62/1.35  tff(c_60, plain, (k4_xboole_0('#skF_6', k1_tarski('#skF_7'))!='#skF_6' | k4_xboole_0('#skF_8', k1_tarski('#skF_9'))='#skF_8'), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.62/1.35  tff(c_296, plain, (k4_xboole_0('#skF_8', k1_tarski('#skF_9'))='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_274, c_60])).
% 2.62/1.35  tff(c_40, plain, (![C_21]: (r2_hidden(C_21, k1_tarski(C_21)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.62/1.35  tff(c_12, plain, (![A_8, B_9]: (r1_xboole_0(A_8, B_9) | k4_xboole_0(A_8, B_9)!=A_8)), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.62/1.35  tff(c_291, plain, (![A_90, B_91, C_92]: (~r1_xboole_0(A_90, B_91) | ~r2_hidden(C_92, B_91) | ~r2_hidden(C_92, A_90))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.62/1.35  tff(c_326, plain, (![C_100, B_101, A_102]: (~r2_hidden(C_100, B_101) | ~r2_hidden(C_100, A_102) | k4_xboole_0(A_102, B_101)!=A_102)), inference(resolution, [status(thm)], [c_12, c_291])).
% 2.62/1.35  tff(c_390, plain, (![C_106, A_107]: (~r2_hidden(C_106, A_107) | k4_xboole_0(A_107, k1_tarski(C_106))!=A_107)), inference(resolution, [status(thm)], [c_40, c_326])).
% 2.62/1.35  tff(c_393, plain, (~r2_hidden('#skF_9', '#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_296, c_390])).
% 2.62/1.35  tff(c_400, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_273, c_393])).
% 2.62/1.35  tff(c_401, plain, (r2_hidden('#skF_9', '#skF_8')), inference(splitRight, [status(thm)], [c_58])).
% 2.62/1.35  tff(c_402, plain, (r2_hidden('#skF_7', '#skF_6')), inference(splitRight, [status(thm)], [c_58])).
% 2.62/1.35  tff(c_62, plain, (~r2_hidden('#skF_7', '#skF_6') | k4_xboole_0('#skF_8', k1_tarski('#skF_9'))='#skF_8'), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.62/1.35  tff(c_441, plain, (k4_xboole_0('#skF_8', k1_tarski('#skF_9'))='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_402, c_62])).
% 2.62/1.35  tff(c_473, plain, (![A_129, B_130, C_131]: (~r1_xboole_0(A_129, B_130) | ~r2_hidden(C_131, B_130) | ~r2_hidden(C_131, A_129))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.62/1.35  tff(c_503, plain, (![C_139, B_140, A_141]: (~r2_hidden(C_139, B_140) | ~r2_hidden(C_139, A_141) | k4_xboole_0(A_141, B_140)!=A_141)), inference(resolution, [status(thm)], [c_12, c_473])).
% 2.62/1.35  tff(c_605, plain, (![C_146, A_147]: (~r2_hidden(C_146, A_147) | k4_xboole_0(A_147, k1_tarski(C_146))!=A_147)), inference(resolution, [status(thm)], [c_40, c_503])).
% 2.62/1.35  tff(c_608, plain, (~r2_hidden('#skF_9', '#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_441, c_605])).
% 2.62/1.35  tff(c_612, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_401, c_608])).
% 2.62/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.62/1.35  
% 2.62/1.35  Inference rules
% 2.62/1.35  ----------------------
% 2.62/1.35  #Ref     : 0
% 2.62/1.35  #Sup     : 126
% 2.62/1.35  #Fact    : 0
% 2.62/1.35  #Define  : 0
% 2.62/1.35  #Split   : 3
% 2.62/1.35  #Chain   : 0
% 2.62/1.35  #Close   : 0
% 2.62/1.35  
% 2.62/1.35  Ordering : KBO
% 2.62/1.35  
% 2.62/1.35  Simplification rules
% 2.62/1.35  ----------------------
% 2.62/1.35  #Subsume      : 5
% 2.62/1.35  #Demod        : 12
% 2.62/1.35  #Tautology    : 40
% 2.62/1.35  #SimpNegUnit  : 2
% 2.62/1.35  #BackRed      : 0
% 2.62/1.35  
% 2.62/1.35  #Partial instantiations: 0
% 2.62/1.35  #Strategies tried      : 1
% 2.62/1.35  
% 2.62/1.35  Timing (in seconds)
% 2.62/1.35  ----------------------
% 2.62/1.35  Preprocessing        : 0.32
% 2.62/1.35  Parsing              : 0.16
% 2.62/1.35  CNF conversion       : 0.03
% 2.62/1.35  Main loop            : 0.28
% 2.62/1.35  Inferencing          : 0.10
% 2.62/1.35  Reduction            : 0.08
% 2.62/1.35  Demodulation         : 0.05
% 2.62/1.35  BG Simplification    : 0.02
% 2.62/1.35  Subsumption          : 0.05
% 2.62/1.35  Abstraction          : 0.02
% 2.62/1.35  MUC search           : 0.00
% 2.62/1.35  Cooper               : 0.00
% 2.62/1.35  Total                : 0.63
% 2.62/1.35  Index Insertion      : 0.00
% 2.62/1.35  Index Deletion       : 0.00
% 2.62/1.35  Index Matching       : 0.00
% 2.62/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
