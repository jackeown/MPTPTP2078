%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:41 EST 2020

% Result     : Theorem 2.11s
% Output     : CNFRefutation 2.11s
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
%$ r2_hidden > r1_xboole_0 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_4 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_9 > #skF_8 > #skF_2 > #skF_1

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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_77,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(A,k1_tarski(B)) = A
      <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_56,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_49,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(c_50,plain,
    ( k4_xboole_0('#skF_6',k1_tarski('#skF_7')) != '#skF_6'
    | r2_hidden('#skF_9','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_99,plain,(
    k4_xboole_0('#skF_6',k1_tarski('#skF_7')) != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_52,plain,
    ( ~ r2_hidden('#skF_7','#skF_6')
    | r2_hidden('#skF_9','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_83,plain,(
    ~ r2_hidden('#skF_7','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_100,plain,(
    ! [A_41,B_42] :
      ( r2_hidden('#skF_1'(A_41,B_42),B_42)
      | r1_xboole_0(A_41,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_14,plain,(
    ! [C_14,A_10] :
      ( C_14 = A_10
      | ~ r2_hidden(C_14,k1_tarski(A_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_166,plain,(
    ! [A_58,A_59] :
      ( '#skF_1'(A_58,k1_tarski(A_59)) = A_59
      | r1_xboole_0(A_58,k1_tarski(A_59)) ) ),
    inference(resolution,[status(thm)],[c_100,c_14])).

tff(c_10,plain,(
    ! [A_8,B_9] :
      ( k4_xboole_0(A_8,B_9) = A_8
      | ~ r1_xboole_0(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_201,plain,(
    ! [A_73,A_74] :
      ( k4_xboole_0(A_73,k1_tarski(A_74)) = A_73
      | '#skF_1'(A_73,k1_tarski(A_74)) = A_74 ) ),
    inference(resolution,[status(thm)],[c_166,c_10])).

tff(c_216,plain,(
    '#skF_1'('#skF_6',k1_tarski('#skF_7')) = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_201,c_99])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_221,plain,
    ( r2_hidden('#skF_7','#skF_6')
    | r1_xboole_0('#skF_6',k1_tarski('#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_216,c_6])).

tff(c_227,plain,(
    r1_xboole_0('#skF_6',k1_tarski('#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_83,c_221])).

tff(c_234,plain,(
    k4_xboole_0('#skF_6',k1_tarski('#skF_7')) = '#skF_6' ),
    inference(resolution,[status(thm)],[c_227,c_10])).

tff(c_239,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_99,c_234])).

tff(c_240,plain,(
    r2_hidden('#skF_9','#skF_8') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_241,plain,(
    k4_xboole_0('#skF_6',k1_tarski('#skF_7')) = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_54,plain,
    ( k4_xboole_0('#skF_6',k1_tarski('#skF_7')) != '#skF_6'
    | k4_xboole_0('#skF_8',k1_tarski('#skF_9')) = '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_313,plain,(
    k4_xboole_0('#skF_8',k1_tarski('#skF_9')) = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_241,c_54])).

tff(c_16,plain,(
    ! [C_14] : r2_hidden(C_14,k1_tarski(C_14)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_12,plain,(
    ! [A_8,B_9] :
      ( r1_xboole_0(A_8,B_9)
      | k4_xboole_0(A_8,B_9) != A_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_300,plain,(
    ! [A_87,B_88,C_89] :
      ( ~ r1_xboole_0(A_87,B_88)
      | ~ r2_hidden(C_89,B_88)
      | ~ r2_hidden(C_89,A_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_326,plain,(
    ! [C_94,B_95,A_96] :
      ( ~ r2_hidden(C_94,B_95)
      | ~ r2_hidden(C_94,A_96)
      | k4_xboole_0(A_96,B_95) != A_96 ) ),
    inference(resolution,[status(thm)],[c_12,c_300])).

tff(c_366,plain,(
    ! [C_100,A_101] :
      ( ~ r2_hidden(C_100,A_101)
      | k4_xboole_0(A_101,k1_tarski(C_100)) != A_101 ) ),
    inference(resolution,[status(thm)],[c_16,c_326])).

tff(c_369,plain,(
    ~ r2_hidden('#skF_9','#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_313,c_366])).

tff(c_376,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_240,c_369])).

tff(c_377,plain,(
    r2_hidden('#skF_9','#skF_8') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_378,plain,(
    r2_hidden('#skF_7','#skF_6') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_56,plain,
    ( ~ r2_hidden('#skF_7','#skF_6')
    | k4_xboole_0('#skF_8',k1_tarski('#skF_9')) = '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_380,plain,(
    k4_xboole_0('#skF_8',k1_tarski('#skF_9')) = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_378,c_56])).

tff(c_446,plain,(
    ! [A_117,B_118,C_119] :
      ( ~ r1_xboole_0(A_117,B_118)
      | ~ r2_hidden(C_119,B_118)
      | ~ r2_hidden(C_119,A_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_476,plain,(
    ! [C_127,B_128,A_129] :
      ( ~ r2_hidden(C_127,B_128)
      | ~ r2_hidden(C_127,A_129)
      | k4_xboole_0(A_129,B_128) != A_129 ) ),
    inference(resolution,[status(thm)],[c_12,c_446])).

tff(c_539,plain,(
    ! [C_134,A_135] :
      ( ~ r2_hidden(C_134,A_135)
      | k4_xboole_0(A_135,k1_tarski(C_134)) != A_135 ) ),
    inference(resolution,[status(thm)],[c_16,c_476])).

tff(c_542,plain,(
    ~ r2_hidden('#skF_9','#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_380,c_539])).

tff(c_546,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_377,c_542])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.33  % Computer   : n006.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % DateTime   : Tue Dec  1 20:54:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.11/1.30  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.11/1.31  
% 2.11/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.11/1.31  %$ r2_hidden > r1_xboole_0 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_4 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_9 > #skF_8 > #skF_2 > #skF_1
% 2.11/1.31  
% 2.11/1.31  %Foreground sorts:
% 2.11/1.31  
% 2.11/1.31  
% 2.11/1.31  %Background operators:
% 2.11/1.31  
% 2.11/1.31  
% 2.11/1.31  %Foreground operators:
% 2.11/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.11/1.31  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.11/1.31  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.11/1.31  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.11/1.31  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.11/1.31  tff('#skF_7', type, '#skF_7': $i).
% 2.11/1.31  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.11/1.31  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.11/1.31  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.11/1.31  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.11/1.31  tff('#skF_6', type, '#skF_6': $i).
% 2.11/1.31  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 2.11/1.31  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.11/1.31  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.11/1.31  tff('#skF_9', type, '#skF_9': $i).
% 2.11/1.31  tff('#skF_8', type, '#skF_8': $i).
% 2.11/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.11/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.11/1.31  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.11/1.31  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.11/1.31  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.11/1.31  
% 2.11/1.32  tff(f_77, negated_conjecture, ~(![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 2.11/1.32  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.11/1.32  tff(f_56, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 2.11/1.32  tff(f_49, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.11/1.32  tff(c_50, plain, (k4_xboole_0('#skF_6', k1_tarski('#skF_7'))!='#skF_6' | r2_hidden('#skF_9', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.11/1.32  tff(c_99, plain, (k4_xboole_0('#skF_6', k1_tarski('#skF_7'))!='#skF_6'), inference(splitLeft, [status(thm)], [c_50])).
% 2.11/1.32  tff(c_52, plain, (~r2_hidden('#skF_7', '#skF_6') | r2_hidden('#skF_9', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.11/1.32  tff(c_83, plain, (~r2_hidden('#skF_7', '#skF_6')), inference(splitLeft, [status(thm)], [c_52])).
% 2.11/1.32  tff(c_100, plain, (![A_41, B_42]: (r2_hidden('#skF_1'(A_41, B_42), B_42) | r1_xboole_0(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.11/1.32  tff(c_14, plain, (![C_14, A_10]: (C_14=A_10 | ~r2_hidden(C_14, k1_tarski(A_10)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.11/1.32  tff(c_166, plain, (![A_58, A_59]: ('#skF_1'(A_58, k1_tarski(A_59))=A_59 | r1_xboole_0(A_58, k1_tarski(A_59)))), inference(resolution, [status(thm)], [c_100, c_14])).
% 2.11/1.32  tff(c_10, plain, (![A_8, B_9]: (k4_xboole_0(A_8, B_9)=A_8 | ~r1_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.11/1.32  tff(c_201, plain, (![A_73, A_74]: (k4_xboole_0(A_73, k1_tarski(A_74))=A_73 | '#skF_1'(A_73, k1_tarski(A_74))=A_74)), inference(resolution, [status(thm)], [c_166, c_10])).
% 2.11/1.32  tff(c_216, plain, ('#skF_1'('#skF_6', k1_tarski('#skF_7'))='#skF_7'), inference(superposition, [status(thm), theory('equality')], [c_201, c_99])).
% 2.11/1.32  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.11/1.32  tff(c_221, plain, (r2_hidden('#skF_7', '#skF_6') | r1_xboole_0('#skF_6', k1_tarski('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_216, c_6])).
% 2.11/1.32  tff(c_227, plain, (r1_xboole_0('#skF_6', k1_tarski('#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_83, c_221])).
% 2.11/1.32  tff(c_234, plain, (k4_xboole_0('#skF_6', k1_tarski('#skF_7'))='#skF_6'), inference(resolution, [status(thm)], [c_227, c_10])).
% 2.11/1.32  tff(c_239, plain, $false, inference(negUnitSimplification, [status(thm)], [c_99, c_234])).
% 2.11/1.32  tff(c_240, plain, (r2_hidden('#skF_9', '#skF_8')), inference(splitRight, [status(thm)], [c_50])).
% 2.11/1.32  tff(c_241, plain, (k4_xboole_0('#skF_6', k1_tarski('#skF_7'))='#skF_6'), inference(splitRight, [status(thm)], [c_50])).
% 2.11/1.32  tff(c_54, plain, (k4_xboole_0('#skF_6', k1_tarski('#skF_7'))!='#skF_6' | k4_xboole_0('#skF_8', k1_tarski('#skF_9'))='#skF_8'), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.11/1.32  tff(c_313, plain, (k4_xboole_0('#skF_8', k1_tarski('#skF_9'))='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_241, c_54])).
% 2.11/1.32  tff(c_16, plain, (![C_14]: (r2_hidden(C_14, k1_tarski(C_14)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.11/1.32  tff(c_12, plain, (![A_8, B_9]: (r1_xboole_0(A_8, B_9) | k4_xboole_0(A_8, B_9)!=A_8)), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.11/1.32  tff(c_300, plain, (![A_87, B_88, C_89]: (~r1_xboole_0(A_87, B_88) | ~r2_hidden(C_89, B_88) | ~r2_hidden(C_89, A_87))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.11/1.32  tff(c_326, plain, (![C_94, B_95, A_96]: (~r2_hidden(C_94, B_95) | ~r2_hidden(C_94, A_96) | k4_xboole_0(A_96, B_95)!=A_96)), inference(resolution, [status(thm)], [c_12, c_300])).
% 2.11/1.32  tff(c_366, plain, (![C_100, A_101]: (~r2_hidden(C_100, A_101) | k4_xboole_0(A_101, k1_tarski(C_100))!=A_101)), inference(resolution, [status(thm)], [c_16, c_326])).
% 2.11/1.32  tff(c_369, plain, (~r2_hidden('#skF_9', '#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_313, c_366])).
% 2.11/1.32  tff(c_376, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_240, c_369])).
% 2.11/1.32  tff(c_377, plain, (r2_hidden('#skF_9', '#skF_8')), inference(splitRight, [status(thm)], [c_52])).
% 2.11/1.32  tff(c_378, plain, (r2_hidden('#skF_7', '#skF_6')), inference(splitRight, [status(thm)], [c_52])).
% 2.11/1.32  tff(c_56, plain, (~r2_hidden('#skF_7', '#skF_6') | k4_xboole_0('#skF_8', k1_tarski('#skF_9'))='#skF_8'), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.11/1.32  tff(c_380, plain, (k4_xboole_0('#skF_8', k1_tarski('#skF_9'))='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_378, c_56])).
% 2.11/1.32  tff(c_446, plain, (![A_117, B_118, C_119]: (~r1_xboole_0(A_117, B_118) | ~r2_hidden(C_119, B_118) | ~r2_hidden(C_119, A_117))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.11/1.32  tff(c_476, plain, (![C_127, B_128, A_129]: (~r2_hidden(C_127, B_128) | ~r2_hidden(C_127, A_129) | k4_xboole_0(A_129, B_128)!=A_129)), inference(resolution, [status(thm)], [c_12, c_446])).
% 2.11/1.32  tff(c_539, plain, (![C_134, A_135]: (~r2_hidden(C_134, A_135) | k4_xboole_0(A_135, k1_tarski(C_134))!=A_135)), inference(resolution, [status(thm)], [c_16, c_476])).
% 2.11/1.32  tff(c_542, plain, (~r2_hidden('#skF_9', '#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_380, c_539])).
% 2.11/1.32  tff(c_546, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_377, c_542])).
% 2.11/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.11/1.32  
% 2.11/1.32  Inference rules
% 2.11/1.32  ----------------------
% 2.11/1.32  #Ref     : 0
% 2.11/1.32  #Sup     : 110
% 2.11/1.32  #Fact    : 0
% 2.11/1.32  #Define  : 0
% 2.11/1.32  #Split   : 2
% 2.11/1.32  #Chain   : 0
% 2.11/1.32  #Close   : 0
% 2.11/1.32  
% 2.11/1.32  Ordering : KBO
% 2.11/1.32  
% 2.11/1.32  Simplification rules
% 2.11/1.32  ----------------------
% 2.11/1.32  #Subsume      : 7
% 2.11/1.32  #Demod        : 9
% 2.11/1.32  #Tautology    : 42
% 2.11/1.32  #SimpNegUnit  : 2
% 2.11/1.32  #BackRed      : 0
% 2.11/1.32  
% 2.11/1.32  #Partial instantiations: 0
% 2.11/1.32  #Strategies tried      : 1
% 2.11/1.32  
% 2.11/1.32  Timing (in seconds)
% 2.11/1.32  ----------------------
% 2.11/1.32  Preprocessing        : 0.32
% 2.11/1.32  Parsing              : 0.16
% 2.11/1.32  CNF conversion       : 0.02
% 2.11/1.32  Main loop            : 0.26
% 2.11/1.32  Inferencing          : 0.10
% 2.11/1.32  Reduction            : 0.07
% 2.11/1.32  Demodulation         : 0.05
% 2.11/1.33  BG Simplification    : 0.02
% 2.11/1.33  Subsumption          : 0.04
% 2.11/1.33  Abstraction          : 0.02
% 2.11/1.33  MUC search           : 0.00
% 2.11/1.33  Cooper               : 0.00
% 2.11/1.33  Total                : 0.60
% 2.11/1.33  Index Insertion      : 0.00
% 2.11/1.33  Index Deletion       : 0.00
% 2.11/1.33  Index Matching       : 0.00
% 2.11/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
