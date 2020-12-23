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
% DateTime   : Thu Dec  3 09:52:42 EST 2020

% Result     : Theorem 2.10s
% Output     : CNFRefutation 2.10s
% Verified   : 
% Statistics : Number of formulae       :   52 (  71 expanded)
%              Number of leaves         :   24 (  35 expanded)
%              Depth                    :    8
%              Number of atoms          :   55 (  96 expanded)
%              Number of equality atoms :   20 (  35 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2 > #skF_1

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_75,negated_conjecture,(
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

tff(f_69,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k4_xboole_0(B,k1_tarski(C)))
    <=> ( r2_hidden(A,B)
        & A != C ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).

tff(c_38,plain,
    ( k4_xboole_0('#skF_4',k1_tarski('#skF_5')) != '#skF_4'
    | r2_hidden('#skF_7','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_78,plain,(
    k4_xboole_0('#skF_4',k1_tarski('#skF_5')) != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_40,plain,
    ( ~ r2_hidden('#skF_5','#skF_4')
    | r2_hidden('#skF_7','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_55,plain,(
    ~ r2_hidden('#skF_5','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_79,plain,(
    ! [A_36,B_37] :
      ( r2_hidden('#skF_1'(A_36,B_37),B_37)
      | r1_xboole_0(A_36,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_14,plain,(
    ! [C_14,A_10] :
      ( C_14 = A_10
      | ~ r2_hidden(C_14,k1_tarski(A_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_124,plain,(
    ! [A_51,A_52] :
      ( '#skF_1'(A_51,k1_tarski(A_52)) = A_52
      | r1_xboole_0(A_51,k1_tarski(A_52)) ) ),
    inference(resolution,[status(thm)],[c_79,c_14])).

tff(c_10,plain,(
    ! [A_8,B_9] :
      ( k4_xboole_0(A_8,B_9) = A_8
      | ~ r1_xboole_0(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_152,plain,(
    ! [A_60,A_61] :
      ( k4_xboole_0(A_60,k1_tarski(A_61)) = A_60
      | '#skF_1'(A_60,k1_tarski(A_61)) = A_61 ) ),
    inference(resolution,[status(thm)],[c_124,c_10])).

tff(c_173,plain,(
    '#skF_1'('#skF_4',k1_tarski('#skF_5')) = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_152,c_78])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_178,plain,
    ( r2_hidden('#skF_5','#skF_4')
    | r1_xboole_0('#skF_4',k1_tarski('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_173,c_6])).

tff(c_184,plain,(
    r1_xboole_0('#skF_4',k1_tarski('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_55,c_178])).

tff(c_192,plain,(
    k4_xboole_0('#skF_4',k1_tarski('#skF_5')) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_184,c_10])).

tff(c_197,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_192])).

tff(c_198,plain,(
    r2_hidden('#skF_7','#skF_6') ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_199,plain,(
    k4_xboole_0('#skF_4',k1_tarski('#skF_5')) = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_42,plain,
    ( k4_xboole_0('#skF_4',k1_tarski('#skF_5')) != '#skF_4'
    | k4_xboole_0('#skF_6',k1_tarski('#skF_7')) = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_272,plain,(
    k4_xboole_0('#skF_6',k1_tarski('#skF_7')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_199,c_42])).

tff(c_34,plain,(
    ! [C_23,B_22] : ~ r2_hidden(C_23,k4_xboole_0(B_22,k1_tarski(C_23))) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_279,plain,(
    ~ r2_hidden('#skF_7','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_272,c_34])).

tff(c_284,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_198,c_279])).

tff(c_285,plain,(
    r2_hidden('#skF_7','#skF_6') ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_286,plain,(
    r2_hidden('#skF_5','#skF_4') ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_44,plain,
    ( ~ r2_hidden('#skF_5','#skF_4')
    | k4_xboole_0('#skF_6',k1_tarski('#skF_7')) = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_317,plain,(
    k4_xboole_0('#skF_6',k1_tarski('#skF_7')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_286,c_44])).

tff(c_321,plain,(
    ~ r2_hidden('#skF_7','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_317,c_34])).

tff(c_326,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_285,c_321])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n010.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:34:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.10/1.24  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.10/1.25  
% 2.10/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.10/1.25  %$ r2_hidden > r1_xboole_0 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2 > #skF_1
% 2.10/1.25  
% 2.10/1.25  %Foreground sorts:
% 2.10/1.25  
% 2.10/1.25  
% 2.10/1.25  %Background operators:
% 2.10/1.25  
% 2.10/1.25  
% 2.10/1.25  %Foreground operators:
% 2.10/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.10/1.25  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.10/1.25  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.10/1.25  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.10/1.25  tff('#skF_7', type, '#skF_7': $i).
% 2.10/1.25  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.10/1.25  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.10/1.25  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.10/1.25  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.10/1.25  tff('#skF_5', type, '#skF_5': $i).
% 2.10/1.25  tff('#skF_6', type, '#skF_6': $i).
% 2.10/1.25  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.10/1.25  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.10/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.10/1.25  tff('#skF_4', type, '#skF_4': $i).
% 2.10/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.10/1.25  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.10/1.25  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.10/1.25  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.10/1.25  
% 2.10/1.26  tff(f_75, negated_conjecture, ~(![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 2.10/1.26  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.10/1.26  tff(f_56, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 2.10/1.26  tff(f_49, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.10/1.26  tff(f_69, axiom, (![A, B, C]: (r2_hidden(A, k4_xboole_0(B, k1_tarski(C))) <=> (r2_hidden(A, B) & ~(A = C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 2.10/1.26  tff(c_38, plain, (k4_xboole_0('#skF_4', k1_tarski('#skF_5'))!='#skF_4' | r2_hidden('#skF_7', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.10/1.26  tff(c_78, plain, (k4_xboole_0('#skF_4', k1_tarski('#skF_5'))!='#skF_4'), inference(splitLeft, [status(thm)], [c_38])).
% 2.10/1.26  tff(c_40, plain, (~r2_hidden('#skF_5', '#skF_4') | r2_hidden('#skF_7', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.10/1.26  tff(c_55, plain, (~r2_hidden('#skF_5', '#skF_4')), inference(splitLeft, [status(thm)], [c_40])).
% 2.10/1.26  tff(c_79, plain, (![A_36, B_37]: (r2_hidden('#skF_1'(A_36, B_37), B_37) | r1_xboole_0(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.10/1.26  tff(c_14, plain, (![C_14, A_10]: (C_14=A_10 | ~r2_hidden(C_14, k1_tarski(A_10)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.10/1.26  tff(c_124, plain, (![A_51, A_52]: ('#skF_1'(A_51, k1_tarski(A_52))=A_52 | r1_xboole_0(A_51, k1_tarski(A_52)))), inference(resolution, [status(thm)], [c_79, c_14])).
% 2.10/1.26  tff(c_10, plain, (![A_8, B_9]: (k4_xboole_0(A_8, B_9)=A_8 | ~r1_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.10/1.26  tff(c_152, plain, (![A_60, A_61]: (k4_xboole_0(A_60, k1_tarski(A_61))=A_60 | '#skF_1'(A_60, k1_tarski(A_61))=A_61)), inference(resolution, [status(thm)], [c_124, c_10])).
% 2.10/1.26  tff(c_173, plain, ('#skF_1'('#skF_4', k1_tarski('#skF_5'))='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_152, c_78])).
% 2.10/1.26  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.10/1.26  tff(c_178, plain, (r2_hidden('#skF_5', '#skF_4') | r1_xboole_0('#skF_4', k1_tarski('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_173, c_6])).
% 2.10/1.26  tff(c_184, plain, (r1_xboole_0('#skF_4', k1_tarski('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_55, c_178])).
% 2.10/1.26  tff(c_192, plain, (k4_xboole_0('#skF_4', k1_tarski('#skF_5'))='#skF_4'), inference(resolution, [status(thm)], [c_184, c_10])).
% 2.10/1.26  tff(c_197, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_192])).
% 2.10/1.26  tff(c_198, plain, (r2_hidden('#skF_7', '#skF_6')), inference(splitRight, [status(thm)], [c_38])).
% 2.10/1.26  tff(c_199, plain, (k4_xboole_0('#skF_4', k1_tarski('#skF_5'))='#skF_4'), inference(splitRight, [status(thm)], [c_38])).
% 2.10/1.26  tff(c_42, plain, (k4_xboole_0('#skF_4', k1_tarski('#skF_5'))!='#skF_4' | k4_xboole_0('#skF_6', k1_tarski('#skF_7'))='#skF_6'), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.10/1.26  tff(c_272, plain, (k4_xboole_0('#skF_6', k1_tarski('#skF_7'))='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_199, c_42])).
% 2.10/1.26  tff(c_34, plain, (![C_23, B_22]: (~r2_hidden(C_23, k4_xboole_0(B_22, k1_tarski(C_23))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.10/1.26  tff(c_279, plain, (~r2_hidden('#skF_7', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_272, c_34])).
% 2.10/1.26  tff(c_284, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_198, c_279])).
% 2.10/1.26  tff(c_285, plain, (r2_hidden('#skF_7', '#skF_6')), inference(splitRight, [status(thm)], [c_40])).
% 2.10/1.26  tff(c_286, plain, (r2_hidden('#skF_5', '#skF_4')), inference(splitRight, [status(thm)], [c_40])).
% 2.10/1.26  tff(c_44, plain, (~r2_hidden('#skF_5', '#skF_4') | k4_xboole_0('#skF_6', k1_tarski('#skF_7'))='#skF_6'), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.10/1.26  tff(c_317, plain, (k4_xboole_0('#skF_6', k1_tarski('#skF_7'))='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_286, c_44])).
% 2.10/1.26  tff(c_321, plain, (~r2_hidden('#skF_7', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_317, c_34])).
% 2.10/1.26  tff(c_326, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_285, c_321])).
% 2.10/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.10/1.26  
% 2.10/1.26  Inference rules
% 2.10/1.26  ----------------------
% 2.10/1.26  #Ref     : 0
% 2.10/1.26  #Sup     : 63
% 2.10/1.26  #Fact    : 0
% 2.10/1.26  #Define  : 0
% 2.10/1.26  #Split   : 3
% 2.10/1.26  #Chain   : 0
% 2.10/1.26  #Close   : 0
% 2.10/1.26  
% 2.10/1.26  Ordering : KBO
% 2.10/1.26  
% 2.10/1.26  Simplification rules
% 2.10/1.26  ----------------------
% 2.10/1.26  #Subsume      : 4
% 2.10/1.26  #Demod        : 5
% 2.10/1.26  #Tautology    : 30
% 2.10/1.26  #SimpNegUnit  : 2
% 2.10/1.26  #BackRed      : 0
% 2.10/1.26  
% 2.10/1.26  #Partial instantiations: 0
% 2.10/1.26  #Strategies tried      : 1
% 2.10/1.26  
% 2.10/1.26  Timing (in seconds)
% 2.10/1.26  ----------------------
% 2.10/1.26  Preprocessing        : 0.31
% 2.10/1.26  Parsing              : 0.16
% 2.10/1.26  CNF conversion       : 0.02
% 2.10/1.26  Main loop            : 0.20
% 2.10/1.26  Inferencing          : 0.07
% 2.10/1.26  Reduction            : 0.05
% 2.10/1.26  Demodulation         : 0.03
% 2.10/1.26  BG Simplification    : 0.01
% 2.10/1.26  Subsumption          : 0.03
% 2.10/1.26  Abstraction          : 0.01
% 2.10/1.26  MUC search           : 0.00
% 2.10/1.26  Cooper               : 0.00
% 2.10/1.26  Total                : 0.53
% 2.10/1.26  Index Insertion      : 0.00
% 2.10/1.26  Index Deletion       : 0.00
% 2.10/1.26  Index Matching       : 0.00
% 2.10/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
