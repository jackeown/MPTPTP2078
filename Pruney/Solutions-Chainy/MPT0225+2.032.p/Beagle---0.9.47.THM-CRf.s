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
% DateTime   : Thu Dec  3 09:48:35 EST 2020

% Result     : Theorem 1.86s
% Output     : CNFRefutation 2.10s
% Verified   : 
% Statistics : Number of formulae       :   53 (  77 expanded)
%              Number of leaves         :   24 (  38 expanded)
%              Depth                    :    5
%              Number of atoms          :   53 ( 100 expanded)
%              Number of equality atoms :   28 (  67 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_8 > #skF_3 > #skF_2 > #skF_1

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

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_38,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_67,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
      <=> A != B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),B)
        & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l24_zfmisc_1)).

tff(c_10,plain,(
    ! [C_9] : r2_hidden(C_9,k1_tarski(C_9)) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_48,plain,
    ( '#skF_5' != '#skF_6'
    | '#skF_7' = '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_53,plain,(
    '#skF_5' != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_96,plain,(
    ! [A_37,B_38] :
      ( r1_xboole_0(k1_tarski(A_37),B_38)
      | r2_hidden(A_37,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( k4_xboole_0(A_3,B_4) = A_3
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_135,plain,(
    ! [A_48,B_49] :
      ( k4_xboole_0(k1_tarski(A_48),B_49) = k1_tarski(A_48)
      | r2_hidden(A_48,B_49) ) ),
    inference(resolution,[status(thm)],[c_96,c_4])).

tff(c_46,plain,
    ( k4_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6')) != k1_tarski('#skF_5')
    | '#skF_7' = '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_90,plain,(
    k4_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6')) != k1_tarski('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_150,plain,(
    r2_hidden('#skF_5',k1_tarski('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_135,c_90])).

tff(c_8,plain,(
    ! [C_9,A_5] :
      ( C_9 = A_5
      | ~ r2_hidden(C_9,k1_tarski(A_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_154,plain,(
    '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_150,c_8])).

tff(c_158,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_53,c_154])).

tff(c_159,plain,(
    '#skF_7' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_160,plain,(
    k4_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6')) = k1_tarski('#skF_5') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_50,plain,
    ( k4_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6')) != k1_tarski('#skF_5')
    | k4_xboole_0(k1_tarski('#skF_7'),k1_tarski('#skF_8')) = k1_tarski('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_214,plain,(
    k4_xboole_0(k1_tarski('#skF_8'),k1_tarski('#skF_8')) = k1_tarski('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_159,c_159,c_160,c_50])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( r1_xboole_0(A_3,B_4)
      | k4_xboole_0(A_3,B_4) != A_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_175,plain,(
    ! [A_54,B_55] :
      ( ~ r2_hidden(A_54,B_55)
      | ~ r1_xboole_0(k1_tarski(A_54),B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_246,plain,(
    ! [A_63,B_64] :
      ( ~ r2_hidden(A_63,B_64)
      | k4_xboole_0(k1_tarski(A_63),B_64) != k1_tarski(A_63) ) ),
    inference(resolution,[status(thm)],[c_6,c_175])).

tff(c_252,plain,(
    ~ r2_hidden('#skF_8',k1_tarski('#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_214,c_246])).

tff(c_260,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_252])).

tff(c_261,plain,(
    '#skF_7' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_262,plain,(
    '#skF_5' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_52,plain,
    ( '#skF_5' != '#skF_6'
    | k4_xboole_0(k1_tarski('#skF_7'),k1_tarski('#skF_8')) = k1_tarski('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_352,plain,(
    k4_xboole_0(k1_tarski('#skF_8'),k1_tarski('#skF_8')) = k1_tarski('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_261,c_261,c_262,c_52])).

tff(c_318,plain,(
    ! [A_81,B_82] :
      ( ~ r2_hidden(A_81,B_82)
      | ~ r1_xboole_0(k1_tarski(A_81),B_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_377,plain,(
    ! [A_90,B_91] :
      ( ~ r2_hidden(A_90,B_91)
      | k4_xboole_0(k1_tarski(A_90),B_91) != k1_tarski(A_90) ) ),
    inference(resolution,[status(thm)],[c_6,c_318])).

tff(c_383,plain,(
    ~ r2_hidden('#skF_8',k1_tarski('#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_352,c_377])).

tff(c_388,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_383])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:05:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.86/1.22  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.86/1.22  
% 1.86/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.86/1.22  %$ r2_hidden > r1_xboole_0 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_8 > #skF_3 > #skF_2 > #skF_1
% 1.86/1.22  
% 1.86/1.22  %Foreground sorts:
% 1.86/1.22  
% 1.86/1.22  
% 1.86/1.22  %Background operators:
% 1.86/1.22  
% 1.86/1.22  
% 1.86/1.22  %Foreground operators:
% 1.86/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.86/1.22  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.86/1.22  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.86/1.22  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.86/1.22  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 1.86/1.22  tff('#skF_7', type, '#skF_7': $i).
% 1.86/1.22  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.86/1.22  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.86/1.22  tff('#skF_5', type, '#skF_5': $i).
% 1.86/1.22  tff('#skF_6', type, '#skF_6': $i).
% 1.86/1.22  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.86/1.22  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.86/1.22  tff('#skF_8', type, '#skF_8': $i).
% 1.86/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.86/1.22  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 1.86/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.86/1.22  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.86/1.22  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.86/1.22  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.86/1.22  
% 2.10/1.23  tff(f_38, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 2.10/1.23  tff(f_67, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 2.10/1.23  tff(f_61, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 2.10/1.23  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.10/1.23  tff(f_56, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 2.10/1.23  tff(c_10, plain, (![C_9]: (r2_hidden(C_9, k1_tarski(C_9)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.10/1.23  tff(c_48, plain, ('#skF_5'!='#skF_6' | '#skF_7'='#skF_8'), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.10/1.23  tff(c_53, plain, ('#skF_5'!='#skF_6'), inference(splitLeft, [status(thm)], [c_48])).
% 2.10/1.23  tff(c_96, plain, (![A_37, B_38]: (r1_xboole_0(k1_tarski(A_37), B_38) | r2_hidden(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.10/1.23  tff(c_4, plain, (![A_3, B_4]: (k4_xboole_0(A_3, B_4)=A_3 | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.10/1.23  tff(c_135, plain, (![A_48, B_49]: (k4_xboole_0(k1_tarski(A_48), B_49)=k1_tarski(A_48) | r2_hidden(A_48, B_49))), inference(resolution, [status(thm)], [c_96, c_4])).
% 2.10/1.23  tff(c_46, plain, (k4_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6'))!=k1_tarski('#skF_5') | '#skF_7'='#skF_8'), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.10/1.23  tff(c_90, plain, (k4_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6'))!=k1_tarski('#skF_5')), inference(splitLeft, [status(thm)], [c_46])).
% 2.10/1.23  tff(c_150, plain, (r2_hidden('#skF_5', k1_tarski('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_135, c_90])).
% 2.10/1.23  tff(c_8, plain, (![C_9, A_5]: (C_9=A_5 | ~r2_hidden(C_9, k1_tarski(A_5)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.10/1.23  tff(c_154, plain, ('#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_150, c_8])).
% 2.10/1.23  tff(c_158, plain, $false, inference(negUnitSimplification, [status(thm)], [c_53, c_154])).
% 2.10/1.23  tff(c_159, plain, ('#skF_7'='#skF_8'), inference(splitRight, [status(thm)], [c_46])).
% 2.10/1.23  tff(c_160, plain, (k4_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6'))=k1_tarski('#skF_5')), inference(splitRight, [status(thm)], [c_46])).
% 2.10/1.23  tff(c_50, plain, (k4_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6'))!=k1_tarski('#skF_5') | k4_xboole_0(k1_tarski('#skF_7'), k1_tarski('#skF_8'))=k1_tarski('#skF_7')), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.10/1.23  tff(c_214, plain, (k4_xboole_0(k1_tarski('#skF_8'), k1_tarski('#skF_8'))=k1_tarski('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_159, c_159, c_160, c_50])).
% 2.10/1.23  tff(c_6, plain, (![A_3, B_4]: (r1_xboole_0(A_3, B_4) | k4_xboole_0(A_3, B_4)!=A_3)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.10/1.23  tff(c_175, plain, (![A_54, B_55]: (~r2_hidden(A_54, B_55) | ~r1_xboole_0(k1_tarski(A_54), B_55))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.10/1.23  tff(c_246, plain, (![A_63, B_64]: (~r2_hidden(A_63, B_64) | k4_xboole_0(k1_tarski(A_63), B_64)!=k1_tarski(A_63))), inference(resolution, [status(thm)], [c_6, c_175])).
% 2.10/1.23  tff(c_252, plain, (~r2_hidden('#skF_8', k1_tarski('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_214, c_246])).
% 2.10/1.23  tff(c_260, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10, c_252])).
% 2.10/1.23  tff(c_261, plain, ('#skF_7'='#skF_8'), inference(splitRight, [status(thm)], [c_48])).
% 2.10/1.23  tff(c_262, plain, ('#skF_5'='#skF_6'), inference(splitRight, [status(thm)], [c_48])).
% 2.10/1.23  tff(c_52, plain, ('#skF_5'!='#skF_6' | k4_xboole_0(k1_tarski('#skF_7'), k1_tarski('#skF_8'))=k1_tarski('#skF_7')), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.10/1.23  tff(c_352, plain, (k4_xboole_0(k1_tarski('#skF_8'), k1_tarski('#skF_8'))=k1_tarski('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_261, c_261, c_262, c_52])).
% 2.10/1.23  tff(c_318, plain, (![A_81, B_82]: (~r2_hidden(A_81, B_82) | ~r1_xboole_0(k1_tarski(A_81), B_82))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.10/1.23  tff(c_377, plain, (![A_90, B_91]: (~r2_hidden(A_90, B_91) | k4_xboole_0(k1_tarski(A_90), B_91)!=k1_tarski(A_90))), inference(resolution, [status(thm)], [c_6, c_318])).
% 2.10/1.23  tff(c_383, plain, (~r2_hidden('#skF_8', k1_tarski('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_352, c_377])).
% 2.10/1.23  tff(c_388, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10, c_383])).
% 2.10/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.10/1.23  
% 2.10/1.23  Inference rules
% 2.10/1.23  ----------------------
% 2.10/1.23  #Ref     : 0
% 2.10/1.23  #Sup     : 73
% 2.10/1.23  #Fact    : 0
% 2.10/1.23  #Define  : 0
% 2.10/1.23  #Split   : 2
% 2.10/1.23  #Chain   : 0
% 2.10/1.23  #Close   : 0
% 2.10/1.23  
% 2.10/1.23  Ordering : KBO
% 2.10/1.23  
% 2.10/1.23  Simplification rules
% 2.10/1.23  ----------------------
% 2.10/1.23  #Subsume      : 6
% 2.10/1.23  #Demod        : 26
% 2.10/1.23  #Tautology    : 61
% 2.10/1.23  #SimpNegUnit  : 1
% 2.10/1.23  #BackRed      : 0
% 2.10/1.23  
% 2.10/1.23  #Partial instantiations: 0
% 2.10/1.23  #Strategies tried      : 1
% 2.10/1.23  
% 2.10/1.23  Timing (in seconds)
% 2.10/1.23  ----------------------
% 2.10/1.24  Preprocessing        : 0.29
% 2.10/1.24  Parsing              : 0.15
% 2.10/1.24  CNF conversion       : 0.02
% 2.10/1.24  Main loop            : 0.19
% 2.10/1.24  Inferencing          : 0.07
% 2.10/1.24  Reduction            : 0.06
% 2.10/1.24  Demodulation         : 0.04
% 2.10/1.24  BG Simplification    : 0.01
% 2.10/1.24  Subsumption          : 0.03
% 2.10/1.24  Abstraction          : 0.01
% 2.10/1.24  MUC search           : 0.00
% 2.10/1.24  Cooper               : 0.00
% 2.10/1.24  Total                : 0.51
% 2.10/1.24  Index Insertion      : 0.00
% 2.10/1.24  Index Deletion       : 0.00
% 2.10/1.24  Index Matching       : 0.00
% 2.10/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
