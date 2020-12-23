%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:36 EST 2020

% Result     : Theorem 2.19s
% Output     : CNFRefutation 2.46s
% Verified   : 
% Statistics : Number of formulae       :   55 (  77 expanded)
%              Number of leaves         :   24 (  38 expanded)
%              Depth                    :    5
%              Number of atoms          :   65 ( 114 expanded)
%              Number of equality atoms :   30 (  63 expanded)
%              Maximal formula depth    :    9 (   4 average)
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

tff(f_56,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_73,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
      <=> A != B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

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

tff(c_16,plain,(
    ! [C_14] : r2_hidden(C_14,k1_tarski(C_14)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_36,plain,
    ( '#skF_5' != '#skF_4'
    | '#skF_7' = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_41,plain,(
    '#skF_5' != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_32,plain,(
    ! [A_21,B_22] :
      ( r1_xboole_0(k1_tarski(A_21),B_22)
      | r2_hidden(A_21,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_69,plain,(
    ! [A_33,B_34] :
      ( k4_xboole_0(A_33,B_34) = A_33
      | ~ r1_xboole_0(A_33,B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_116,plain,(
    ! [A_47,B_48] :
      ( k4_xboole_0(k1_tarski(A_47),B_48) = k1_tarski(A_47)
      | r2_hidden(A_47,B_48) ) ),
    inference(resolution,[status(thm)],[c_32,c_69])).

tff(c_34,plain,
    ( k4_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_5')) != k1_tarski('#skF_4')
    | '#skF_7' = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_78,plain,(
    k4_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_5')) != k1_tarski('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_127,plain,(
    r2_hidden('#skF_4',k1_tarski('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_116,c_78])).

tff(c_14,plain,(
    ! [C_14,A_10] :
      ( C_14 = A_10
      | ~ r2_hidden(C_14,k1_tarski(A_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_131,plain,(
    '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_127,c_14])).

tff(c_135,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_41,c_131])).

tff(c_136,plain,(
    '#skF_7' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_137,plain,(
    k4_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_5')) = k1_tarski('#skF_4') ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_38,plain,
    ( k4_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_5')) != k1_tarski('#skF_4')
    | k4_xboole_0(k1_tarski('#skF_6'),k1_tarski('#skF_7')) = k1_tarski('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_209,plain,(
    k4_xboole_0(k1_tarski('#skF_6'),k1_tarski('#skF_6')) = k1_tarski('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_137,c_38])).

tff(c_12,plain,(
    ! [A_8,B_9] :
      ( r1_xboole_0(A_8,B_9)
      | k4_xboole_0(A_8,B_9) != A_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_167,plain,(
    ! [A_55,B_56,C_57] :
      ( ~ r1_xboole_0(A_55,B_56)
      | ~ r2_hidden(C_57,B_56)
      | ~ r2_hidden(C_57,A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_232,plain,(
    ! [C_67,B_68,A_69] :
      ( ~ r2_hidden(C_67,B_68)
      | ~ r2_hidden(C_67,A_69)
      | k4_xboole_0(A_69,B_68) != A_69 ) ),
    inference(resolution,[status(thm)],[c_12,c_167])).

tff(c_242,plain,(
    ! [C_70,A_71] :
      ( ~ r2_hidden(C_70,A_71)
      | k4_xboole_0(A_71,k1_tarski(C_70)) != A_71 ) ),
    inference(resolution,[status(thm)],[c_16,c_232])).

tff(c_245,plain,(
    ~ r2_hidden('#skF_6',k1_tarski('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_209,c_242])).

tff(c_256,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_245])).

tff(c_257,plain,(
    '#skF_7' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_258,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_40,plain,
    ( '#skF_5' != '#skF_4'
    | k4_xboole_0(k1_tarski('#skF_6'),k1_tarski('#skF_7')) = k1_tarski('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_285,plain,(
    k4_xboole_0(k1_tarski('#skF_6'),k1_tarski('#skF_6')) = k1_tarski('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_257,c_258,c_40])).

tff(c_340,plain,(
    ! [A_93,B_94,C_95] :
      ( ~ r1_xboole_0(A_93,B_94)
      | ~ r2_hidden(C_95,B_94)
      | ~ r2_hidden(C_95,A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_383,plain,(
    ! [C_102,B_103,A_104] :
      ( ~ r2_hidden(C_102,B_103)
      | ~ r2_hidden(C_102,A_104)
      | k4_xboole_0(A_104,B_103) != A_104 ) ),
    inference(resolution,[status(thm)],[c_12,c_340])).

tff(c_393,plain,(
    ! [C_105,A_106] :
      ( ~ r2_hidden(C_105,A_106)
      | k4_xboole_0(A_106,k1_tarski(C_105)) != A_106 ) ),
    inference(resolution,[status(thm)],[c_16,c_383])).

tff(c_400,plain,(
    ~ r2_hidden('#skF_6',k1_tarski('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_285,c_393])).

tff(c_405,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_400])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n004.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 19:52:08 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.19/1.45  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.19/1.46  
% 2.19/1.46  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.19/1.46  %$ r2_hidden > r1_xboole_0 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2 > #skF_1
% 2.19/1.46  
% 2.19/1.46  %Foreground sorts:
% 2.19/1.46  
% 2.19/1.46  
% 2.19/1.46  %Background operators:
% 2.19/1.46  
% 2.19/1.46  
% 2.19/1.46  %Foreground operators:
% 2.19/1.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.19/1.46  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.19/1.46  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.19/1.46  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.19/1.46  tff('#skF_7', type, '#skF_7': $i).
% 2.19/1.46  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.19/1.46  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.19/1.46  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.19/1.46  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.19/1.46  tff('#skF_5', type, '#skF_5': $i).
% 2.19/1.46  tff('#skF_6', type, '#skF_6': $i).
% 2.19/1.46  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.19/1.46  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.19/1.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.19/1.46  tff('#skF_4', type, '#skF_4': $i).
% 2.19/1.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.19/1.46  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.19/1.46  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.19/1.46  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.19/1.46  
% 2.46/1.47  tff(f_56, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 2.46/1.47  tff(f_73, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 2.46/1.47  tff(f_67, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 2.46/1.47  tff(f_49, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.46/1.47  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.46/1.47  tff(c_16, plain, (![C_14]: (r2_hidden(C_14, k1_tarski(C_14)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.46/1.47  tff(c_36, plain, ('#skF_5'!='#skF_4' | '#skF_7'='#skF_6'), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.46/1.47  tff(c_41, plain, ('#skF_5'!='#skF_4'), inference(splitLeft, [status(thm)], [c_36])).
% 2.46/1.47  tff(c_32, plain, (![A_21, B_22]: (r1_xboole_0(k1_tarski(A_21), B_22) | r2_hidden(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.46/1.47  tff(c_69, plain, (![A_33, B_34]: (k4_xboole_0(A_33, B_34)=A_33 | ~r1_xboole_0(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.46/1.47  tff(c_116, plain, (![A_47, B_48]: (k4_xboole_0(k1_tarski(A_47), B_48)=k1_tarski(A_47) | r2_hidden(A_47, B_48))), inference(resolution, [status(thm)], [c_32, c_69])).
% 2.46/1.47  tff(c_34, plain, (k4_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_5'))!=k1_tarski('#skF_4') | '#skF_7'='#skF_6'), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.46/1.47  tff(c_78, plain, (k4_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_5'))!=k1_tarski('#skF_4')), inference(splitLeft, [status(thm)], [c_34])).
% 2.46/1.47  tff(c_127, plain, (r2_hidden('#skF_4', k1_tarski('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_116, c_78])).
% 2.46/1.47  tff(c_14, plain, (![C_14, A_10]: (C_14=A_10 | ~r2_hidden(C_14, k1_tarski(A_10)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.46/1.47  tff(c_131, plain, ('#skF_5'='#skF_4'), inference(resolution, [status(thm)], [c_127, c_14])).
% 2.46/1.47  tff(c_135, plain, $false, inference(negUnitSimplification, [status(thm)], [c_41, c_131])).
% 2.46/1.47  tff(c_136, plain, ('#skF_7'='#skF_6'), inference(splitRight, [status(thm)], [c_34])).
% 2.46/1.47  tff(c_137, plain, (k4_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_5'))=k1_tarski('#skF_4')), inference(splitRight, [status(thm)], [c_34])).
% 2.46/1.47  tff(c_38, plain, (k4_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_5'))!=k1_tarski('#skF_4') | k4_xboole_0(k1_tarski('#skF_6'), k1_tarski('#skF_7'))=k1_tarski('#skF_6')), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.46/1.47  tff(c_209, plain, (k4_xboole_0(k1_tarski('#skF_6'), k1_tarski('#skF_6'))=k1_tarski('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_136, c_137, c_38])).
% 2.46/1.47  tff(c_12, plain, (![A_8, B_9]: (r1_xboole_0(A_8, B_9) | k4_xboole_0(A_8, B_9)!=A_8)), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.46/1.47  tff(c_167, plain, (![A_55, B_56, C_57]: (~r1_xboole_0(A_55, B_56) | ~r2_hidden(C_57, B_56) | ~r2_hidden(C_57, A_55))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.46/1.47  tff(c_232, plain, (![C_67, B_68, A_69]: (~r2_hidden(C_67, B_68) | ~r2_hidden(C_67, A_69) | k4_xboole_0(A_69, B_68)!=A_69)), inference(resolution, [status(thm)], [c_12, c_167])).
% 2.46/1.47  tff(c_242, plain, (![C_70, A_71]: (~r2_hidden(C_70, A_71) | k4_xboole_0(A_71, k1_tarski(C_70))!=A_71)), inference(resolution, [status(thm)], [c_16, c_232])).
% 2.46/1.47  tff(c_245, plain, (~r2_hidden('#skF_6', k1_tarski('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_209, c_242])).
% 2.46/1.47  tff(c_256, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_245])).
% 2.46/1.47  tff(c_257, plain, ('#skF_7'='#skF_6'), inference(splitRight, [status(thm)], [c_36])).
% 2.46/1.47  tff(c_258, plain, ('#skF_5'='#skF_4'), inference(splitRight, [status(thm)], [c_36])).
% 2.46/1.47  tff(c_40, plain, ('#skF_5'!='#skF_4' | k4_xboole_0(k1_tarski('#skF_6'), k1_tarski('#skF_7'))=k1_tarski('#skF_6')), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.46/1.47  tff(c_285, plain, (k4_xboole_0(k1_tarski('#skF_6'), k1_tarski('#skF_6'))=k1_tarski('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_257, c_258, c_40])).
% 2.46/1.47  tff(c_340, plain, (![A_93, B_94, C_95]: (~r1_xboole_0(A_93, B_94) | ~r2_hidden(C_95, B_94) | ~r2_hidden(C_95, A_93))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.46/1.47  tff(c_383, plain, (![C_102, B_103, A_104]: (~r2_hidden(C_102, B_103) | ~r2_hidden(C_102, A_104) | k4_xboole_0(A_104, B_103)!=A_104)), inference(resolution, [status(thm)], [c_12, c_340])).
% 2.46/1.47  tff(c_393, plain, (![C_105, A_106]: (~r2_hidden(C_105, A_106) | k4_xboole_0(A_106, k1_tarski(C_105))!=A_106)), inference(resolution, [status(thm)], [c_16, c_383])).
% 2.46/1.47  tff(c_400, plain, (~r2_hidden('#skF_6', k1_tarski('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_285, c_393])).
% 2.46/1.47  tff(c_405, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_400])).
% 2.46/1.47  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.46/1.47  
% 2.46/1.47  Inference rules
% 2.46/1.47  ----------------------
% 2.46/1.47  #Ref     : 0
% 2.46/1.47  #Sup     : 83
% 2.46/1.47  #Fact    : 0
% 2.46/1.47  #Define  : 0
% 2.46/1.47  #Split   : 2
% 2.46/1.47  #Chain   : 0
% 2.46/1.47  #Close   : 0
% 2.46/1.47  
% 2.46/1.47  Ordering : KBO
% 2.46/1.47  
% 2.46/1.47  Simplification rules
% 2.46/1.47  ----------------------
% 2.46/1.47  #Subsume      : 2
% 2.46/1.47  #Demod        : 15
% 2.46/1.47  #Tautology    : 50
% 2.46/1.48  #SimpNegUnit  : 1
% 2.46/1.48  #BackRed      : 0
% 2.46/1.48  
% 2.46/1.48  #Partial instantiations: 0
% 2.46/1.48  #Strategies tried      : 1
% 2.46/1.48  
% 2.46/1.48  Timing (in seconds)
% 2.46/1.48  ----------------------
% 2.46/1.48  Preprocessing        : 0.44
% 2.46/1.48  Parsing              : 0.21
% 2.46/1.48  CNF conversion       : 0.04
% 2.46/1.48  Main loop            : 0.25
% 2.46/1.48  Inferencing          : 0.10
% 2.46/1.48  Reduction            : 0.06
% 2.46/1.48  Demodulation         : 0.04
% 2.46/1.48  BG Simplification    : 0.02
% 2.46/1.48  Subsumption          : 0.04
% 2.46/1.48  Abstraction          : 0.02
% 2.46/1.48  MUC search           : 0.00
% 2.46/1.48  Cooper               : 0.00
% 2.46/1.48  Total                : 0.73
% 2.46/1.48  Index Insertion      : 0.00
% 2.46/1.48  Index Deletion       : 0.00
% 2.46/1.48  Index Matching       : 0.00
% 2.46/1.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
