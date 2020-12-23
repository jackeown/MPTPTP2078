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
% DateTime   : Thu Dec  3 09:48:37 EST 2020

% Result     : Theorem 2.10s
% Output     : CNFRefutation 2.10s
% Verified   : 
% Statistics : Number of formulae       :   57 (  87 expanded)
%              Number of leaves         :   26 (  42 expanded)
%              Depth                    :    6
%              Number of atoms          :   57 ( 114 expanded)
%              Number of equality atoms :   32 (  79 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_8 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_52,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(f_67,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
      <=> A != B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( A != B
     => r1_xboole_0(k1_tarski(A),k1_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(c_44,plain,(
    ! [A_17] : k2_tarski(A_17,A_17) = k1_tarski(A_17) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_332,plain,(
    ! [D_88,B_89] : r2_hidden(D_88,k2_tarski(D_88,B_89)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_335,plain,(
    ! [A_17] : r2_hidden(A_17,k1_tarski(A_17)) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_332])).

tff(c_61,plain,(
    ! [A_27] : k2_tarski(A_27,A_27) = k1_tarski(A_27) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_28,plain,(
    ! [D_16,A_11] : r2_hidden(D_16,k2_tarski(A_11,D_16)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_67,plain,(
    ! [A_27] : r2_hidden(A_27,k1_tarski(A_27)) ),
    inference(superposition,[status(thm),theory(equality)],[c_61,c_28])).

tff(c_54,plain,
    ( '#skF_5' != '#skF_6'
    | '#skF_7' = '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_59,plain,(
    '#skF_5' != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_95,plain,(
    ! [A_37,B_38] :
      ( r1_xboole_0(k1_tarski(A_37),k1_tarski(B_38))
      | B_38 = A_37 ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_22,plain,(
    ! [A_9,B_10] :
      ( k4_xboole_0(A_9,B_10) = A_9
      | ~ r1_xboole_0(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_141,plain,(
    ! [A_55,B_56] :
      ( k4_xboole_0(k1_tarski(A_55),k1_tarski(B_56)) = k1_tarski(A_55)
      | B_56 = A_55 ) ),
    inference(resolution,[status(thm)],[c_95,c_22])).

tff(c_52,plain,
    ( k4_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6')) != k1_tarski('#skF_5')
    | '#skF_7' = '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_94,plain,(
    k4_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6')) != k1_tarski('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_153,plain,(
    '#skF_5' = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_141,c_94])).

tff(c_161,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_59,c_153])).

tff(c_162,plain,(
    '#skF_7' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_163,plain,(
    k4_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6')) = k1_tarski('#skF_5') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_56,plain,
    ( k4_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6')) != k1_tarski('#skF_5')
    | k4_xboole_0(k1_tarski('#skF_7'),k1_tarski('#skF_8')) = k1_tarski('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_282,plain,(
    k4_xboole_0(k1_tarski('#skF_8'),k1_tarski('#skF_8')) = k1_tarski('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_162,c_162,c_163,c_56])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( ~ r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,k4_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_304,plain,(
    ! [D_86] :
      ( ~ r2_hidden(D_86,k1_tarski('#skF_8'))
      | ~ r2_hidden(D_86,k1_tarski('#skF_8')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_282,c_4])).

tff(c_307,plain,(
    ~ r2_hidden('#skF_8',k1_tarski('#skF_8')) ),
    inference(resolution,[status(thm)],[c_67,c_304])).

tff(c_311,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_307])).

tff(c_312,plain,(
    '#skF_7' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_313,plain,(
    '#skF_5' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_58,plain,
    ( '#skF_5' != '#skF_6'
    | k4_xboole_0(k1_tarski('#skF_7'),k1_tarski('#skF_8')) = k1_tarski('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_354,plain,(
    k4_xboole_0(k1_tarski('#skF_8'),k1_tarski('#skF_8')) = k1_tarski('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_312,c_312,c_313,c_58])).

tff(c_373,plain,(
    ! [D_104,B_105,A_106] :
      ( ~ r2_hidden(D_104,B_105)
      | ~ r2_hidden(D_104,k4_xboole_0(A_106,B_105)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_400,plain,(
    ! [D_112] :
      ( ~ r2_hidden(D_112,k1_tarski('#skF_8'))
      | ~ r2_hidden(D_112,k1_tarski('#skF_8')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_354,c_373])).

tff(c_403,plain,(
    ~ r2_hidden('#skF_8',k1_tarski('#skF_8')) ),
    inference(resolution,[status(thm)],[c_335,c_400])).

tff(c_407,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_335,c_403])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:28:57 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.10/1.35  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.10/1.36  
% 2.10/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.10/1.36  %$ r2_hidden > r1_xboole_0 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_8 > #skF_3
% 2.10/1.36  
% 2.10/1.36  %Foreground sorts:
% 2.10/1.36  
% 2.10/1.36  
% 2.10/1.36  %Background operators:
% 2.10/1.36  
% 2.10/1.36  
% 2.10/1.36  %Foreground operators:
% 2.10/1.36  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.10/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.10/1.36  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.10/1.36  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.10/1.36  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.10/1.36  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.10/1.36  tff('#skF_7', type, '#skF_7': $i).
% 2.10/1.36  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.10/1.36  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.10/1.36  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.10/1.36  tff('#skF_5', type, '#skF_5': $i).
% 2.10/1.36  tff('#skF_6', type, '#skF_6': $i).
% 2.10/1.36  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.10/1.36  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.10/1.36  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.10/1.36  tff('#skF_8', type, '#skF_8': $i).
% 2.10/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.10/1.36  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.10/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.10/1.36  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.10/1.36  
% 2.10/1.37  tff(f_52, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.10/1.37  tff(f_50, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 2.10/1.37  tff(f_67, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 2.10/1.37  tff(f_61, axiom, (![A, B]: (~(A = B) => r1_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_zfmisc_1)).
% 2.10/1.37  tff(f_41, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.10/1.37  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 2.10/1.37  tff(c_44, plain, (![A_17]: (k2_tarski(A_17, A_17)=k1_tarski(A_17))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.10/1.37  tff(c_332, plain, (![D_88, B_89]: (r2_hidden(D_88, k2_tarski(D_88, B_89)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.10/1.37  tff(c_335, plain, (![A_17]: (r2_hidden(A_17, k1_tarski(A_17)))), inference(superposition, [status(thm), theory('equality')], [c_44, c_332])).
% 2.10/1.37  tff(c_61, plain, (![A_27]: (k2_tarski(A_27, A_27)=k1_tarski(A_27))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.10/1.37  tff(c_28, plain, (![D_16, A_11]: (r2_hidden(D_16, k2_tarski(A_11, D_16)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.10/1.37  tff(c_67, plain, (![A_27]: (r2_hidden(A_27, k1_tarski(A_27)))), inference(superposition, [status(thm), theory('equality')], [c_61, c_28])).
% 2.10/1.37  tff(c_54, plain, ('#skF_5'!='#skF_6' | '#skF_7'='#skF_8'), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.10/1.37  tff(c_59, plain, ('#skF_5'!='#skF_6'), inference(splitLeft, [status(thm)], [c_54])).
% 2.10/1.37  tff(c_95, plain, (![A_37, B_38]: (r1_xboole_0(k1_tarski(A_37), k1_tarski(B_38)) | B_38=A_37)), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.10/1.37  tff(c_22, plain, (![A_9, B_10]: (k4_xboole_0(A_9, B_10)=A_9 | ~r1_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.10/1.37  tff(c_141, plain, (![A_55, B_56]: (k4_xboole_0(k1_tarski(A_55), k1_tarski(B_56))=k1_tarski(A_55) | B_56=A_55)), inference(resolution, [status(thm)], [c_95, c_22])).
% 2.10/1.37  tff(c_52, plain, (k4_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6'))!=k1_tarski('#skF_5') | '#skF_7'='#skF_8'), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.10/1.37  tff(c_94, plain, (k4_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6'))!=k1_tarski('#skF_5')), inference(splitLeft, [status(thm)], [c_52])).
% 2.10/1.37  tff(c_153, plain, ('#skF_5'='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_141, c_94])).
% 2.10/1.37  tff(c_161, plain, $false, inference(negUnitSimplification, [status(thm)], [c_59, c_153])).
% 2.10/1.37  tff(c_162, plain, ('#skF_7'='#skF_8'), inference(splitRight, [status(thm)], [c_52])).
% 2.10/1.37  tff(c_163, plain, (k4_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6'))=k1_tarski('#skF_5')), inference(splitRight, [status(thm)], [c_52])).
% 2.10/1.37  tff(c_56, plain, (k4_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6'))!=k1_tarski('#skF_5') | k4_xboole_0(k1_tarski('#skF_7'), k1_tarski('#skF_8'))=k1_tarski('#skF_7')), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.10/1.37  tff(c_282, plain, (k4_xboole_0(k1_tarski('#skF_8'), k1_tarski('#skF_8'))=k1_tarski('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_162, c_162, c_163, c_56])).
% 2.10/1.37  tff(c_4, plain, (![D_6, B_2, A_1]: (~r2_hidden(D_6, B_2) | ~r2_hidden(D_6, k4_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.10/1.37  tff(c_304, plain, (![D_86]: (~r2_hidden(D_86, k1_tarski('#skF_8')) | ~r2_hidden(D_86, k1_tarski('#skF_8')))), inference(superposition, [status(thm), theory('equality')], [c_282, c_4])).
% 2.10/1.37  tff(c_307, plain, (~r2_hidden('#skF_8', k1_tarski('#skF_8'))), inference(resolution, [status(thm)], [c_67, c_304])).
% 2.10/1.37  tff(c_311, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_67, c_307])).
% 2.10/1.37  tff(c_312, plain, ('#skF_7'='#skF_8'), inference(splitRight, [status(thm)], [c_54])).
% 2.10/1.37  tff(c_313, plain, ('#skF_5'='#skF_6'), inference(splitRight, [status(thm)], [c_54])).
% 2.10/1.37  tff(c_58, plain, ('#skF_5'!='#skF_6' | k4_xboole_0(k1_tarski('#skF_7'), k1_tarski('#skF_8'))=k1_tarski('#skF_7')), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.10/1.37  tff(c_354, plain, (k4_xboole_0(k1_tarski('#skF_8'), k1_tarski('#skF_8'))=k1_tarski('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_312, c_312, c_313, c_58])).
% 2.10/1.37  tff(c_373, plain, (![D_104, B_105, A_106]: (~r2_hidden(D_104, B_105) | ~r2_hidden(D_104, k4_xboole_0(A_106, B_105)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.10/1.37  tff(c_400, plain, (![D_112]: (~r2_hidden(D_112, k1_tarski('#skF_8')) | ~r2_hidden(D_112, k1_tarski('#skF_8')))), inference(superposition, [status(thm), theory('equality')], [c_354, c_373])).
% 2.10/1.37  tff(c_403, plain, (~r2_hidden('#skF_8', k1_tarski('#skF_8'))), inference(resolution, [status(thm)], [c_335, c_400])).
% 2.10/1.37  tff(c_407, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_335, c_403])).
% 2.10/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.10/1.37  
% 2.10/1.37  Inference rules
% 2.10/1.37  ----------------------
% 2.10/1.37  #Ref     : 0
% 2.10/1.37  #Sup     : 79
% 2.10/1.37  #Fact    : 0
% 2.10/1.37  #Define  : 0
% 2.10/1.37  #Split   : 3
% 2.10/1.37  #Chain   : 0
% 2.10/1.37  #Close   : 0
% 2.10/1.37  
% 2.10/1.37  Ordering : KBO
% 2.10/1.37  
% 2.10/1.37  Simplification rules
% 2.10/1.37  ----------------------
% 2.10/1.37  #Subsume      : 4
% 2.10/1.37  #Demod        : 14
% 2.10/1.37  #Tautology    : 60
% 2.10/1.37  #SimpNegUnit  : 3
% 2.10/1.37  #BackRed      : 0
% 2.10/1.37  
% 2.10/1.37  #Partial instantiations: 0
% 2.10/1.37  #Strategies tried      : 1
% 2.10/1.37  
% 2.10/1.37  Timing (in seconds)
% 2.10/1.37  ----------------------
% 2.10/1.38  Preprocessing        : 0.34
% 2.10/1.38  Parsing              : 0.17
% 2.10/1.38  CNF conversion       : 0.03
% 2.10/1.38  Main loop            : 0.22
% 2.10/1.38  Inferencing          : 0.08
% 2.10/1.38  Reduction            : 0.07
% 2.10/1.38  Demodulation         : 0.05
% 2.10/1.38  BG Simplification    : 0.02
% 2.10/1.38  Subsumption          : 0.04
% 2.10/1.38  Abstraction          : 0.01
% 2.10/1.38  MUC search           : 0.00
% 2.10/1.38  Cooper               : 0.00
% 2.10/1.38  Total                : 0.59
% 2.10/1.38  Index Insertion      : 0.00
% 2.10/1.38  Index Deletion       : 0.00
% 2.10/1.38  Index Matching       : 0.00
% 2.10/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
