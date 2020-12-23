%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:58 EST 2020

% Result     : Theorem 2.01s
% Output     : CNFRefutation 2.01s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 178 expanded)
%              Number of leaves         :   23 (  64 expanded)
%              Depth                    :    7
%              Number of atoms          :   88 ( 315 expanded)
%              Number of equality atoms :   38 ( 188 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_xboole_0 > r2_xboole_0 > r2_hidden > r1_xboole_0 > r1_tarski > k4_enumset1 > k3_enumset1 > k1_enumset1 > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(r3_xboole_0,type,(
    r3_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_76,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(A,k1_tarski(B))
      <=> ( A = k1_xboole_0
          | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_69,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_52,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),B)
        & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l24_zfmisc_1)).

tff(c_42,plain,
    ( ~ r1_tarski('#skF_2',k1_tarski('#skF_3'))
    | k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_56,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_38,plain,
    ( ~ r1_tarski('#skF_2',k1_tarski('#skF_3'))
    | k1_tarski('#skF_5') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_67,plain,(
    k1_tarski('#skF_5') != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_84,plain,(
    ! [A_43,B_44] :
      ( ~ r2_hidden('#skF_1'(A_43,B_44),B_44)
      | r1_tarski(A_43,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_89,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_84])).

tff(c_48,plain,
    ( k1_tarski('#skF_3') = '#skF_2'
    | k1_xboole_0 = '#skF_2'
    | r1_tarski('#skF_4',k1_tarski('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_127,plain,(
    r1_tarski('#skF_4',k1_tarski('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_32,plain,(
    ! [B_23,A_22] :
      ( k1_tarski(B_23) = A_22
      | k1_xboole_0 = A_22
      | ~ r1_tarski(A_22,k1_tarski(B_23)) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_130,plain,
    ( k1_tarski('#skF_5') = '#skF_4'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_127,c_32])).

tff(c_134,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_67,c_130])).

tff(c_135,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_tarski('#skF_3') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_137,plain,(
    k1_tarski('#skF_3') = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_135])).

tff(c_46,plain,
    ( ~ r1_tarski('#skF_2',k1_tarski('#skF_3'))
    | r1_tarski('#skF_4',k1_tarski('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_83,plain,(
    ~ r1_tarski('#skF_2',k1_tarski('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_138,plain,(
    ~ r1_tarski('#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_83])).

tff(c_141,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_138])).

tff(c_142,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_135])).

tff(c_22,plain,(
    ! [A_10] : r1_xboole_0(A_10,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_68,plain,(
    ! [A_37,B_38] :
      ( ~ r2_hidden(A_37,B_38)
      | ~ r1_xboole_0(k1_tarski(A_37),B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_73,plain,(
    ! [A_37] : ~ r2_hidden(A_37,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_22,c_68])).

tff(c_159,plain,(
    ! [A_51] : ~ r2_hidden(A_51,'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_73])).

tff(c_164,plain,(
    ! [B_2] : r1_tarski('#skF_2',B_2) ),
    inference(resolution,[status(thm)],[c_6,c_159])).

tff(c_171,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_164,c_83])).

tff(c_172,plain,(
    r1_tarski('#skF_4',k1_tarski('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_209,plain,(
    ! [B_63,A_64] :
      ( k1_tarski(B_63) = A_64
      | k1_xboole_0 = A_64
      | ~ r1_tarski(A_64,k1_tarski(B_63)) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_219,plain,
    ( k1_tarski('#skF_5') = '#skF_4'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_172,c_209])).

tff(c_230,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_67,c_219])).

tff(c_232,plain,(
    k1_tarski('#skF_5') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_40,plain,
    ( k1_tarski('#skF_3') = '#skF_2'
    | k1_xboole_0 = '#skF_2'
    | k1_tarski('#skF_5') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_248,plain,
    ( k1_tarski('#skF_3') = '#skF_2'
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_232,c_40])).

tff(c_249,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_248])).

tff(c_36,plain,(
    ! [B_23] : r1_tarski(k1_xboole_0,k1_tarski(B_23)) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_252,plain,(
    ! [B_23] : r1_tarski('#skF_2',k1_tarski(B_23)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_249,c_36])).

tff(c_231,plain,(
    ~ r1_tarski('#skF_2',k1_tarski('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_265,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_252,c_231])).

tff(c_266,plain,(
    k1_tarski('#skF_3') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_248])).

tff(c_34,plain,(
    ! [B_23] : r1_tarski(k1_tarski(B_23),k1_tarski(B_23)) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_274,plain,(
    r1_tarski(k1_tarski('#skF_3'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_266,c_34])).

tff(c_280,plain,(
    r1_tarski('#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_266,c_274])).

tff(c_286,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_280,c_266,c_231])).

tff(c_288,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_289,plain,(
    ! [B_23] : r1_tarski('#skF_4',k1_tarski(B_23)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_288,c_36])).

tff(c_44,plain,
    ( k1_tarski('#skF_3') = '#skF_2'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_298,plain,
    ( k1_tarski('#skF_3') = '#skF_2'
    | '#skF_2' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_288,c_288,c_44])).

tff(c_299,plain,(
    '#skF_2' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_298])).

tff(c_287,plain,(
    ~ r1_tarski('#skF_2',k1_tarski('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_300,plain,(
    ~ r1_tarski('#skF_4',k1_tarski('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_299,c_287])).

tff(c_303,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_289,c_300])).

tff(c_304,plain,(
    k1_tarski('#skF_3') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_298])).

tff(c_306,plain,(
    ~ r1_tarski('#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_304,c_287])).

tff(c_312,plain,(
    r1_tarski('#skF_2',k1_tarski('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_304,c_34])).

tff(c_318,plain,(
    r1_tarski('#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_304,c_312])).

tff(c_330,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_306,c_318])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:46:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.01/1.27  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.01/1.28  
% 2.01/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.01/1.28  %$ r3_xboole_0 > r2_xboole_0 > r2_hidden > r1_xboole_0 > r1_tarski > k4_enumset1 > k3_enumset1 > k1_enumset1 > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.01/1.28  
% 2.01/1.28  %Foreground sorts:
% 2.01/1.28  
% 2.01/1.28  
% 2.01/1.28  %Background operators:
% 2.01/1.28  
% 2.01/1.28  
% 2.01/1.28  %Foreground operators:
% 2.01/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.01/1.28  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.01/1.28  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.01/1.28  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.01/1.28  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.01/1.28  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.01/1.28  tff('#skF_5', type, '#skF_5': $i).
% 2.01/1.28  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.01/1.28  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.01/1.28  tff('#skF_2', type, '#skF_2': $i).
% 2.01/1.28  tff('#skF_3', type, '#skF_3': $i).
% 2.01/1.28  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.01/1.28  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 2.01/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.01/1.28  tff('#skF_4', type, '#skF_4': $i).
% 2.01/1.28  tff(r3_xboole_0, type, r3_xboole_0: ($i * $i) > $o).
% 2.01/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.01/1.28  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.01/1.28  
% 2.01/1.29  tff(f_76, negated_conjecture, ~(![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_zfmisc_1)).
% 2.01/1.29  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.01/1.29  tff(f_69, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 2.01/1.29  tff(f_52, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.01/1.29  tff(f_63, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 2.01/1.29  tff(c_42, plain, (~r1_tarski('#skF_2', k1_tarski('#skF_3')) | k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.01/1.29  tff(c_56, plain, (k1_xboole_0!='#skF_4'), inference(splitLeft, [status(thm)], [c_42])).
% 2.01/1.29  tff(c_38, plain, (~r1_tarski('#skF_2', k1_tarski('#skF_3')) | k1_tarski('#skF_5')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.01/1.29  tff(c_67, plain, (k1_tarski('#skF_5')!='#skF_4'), inference(splitLeft, [status(thm)], [c_38])).
% 2.01/1.29  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.01/1.29  tff(c_84, plain, (![A_43, B_44]: (~r2_hidden('#skF_1'(A_43, B_44), B_44) | r1_tarski(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.01/1.29  tff(c_89, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_84])).
% 2.01/1.29  tff(c_48, plain, (k1_tarski('#skF_3')='#skF_2' | k1_xboole_0='#skF_2' | r1_tarski('#skF_4', k1_tarski('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.01/1.29  tff(c_127, plain, (r1_tarski('#skF_4', k1_tarski('#skF_5'))), inference(splitLeft, [status(thm)], [c_48])).
% 2.01/1.29  tff(c_32, plain, (![B_23, A_22]: (k1_tarski(B_23)=A_22 | k1_xboole_0=A_22 | ~r1_tarski(A_22, k1_tarski(B_23)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.01/1.29  tff(c_130, plain, (k1_tarski('#skF_5')='#skF_4' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_127, c_32])).
% 2.01/1.29  tff(c_134, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_67, c_130])).
% 2.01/1.29  tff(c_135, plain, (k1_xboole_0='#skF_2' | k1_tarski('#skF_3')='#skF_2'), inference(splitRight, [status(thm)], [c_48])).
% 2.01/1.29  tff(c_137, plain, (k1_tarski('#skF_3')='#skF_2'), inference(splitLeft, [status(thm)], [c_135])).
% 2.01/1.29  tff(c_46, plain, (~r1_tarski('#skF_2', k1_tarski('#skF_3')) | r1_tarski('#skF_4', k1_tarski('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.01/1.29  tff(c_83, plain, (~r1_tarski('#skF_2', k1_tarski('#skF_3'))), inference(splitLeft, [status(thm)], [c_46])).
% 2.01/1.29  tff(c_138, plain, (~r1_tarski('#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_137, c_83])).
% 2.01/1.29  tff(c_141, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_89, c_138])).
% 2.01/1.29  tff(c_142, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_135])).
% 2.01/1.29  tff(c_22, plain, (![A_10]: (r1_xboole_0(A_10, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.01/1.29  tff(c_68, plain, (![A_37, B_38]: (~r2_hidden(A_37, B_38) | ~r1_xboole_0(k1_tarski(A_37), B_38))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.01/1.29  tff(c_73, plain, (![A_37]: (~r2_hidden(A_37, k1_xboole_0))), inference(resolution, [status(thm)], [c_22, c_68])).
% 2.01/1.29  tff(c_159, plain, (![A_51]: (~r2_hidden(A_51, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_142, c_73])).
% 2.01/1.29  tff(c_164, plain, (![B_2]: (r1_tarski('#skF_2', B_2))), inference(resolution, [status(thm)], [c_6, c_159])).
% 2.01/1.29  tff(c_171, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_164, c_83])).
% 2.01/1.29  tff(c_172, plain, (r1_tarski('#skF_4', k1_tarski('#skF_5'))), inference(splitRight, [status(thm)], [c_46])).
% 2.01/1.29  tff(c_209, plain, (![B_63, A_64]: (k1_tarski(B_63)=A_64 | k1_xboole_0=A_64 | ~r1_tarski(A_64, k1_tarski(B_63)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.01/1.29  tff(c_219, plain, (k1_tarski('#skF_5')='#skF_4' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_172, c_209])).
% 2.01/1.29  tff(c_230, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_67, c_219])).
% 2.01/1.29  tff(c_232, plain, (k1_tarski('#skF_5')='#skF_4'), inference(splitRight, [status(thm)], [c_38])).
% 2.01/1.29  tff(c_40, plain, (k1_tarski('#skF_3')='#skF_2' | k1_xboole_0='#skF_2' | k1_tarski('#skF_5')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.01/1.29  tff(c_248, plain, (k1_tarski('#skF_3')='#skF_2' | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_232, c_40])).
% 2.01/1.29  tff(c_249, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_248])).
% 2.01/1.29  tff(c_36, plain, (![B_23]: (r1_tarski(k1_xboole_0, k1_tarski(B_23)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.01/1.29  tff(c_252, plain, (![B_23]: (r1_tarski('#skF_2', k1_tarski(B_23)))), inference(demodulation, [status(thm), theory('equality')], [c_249, c_36])).
% 2.01/1.29  tff(c_231, plain, (~r1_tarski('#skF_2', k1_tarski('#skF_3'))), inference(splitRight, [status(thm)], [c_38])).
% 2.01/1.29  tff(c_265, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_252, c_231])).
% 2.01/1.29  tff(c_266, plain, (k1_tarski('#skF_3')='#skF_2'), inference(splitRight, [status(thm)], [c_248])).
% 2.01/1.29  tff(c_34, plain, (![B_23]: (r1_tarski(k1_tarski(B_23), k1_tarski(B_23)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.01/1.29  tff(c_274, plain, (r1_tarski(k1_tarski('#skF_3'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_266, c_34])).
% 2.01/1.29  tff(c_280, plain, (r1_tarski('#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_266, c_274])).
% 2.01/1.29  tff(c_286, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_280, c_266, c_231])).
% 2.01/1.29  tff(c_288, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_42])).
% 2.01/1.29  tff(c_289, plain, (![B_23]: (r1_tarski('#skF_4', k1_tarski(B_23)))), inference(demodulation, [status(thm), theory('equality')], [c_288, c_36])).
% 2.01/1.29  tff(c_44, plain, (k1_tarski('#skF_3')='#skF_2' | k1_xboole_0='#skF_2' | k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.01/1.29  tff(c_298, plain, (k1_tarski('#skF_3')='#skF_2' | '#skF_2'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_288, c_288, c_44])).
% 2.01/1.29  tff(c_299, plain, ('#skF_2'='#skF_4'), inference(splitLeft, [status(thm)], [c_298])).
% 2.01/1.29  tff(c_287, plain, (~r1_tarski('#skF_2', k1_tarski('#skF_3'))), inference(splitRight, [status(thm)], [c_42])).
% 2.01/1.29  tff(c_300, plain, (~r1_tarski('#skF_4', k1_tarski('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_299, c_287])).
% 2.01/1.29  tff(c_303, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_289, c_300])).
% 2.01/1.29  tff(c_304, plain, (k1_tarski('#skF_3')='#skF_2'), inference(splitRight, [status(thm)], [c_298])).
% 2.01/1.29  tff(c_306, plain, (~r1_tarski('#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_304, c_287])).
% 2.01/1.29  tff(c_312, plain, (r1_tarski('#skF_2', k1_tarski('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_304, c_34])).
% 2.01/1.29  tff(c_318, plain, (r1_tarski('#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_304, c_312])).
% 2.01/1.29  tff(c_330, plain, $false, inference(negUnitSimplification, [status(thm)], [c_306, c_318])).
% 2.01/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.01/1.29  
% 2.01/1.29  Inference rules
% 2.01/1.29  ----------------------
% 2.01/1.29  #Ref     : 0
% 2.01/1.29  #Sup     : 51
% 2.01/1.29  #Fact    : 0
% 2.01/1.29  #Define  : 0
% 2.01/1.29  #Split   : 7
% 2.01/1.29  #Chain   : 0
% 2.01/1.29  #Close   : 0
% 2.01/1.29  
% 2.01/1.29  Ordering : KBO
% 2.01/1.29  
% 2.01/1.29  Simplification rules
% 2.01/1.29  ----------------------
% 2.01/1.29  #Subsume      : 3
% 2.01/1.29  #Demod        : 42
% 2.01/1.29  #Tautology    : 34
% 2.01/1.29  #SimpNegUnit  : 3
% 2.01/1.29  #BackRed      : 15
% 2.01/1.29  
% 2.01/1.29  #Partial instantiations: 0
% 2.01/1.29  #Strategies tried      : 1
% 2.01/1.29  
% 2.01/1.29  Timing (in seconds)
% 2.01/1.29  ----------------------
% 2.01/1.29  Preprocessing        : 0.29
% 2.01/1.29  Parsing              : 0.15
% 2.01/1.29  CNF conversion       : 0.02
% 2.01/1.30  Main loop            : 0.20
% 2.01/1.30  Inferencing          : 0.07
% 2.01/1.30  Reduction            : 0.06
% 2.01/1.30  Demodulation         : 0.05
% 2.01/1.30  BG Simplification    : 0.02
% 2.01/1.30  Subsumption          : 0.03
% 2.01/1.30  Abstraction          : 0.01
% 2.01/1.30  MUC search           : 0.00
% 2.01/1.30  Cooper               : 0.00
% 2.01/1.30  Total                : 0.52
% 2.01/1.30  Index Insertion      : 0.00
% 2.01/1.30  Index Deletion       : 0.00
% 2.01/1.30  Index Matching       : 0.00
% 2.01/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
