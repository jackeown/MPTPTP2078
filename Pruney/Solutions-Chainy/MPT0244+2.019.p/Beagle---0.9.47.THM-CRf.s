%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:58 EST 2020

% Result     : Theorem 1.88s
% Output     : CNFRefutation 1.88s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 174 expanded)
%              Number of leaves         :   14 (  57 expanded)
%              Depth                    :    7
%              Number of atoms          :   75 ( 320 expanded)
%              Number of equality atoms :   38 ( 206 expanded)
%              Maximal formula depth    :    6 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k1_enumset1 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_57,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(A,k1_tarski(B))
      <=> ( A = k1_xboole_0
          | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(c_26,plain,
    ( ~ r1_tarski('#skF_1',k1_tarski('#skF_2'))
    | k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_58,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_26])).

tff(c_22,plain,
    ( ~ r1_tarski('#skF_1',k1_tarski('#skF_2'))
    | k1_tarski('#skF_4') != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_68,plain,(
    k1_tarski('#skF_4') != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_22])).

tff(c_32,plain,
    ( k1_tarski('#skF_2') = '#skF_1'
    | k1_xboole_0 = '#skF_1'
    | r1_tarski('#skF_3',k1_tarski('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_79,plain,(
    r1_tarski('#skF_3',k1_tarski('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_80,plain,(
    ! [B_22,A_23] :
      ( k1_tarski(B_22) = A_23
      | k1_xboole_0 = A_23
      | ~ r1_tarski(A_23,k1_tarski(B_22)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_83,plain,
    ( k1_tarski('#skF_4') = '#skF_3'
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_79,c_80])).

tff(c_93,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_68,c_83])).

tff(c_94,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_tarski('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_96,plain,(
    k1_tarski('#skF_2') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_94])).

tff(c_30,plain,
    ( ~ r1_tarski('#skF_1',k1_tarski('#skF_2'))
    | r1_tarski('#skF_3',k1_tarski('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_78,plain,(
    ~ r1_tarski('#skF_1',k1_tarski('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_97,plain,(
    ~ r1_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_78])).

tff(c_8,plain,(
    ! [B_5] : r1_tarski(k1_tarski(B_5),k1_tarski(B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_110,plain,(
    r1_tarski(k1_tarski('#skF_2'),'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_8])).

tff(c_116,plain,(
    r1_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_110])).

tff(c_118,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_97,c_116])).

tff(c_119,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_94])).

tff(c_10,plain,(
    ! [B_5] : r1_tarski(k1_xboole_0,k1_tarski(B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_123,plain,(
    ! [B_5] : r1_tarski('#skF_1',k1_tarski(B_5)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_10])).

tff(c_130,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_78])).

tff(c_131,plain,(
    r1_tarski('#skF_3',k1_tarski('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_134,plain,(
    ! [B_24,A_25] :
      ( k1_tarski(B_24) = A_25
      | k1_xboole_0 = A_25
      | ~ r1_tarski(A_25,k1_tarski(B_24)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_140,plain,
    ( k1_tarski('#skF_4') = '#skF_3'
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_131,c_134])).

tff(c_151,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_68,c_140])).

tff(c_153,plain,(
    k1_tarski('#skF_4') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_22])).

tff(c_24,plain,
    ( k1_tarski('#skF_2') = '#skF_1'
    | k1_xboole_0 = '#skF_1'
    | k1_tarski('#skF_4') != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_198,plain,
    ( k1_tarski('#skF_2') = '#skF_1'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_153,c_24])).

tff(c_199,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_198])).

tff(c_203,plain,(
    ! [B_5] : r1_tarski('#skF_1',k1_tarski(B_5)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_199,c_10])).

tff(c_152,plain,(
    ~ r1_tarski('#skF_1',k1_tarski('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_22])).

tff(c_210,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_203,c_152])).

tff(c_211,plain,(
    k1_tarski('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_198])).

tff(c_214,plain,(
    ~ r1_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_211,c_152])).

tff(c_227,plain,(
    r1_tarski(k1_tarski('#skF_2'),'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_211,c_8])).

tff(c_233,plain,(
    r1_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_211,c_227])).

tff(c_235,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_214,c_233])).

tff(c_237,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_28,plain,
    ( k1_tarski('#skF_2') = '#skF_1'
    | k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_250,plain,
    ( k1_tarski('#skF_2') = '#skF_1'
    | '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_237,c_237,c_28])).

tff(c_251,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_250])).

tff(c_239,plain,(
    ! [B_5] : r1_tarski('#skF_3',k1_tarski(B_5)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_237,c_10])).

tff(c_253,plain,(
    ! [B_5] : r1_tarski('#skF_1',k1_tarski(B_5)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_251,c_239])).

tff(c_236,plain,(
    ~ r1_tarski('#skF_1',k1_tarski('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_265,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_253,c_236])).

tff(c_266,plain,(
    k1_tarski('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_250])).

tff(c_268,plain,(
    ~ r1_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_266,c_236])).

tff(c_283,plain,(
    r1_tarski(k1_tarski('#skF_2'),'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_266,c_8])).

tff(c_287,plain,(
    r1_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_266,c_283])).

tff(c_289,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_268,c_287])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:20:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.88/1.20  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.88/1.21  
% 1.88/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.88/1.21  %$ r1_tarski > k1_enumset1 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.88/1.21  
% 1.88/1.21  %Foreground sorts:
% 1.88/1.21  
% 1.88/1.21  
% 1.88/1.21  %Background operators:
% 1.88/1.21  
% 1.88/1.21  
% 1.88/1.21  %Foreground operators:
% 1.88/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.88/1.21  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.88/1.21  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.88/1.21  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.88/1.21  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.88/1.21  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.88/1.21  tff('#skF_2', type, '#skF_2': $i).
% 1.88/1.21  tff('#skF_3', type, '#skF_3': $i).
% 1.88/1.21  tff('#skF_1', type, '#skF_1': $i).
% 1.88/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.88/1.21  tff('#skF_4', type, '#skF_4': $i).
% 1.88/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.88/1.21  
% 1.88/1.22  tff(f_57, negated_conjecture, ~(![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_zfmisc_1)).
% 1.88/1.22  tff(f_35, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 1.88/1.22  tff(c_26, plain, (~r1_tarski('#skF_1', k1_tarski('#skF_2')) | k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.88/1.22  tff(c_58, plain, (k1_xboole_0!='#skF_3'), inference(splitLeft, [status(thm)], [c_26])).
% 1.88/1.22  tff(c_22, plain, (~r1_tarski('#skF_1', k1_tarski('#skF_2')) | k1_tarski('#skF_4')!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.88/1.22  tff(c_68, plain, (k1_tarski('#skF_4')!='#skF_3'), inference(splitLeft, [status(thm)], [c_22])).
% 1.88/1.22  tff(c_32, plain, (k1_tarski('#skF_2')='#skF_1' | k1_xboole_0='#skF_1' | r1_tarski('#skF_3', k1_tarski('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.88/1.22  tff(c_79, plain, (r1_tarski('#skF_3', k1_tarski('#skF_4'))), inference(splitLeft, [status(thm)], [c_32])).
% 1.88/1.22  tff(c_80, plain, (![B_22, A_23]: (k1_tarski(B_22)=A_23 | k1_xboole_0=A_23 | ~r1_tarski(A_23, k1_tarski(B_22)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.88/1.22  tff(c_83, plain, (k1_tarski('#skF_4')='#skF_3' | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_79, c_80])).
% 1.88/1.22  tff(c_93, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_68, c_83])).
% 1.88/1.22  tff(c_94, plain, (k1_xboole_0='#skF_1' | k1_tarski('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_32])).
% 1.88/1.22  tff(c_96, plain, (k1_tarski('#skF_2')='#skF_1'), inference(splitLeft, [status(thm)], [c_94])).
% 1.88/1.22  tff(c_30, plain, (~r1_tarski('#skF_1', k1_tarski('#skF_2')) | r1_tarski('#skF_3', k1_tarski('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.88/1.22  tff(c_78, plain, (~r1_tarski('#skF_1', k1_tarski('#skF_2'))), inference(splitLeft, [status(thm)], [c_30])).
% 1.88/1.22  tff(c_97, plain, (~r1_tarski('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_96, c_78])).
% 1.88/1.22  tff(c_8, plain, (![B_5]: (r1_tarski(k1_tarski(B_5), k1_tarski(B_5)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.88/1.22  tff(c_110, plain, (r1_tarski(k1_tarski('#skF_2'), '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_96, c_8])).
% 1.88/1.22  tff(c_116, plain, (r1_tarski('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_96, c_110])).
% 1.88/1.22  tff(c_118, plain, $false, inference(negUnitSimplification, [status(thm)], [c_97, c_116])).
% 1.88/1.22  tff(c_119, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_94])).
% 1.88/1.22  tff(c_10, plain, (![B_5]: (r1_tarski(k1_xboole_0, k1_tarski(B_5)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.88/1.22  tff(c_123, plain, (![B_5]: (r1_tarski('#skF_1', k1_tarski(B_5)))), inference(demodulation, [status(thm), theory('equality')], [c_119, c_10])).
% 1.88/1.22  tff(c_130, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_123, c_78])).
% 1.88/1.22  tff(c_131, plain, (r1_tarski('#skF_3', k1_tarski('#skF_4'))), inference(splitRight, [status(thm)], [c_30])).
% 1.88/1.22  tff(c_134, plain, (![B_24, A_25]: (k1_tarski(B_24)=A_25 | k1_xboole_0=A_25 | ~r1_tarski(A_25, k1_tarski(B_24)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.88/1.22  tff(c_140, plain, (k1_tarski('#skF_4')='#skF_3' | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_131, c_134])).
% 1.88/1.22  tff(c_151, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_68, c_140])).
% 1.88/1.22  tff(c_153, plain, (k1_tarski('#skF_4')='#skF_3'), inference(splitRight, [status(thm)], [c_22])).
% 1.88/1.22  tff(c_24, plain, (k1_tarski('#skF_2')='#skF_1' | k1_xboole_0='#skF_1' | k1_tarski('#skF_4')!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.88/1.22  tff(c_198, plain, (k1_tarski('#skF_2')='#skF_1' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_153, c_24])).
% 1.88/1.22  tff(c_199, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_198])).
% 1.88/1.22  tff(c_203, plain, (![B_5]: (r1_tarski('#skF_1', k1_tarski(B_5)))), inference(demodulation, [status(thm), theory('equality')], [c_199, c_10])).
% 1.88/1.22  tff(c_152, plain, (~r1_tarski('#skF_1', k1_tarski('#skF_2'))), inference(splitRight, [status(thm)], [c_22])).
% 1.88/1.22  tff(c_210, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_203, c_152])).
% 1.88/1.22  tff(c_211, plain, (k1_tarski('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_198])).
% 1.88/1.22  tff(c_214, plain, (~r1_tarski('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_211, c_152])).
% 1.88/1.22  tff(c_227, plain, (r1_tarski(k1_tarski('#skF_2'), '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_211, c_8])).
% 1.88/1.22  tff(c_233, plain, (r1_tarski('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_211, c_227])).
% 1.88/1.22  tff(c_235, plain, $false, inference(negUnitSimplification, [status(thm)], [c_214, c_233])).
% 1.88/1.22  tff(c_237, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_26])).
% 1.88/1.22  tff(c_28, plain, (k1_tarski('#skF_2')='#skF_1' | k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.88/1.22  tff(c_250, plain, (k1_tarski('#skF_2')='#skF_1' | '#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_237, c_237, c_28])).
% 1.88/1.22  tff(c_251, plain, ('#skF_3'='#skF_1'), inference(splitLeft, [status(thm)], [c_250])).
% 1.88/1.22  tff(c_239, plain, (![B_5]: (r1_tarski('#skF_3', k1_tarski(B_5)))), inference(demodulation, [status(thm), theory('equality')], [c_237, c_10])).
% 1.88/1.22  tff(c_253, plain, (![B_5]: (r1_tarski('#skF_1', k1_tarski(B_5)))), inference(demodulation, [status(thm), theory('equality')], [c_251, c_239])).
% 1.88/1.22  tff(c_236, plain, (~r1_tarski('#skF_1', k1_tarski('#skF_2'))), inference(splitRight, [status(thm)], [c_26])).
% 1.88/1.22  tff(c_265, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_253, c_236])).
% 1.88/1.22  tff(c_266, plain, (k1_tarski('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_250])).
% 1.88/1.22  tff(c_268, plain, (~r1_tarski('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_266, c_236])).
% 1.88/1.22  tff(c_283, plain, (r1_tarski(k1_tarski('#skF_2'), '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_266, c_8])).
% 1.88/1.22  tff(c_287, plain, (r1_tarski('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_266, c_283])).
% 1.88/1.22  tff(c_289, plain, $false, inference(negUnitSimplification, [status(thm)], [c_268, c_287])).
% 1.88/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.88/1.22  
% 1.88/1.22  Inference rules
% 1.88/1.22  ----------------------
% 1.88/1.22  #Ref     : 0
% 1.88/1.22  #Sup     : 59
% 1.88/1.22  #Fact    : 0
% 1.88/1.22  #Define  : 0
% 1.88/1.22  #Split   : 7
% 1.88/1.22  #Chain   : 0
% 1.88/1.22  #Close   : 0
% 1.88/1.22  
% 1.88/1.22  Ordering : KBO
% 1.88/1.22  
% 1.88/1.22  Simplification rules
% 1.88/1.22  ----------------------
% 1.88/1.22  #Subsume      : 5
% 1.88/1.22  #Demod        : 47
% 1.88/1.22  #Tautology    : 35
% 1.88/1.22  #SimpNegUnit  : 5
% 1.88/1.22  #BackRed      : 18
% 1.88/1.22  
% 1.88/1.22  #Partial instantiations: 0
% 1.88/1.22  #Strategies tried      : 1
% 1.88/1.22  
% 1.88/1.22  Timing (in seconds)
% 1.88/1.22  ----------------------
% 1.88/1.23  Preprocessing        : 0.30
% 1.88/1.23  Parsing              : 0.15
% 1.88/1.23  CNF conversion       : 0.02
% 1.88/1.23  Main loop            : 0.19
% 1.88/1.23  Inferencing          : 0.06
% 1.88/1.23  Reduction            : 0.07
% 1.88/1.23  Demodulation         : 0.05
% 1.88/1.23  BG Simplification    : 0.02
% 1.88/1.23  Subsumption          : 0.03
% 1.88/1.23  Abstraction          : 0.01
% 1.88/1.23  MUC search           : 0.00
% 1.88/1.23  Cooper               : 0.00
% 1.88/1.23  Total                : 0.52
% 1.88/1.23  Index Insertion      : 0.00
% 1.88/1.23  Index Deletion       : 0.00
% 1.88/1.23  Index Matching       : 0.00
% 1.88/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
