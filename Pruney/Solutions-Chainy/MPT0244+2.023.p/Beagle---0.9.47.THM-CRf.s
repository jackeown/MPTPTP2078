%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:59 EST 2020

% Result     : Theorem 1.96s
% Output     : CNFRefutation 2.06s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 173 expanded)
%              Number of leaves         :   15 (  58 expanded)
%              Depth                    :    7
%              Number of atoms          :   73 ( 318 expanded)
%              Number of equality atoms :   38 ( 206 expanded)
%              Maximal formula depth    :    6 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

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

tff(f_44,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(A,k1_tarski(B))
      <=> ( A = k1_xboole_0
          | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_zfmisc_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(c_18,plain,
    ( ~ r1_tarski('#skF_1',k1_tarski('#skF_2'))
    | k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_36,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_18])).

tff(c_14,plain,
    ( ~ r1_tarski('#skF_1',k1_tarski('#skF_2'))
    | k1_tarski('#skF_4') != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_37,plain,(
    k1_tarski('#skF_4') != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_14])).

tff(c_24,plain,
    ( k1_tarski('#skF_2') = '#skF_1'
    | k1_xboole_0 = '#skF_1'
    | r1_tarski('#skF_3',k1_tarski('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_68,plain,(
    r1_tarski('#skF_3',k1_tarski('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_24])).

tff(c_8,plain,(
    ! [B_8,A_7] :
      ( k1_tarski(B_8) = A_7
      | k1_xboole_0 = A_7
      | ~ r1_tarski(A_7,k1_tarski(B_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_71,plain,
    ( k1_tarski('#skF_4') = '#skF_3'
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_68,c_8])).

tff(c_75,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_37,c_71])).

tff(c_76,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_tarski('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_78,plain,(
    k1_tarski('#skF_2') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_76])).

tff(c_22,plain,
    ( ~ r1_tarski('#skF_1',k1_tarski('#skF_2'))
    | r1_tarski('#skF_3',k1_tarski('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_47,plain,(
    ~ r1_tarski('#skF_1',k1_tarski('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_22])).

tff(c_79,plain,(
    ~ r1_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_47])).

tff(c_10,plain,(
    ! [B_8] : r1_tarski(k1_tarski(B_8),k1_tarski(B_8)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_86,plain,(
    r1_tarski('#skF_1',k1_tarski('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_10])).

tff(c_95,plain,(
    r1_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_86])).

tff(c_98,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_79,c_95])).

tff(c_99,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_12,plain,(
    ! [B_8] : r1_tarski(k1_xboole_0,k1_tarski(B_8)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_103,plain,(
    ! [B_8] : r1_tarski('#skF_1',k1_tarski(B_8)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_12])).

tff(c_110,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_47])).

tff(c_111,plain,(
    r1_tarski('#skF_3',k1_tarski('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_22])).

tff(c_113,plain,(
    ! [B_19,A_20] :
      ( k1_tarski(B_19) = A_20
      | k1_xboole_0 = A_20
      | ~ r1_tarski(A_20,k1_tarski(B_19)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_119,plain,
    ( k1_tarski('#skF_4') = '#skF_3'
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_111,c_113])).

tff(c_130,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_37,c_119])).

tff(c_132,plain,(
    k1_tarski('#skF_4') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_14])).

tff(c_16,plain,
    ( k1_tarski('#skF_2') = '#skF_1'
    | k1_xboole_0 = '#skF_1'
    | k1_tarski('#skF_4') != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_207,plain,
    ( k1_tarski('#skF_2') = '#skF_1'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_16])).

tff(c_208,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_207])).

tff(c_210,plain,(
    ! [B_8] : r1_tarski('#skF_1',k1_tarski(B_8)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_208,c_12])).

tff(c_131,plain,(
    ~ r1_tarski('#skF_1',k1_tarski('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_14])).

tff(c_223,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_210,c_131])).

tff(c_224,plain,(
    k1_tarski('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_207])).

tff(c_232,plain,(
    r1_tarski(k1_tarski('#skF_2'),'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_224,c_10])).

tff(c_238,plain,(
    r1_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_224,c_232])).

tff(c_247,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_238,c_224,c_131])).

tff(c_249,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_18])).

tff(c_20,plain,
    ( k1_tarski('#skF_2') = '#skF_1'
    | k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_256,plain,
    ( k1_tarski('#skF_2') = '#skF_1'
    | '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_249,c_249,c_20])).

tff(c_257,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_256])).

tff(c_250,plain,(
    ! [B_8] : r1_tarski('#skF_3',k1_tarski(B_8)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_249,c_12])).

tff(c_267,plain,(
    ! [B_8] : r1_tarski('#skF_1',k1_tarski(B_8)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_257,c_250])).

tff(c_248,plain,(
    ~ r1_tarski('#skF_1',k1_tarski('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_18])).

tff(c_270,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_267,c_248])).

tff(c_271,plain,(
    k1_tarski('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_256])).

tff(c_276,plain,(
    r1_tarski('#skF_1',k1_tarski('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_271,c_10])).

tff(c_282,plain,(
    r1_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_271,c_276])).

tff(c_292,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_282,c_271,c_248])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:55:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.96/1.21  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.96/1.22  
% 1.96/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.96/1.22  %$ r1_tarski > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.96/1.22  
% 1.96/1.22  %Foreground sorts:
% 1.96/1.22  
% 1.96/1.22  
% 1.96/1.22  %Background operators:
% 1.96/1.22  
% 1.96/1.22  
% 1.96/1.22  %Foreground operators:
% 1.96/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.96/1.22  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.96/1.22  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.96/1.22  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.96/1.22  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.96/1.22  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.96/1.22  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.96/1.22  tff('#skF_2', type, '#skF_2': $i).
% 1.96/1.22  tff('#skF_3', type, '#skF_3': $i).
% 1.96/1.22  tff('#skF_1', type, '#skF_1': $i).
% 1.96/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.96/1.22  tff('#skF_4', type, '#skF_4': $i).
% 1.96/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.96/1.22  
% 2.06/1.23  tff(f_44, negated_conjecture, ~(![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_zfmisc_1)).
% 2.06/1.23  tff(f_37, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 2.06/1.23  tff(c_18, plain, (~r1_tarski('#skF_1', k1_tarski('#skF_2')) | k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.06/1.23  tff(c_36, plain, (k1_xboole_0!='#skF_3'), inference(splitLeft, [status(thm)], [c_18])).
% 2.06/1.23  tff(c_14, plain, (~r1_tarski('#skF_1', k1_tarski('#skF_2')) | k1_tarski('#skF_4')!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.06/1.23  tff(c_37, plain, (k1_tarski('#skF_4')!='#skF_3'), inference(splitLeft, [status(thm)], [c_14])).
% 2.06/1.23  tff(c_24, plain, (k1_tarski('#skF_2')='#skF_1' | k1_xboole_0='#skF_1' | r1_tarski('#skF_3', k1_tarski('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.06/1.23  tff(c_68, plain, (r1_tarski('#skF_3', k1_tarski('#skF_4'))), inference(splitLeft, [status(thm)], [c_24])).
% 2.06/1.23  tff(c_8, plain, (![B_8, A_7]: (k1_tarski(B_8)=A_7 | k1_xboole_0=A_7 | ~r1_tarski(A_7, k1_tarski(B_8)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.06/1.23  tff(c_71, plain, (k1_tarski('#skF_4')='#skF_3' | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_68, c_8])).
% 2.06/1.23  tff(c_75, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_37, c_71])).
% 2.06/1.23  tff(c_76, plain, (k1_xboole_0='#skF_1' | k1_tarski('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_24])).
% 2.06/1.23  tff(c_78, plain, (k1_tarski('#skF_2')='#skF_1'), inference(splitLeft, [status(thm)], [c_76])).
% 2.06/1.23  tff(c_22, plain, (~r1_tarski('#skF_1', k1_tarski('#skF_2')) | r1_tarski('#skF_3', k1_tarski('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.06/1.23  tff(c_47, plain, (~r1_tarski('#skF_1', k1_tarski('#skF_2'))), inference(splitLeft, [status(thm)], [c_22])).
% 2.06/1.23  tff(c_79, plain, (~r1_tarski('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_47])).
% 2.06/1.23  tff(c_10, plain, (![B_8]: (r1_tarski(k1_tarski(B_8), k1_tarski(B_8)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.06/1.23  tff(c_86, plain, (r1_tarski('#skF_1', k1_tarski('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_78, c_10])).
% 2.06/1.23  tff(c_95, plain, (r1_tarski('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_86])).
% 2.06/1.23  tff(c_98, plain, $false, inference(negUnitSimplification, [status(thm)], [c_79, c_95])).
% 2.06/1.23  tff(c_99, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_76])).
% 2.06/1.23  tff(c_12, plain, (![B_8]: (r1_tarski(k1_xboole_0, k1_tarski(B_8)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.06/1.23  tff(c_103, plain, (![B_8]: (r1_tarski('#skF_1', k1_tarski(B_8)))), inference(demodulation, [status(thm), theory('equality')], [c_99, c_12])).
% 2.06/1.23  tff(c_110, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_103, c_47])).
% 2.06/1.23  tff(c_111, plain, (r1_tarski('#skF_3', k1_tarski('#skF_4'))), inference(splitRight, [status(thm)], [c_22])).
% 2.06/1.23  tff(c_113, plain, (![B_19, A_20]: (k1_tarski(B_19)=A_20 | k1_xboole_0=A_20 | ~r1_tarski(A_20, k1_tarski(B_19)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.06/1.23  tff(c_119, plain, (k1_tarski('#skF_4')='#skF_3' | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_111, c_113])).
% 2.06/1.23  tff(c_130, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_37, c_119])).
% 2.06/1.23  tff(c_132, plain, (k1_tarski('#skF_4')='#skF_3'), inference(splitRight, [status(thm)], [c_14])).
% 2.06/1.23  tff(c_16, plain, (k1_tarski('#skF_2')='#skF_1' | k1_xboole_0='#skF_1' | k1_tarski('#skF_4')!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.06/1.23  tff(c_207, plain, (k1_tarski('#skF_2')='#skF_1' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_132, c_16])).
% 2.06/1.23  tff(c_208, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_207])).
% 2.06/1.23  tff(c_210, plain, (![B_8]: (r1_tarski('#skF_1', k1_tarski(B_8)))), inference(demodulation, [status(thm), theory('equality')], [c_208, c_12])).
% 2.06/1.24  tff(c_131, plain, (~r1_tarski('#skF_1', k1_tarski('#skF_2'))), inference(splitRight, [status(thm)], [c_14])).
% 2.06/1.24  tff(c_223, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_210, c_131])).
% 2.06/1.24  tff(c_224, plain, (k1_tarski('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_207])).
% 2.06/1.24  tff(c_232, plain, (r1_tarski(k1_tarski('#skF_2'), '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_224, c_10])).
% 2.06/1.24  tff(c_238, plain, (r1_tarski('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_224, c_232])).
% 2.06/1.24  tff(c_247, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_238, c_224, c_131])).
% 2.06/1.24  tff(c_249, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_18])).
% 2.06/1.24  tff(c_20, plain, (k1_tarski('#skF_2')='#skF_1' | k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.06/1.24  tff(c_256, plain, (k1_tarski('#skF_2')='#skF_1' | '#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_249, c_249, c_20])).
% 2.06/1.24  tff(c_257, plain, ('#skF_3'='#skF_1'), inference(splitLeft, [status(thm)], [c_256])).
% 2.06/1.24  tff(c_250, plain, (![B_8]: (r1_tarski('#skF_3', k1_tarski(B_8)))), inference(demodulation, [status(thm), theory('equality')], [c_249, c_12])).
% 2.06/1.24  tff(c_267, plain, (![B_8]: (r1_tarski('#skF_1', k1_tarski(B_8)))), inference(demodulation, [status(thm), theory('equality')], [c_257, c_250])).
% 2.06/1.24  tff(c_248, plain, (~r1_tarski('#skF_1', k1_tarski('#skF_2'))), inference(splitRight, [status(thm)], [c_18])).
% 2.06/1.24  tff(c_270, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_267, c_248])).
% 2.06/1.24  tff(c_271, plain, (k1_tarski('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_256])).
% 2.06/1.24  tff(c_276, plain, (r1_tarski('#skF_1', k1_tarski('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_271, c_10])).
% 2.06/1.24  tff(c_282, plain, (r1_tarski('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_271, c_276])).
% 2.06/1.24  tff(c_292, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_282, c_271, c_248])).
% 2.06/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.06/1.24  
% 2.06/1.24  Inference rules
% 2.06/1.24  ----------------------
% 2.06/1.24  #Ref     : 0
% 2.06/1.24  #Sup     : 59
% 2.06/1.24  #Fact    : 0
% 2.06/1.24  #Define  : 0
% 2.06/1.24  #Split   : 9
% 2.06/1.24  #Chain   : 0
% 2.06/1.24  #Close   : 0
% 2.06/1.24  
% 2.06/1.24  Ordering : KBO
% 2.06/1.24  
% 2.06/1.24  Simplification rules
% 2.06/1.24  ----------------------
% 2.06/1.24  #Subsume      : 4
% 2.06/1.24  #Demod        : 58
% 2.06/1.24  #Tautology    : 45
% 2.06/1.24  #SimpNegUnit  : 5
% 2.06/1.24  #BackRed      : 15
% 2.06/1.24  
% 2.06/1.24  #Partial instantiations: 0
% 2.06/1.24  #Strategies tried      : 1
% 2.06/1.24  
% 2.06/1.24  Timing (in seconds)
% 2.06/1.24  ----------------------
% 2.06/1.24  Preprocessing        : 0.28
% 2.06/1.24  Parsing              : 0.14
% 2.06/1.24  CNF conversion       : 0.02
% 2.06/1.24  Main loop            : 0.19
% 2.06/1.24  Inferencing          : 0.06
% 2.06/1.24  Reduction            : 0.06
% 2.06/1.24  Demodulation         : 0.04
% 2.06/1.24  BG Simplification    : 0.02
% 2.06/1.24  Subsumption          : 0.03
% 2.06/1.24  Abstraction          : 0.01
% 2.06/1.24  MUC search           : 0.00
% 2.06/1.24  Cooper               : 0.00
% 2.06/1.24  Total                : 0.50
% 2.06/1.24  Index Insertion      : 0.00
% 2.06/1.24  Index Deletion       : 0.00
% 2.06/1.24  Index Matching       : 0.00
% 2.06/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
