%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:59 EST 2020

% Result     : Theorem 2.16s
% Output     : CNFRefutation 2.16s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 141 expanded)
%              Number of leaves         :   22 (  54 expanded)
%              Depth                    :    6
%              Number of atoms          :   73 ( 227 expanded)
%              Number of equality atoms :   40 ( 136 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k4_enumset1 > k3_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,k2_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_56,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(A,k1_tarski(B))
      <=> ( A = k1_xboole_0
          | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_zfmisc_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(c_40,plain,(
    ! [A_32,B_33] : k3_xboole_0(A_32,k2_xboole_0(A_32,B_33)) = A_32 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k3_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_46,plain,(
    ! [A_32] : r1_tarski(A_32,A_32) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_2])).

tff(c_30,plain,
    ( ~ r1_tarski('#skF_1',k1_tarski('#skF_2'))
    | k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_54,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_26,plain,
    ( ~ r1_tarski('#skF_1',k1_tarski('#skF_2'))
    | k1_tarski('#skF_4') != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_64,plain,(
    k1_tarski('#skF_4') != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_26])).

tff(c_36,plain,
    ( k1_tarski('#skF_2') = '#skF_1'
    | k1_xboole_0 = '#skF_1'
    | r1_tarski('#skF_3',k1_tarski('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_117,plain,(
    r1_tarski('#skF_3',k1_tarski('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_18,plain,(
    ! [B_25,A_24] :
      ( k1_tarski(B_25) = A_24
      | k1_xboole_0 = A_24
      | ~ r1_tarski(A_24,k1_tarski(B_25)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_120,plain,
    ( k1_tarski('#skF_4') = '#skF_3'
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_117,c_18])).

tff(c_124,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_64,c_120])).

tff(c_125,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_tarski('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_127,plain,(
    k1_tarski('#skF_2') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_125])).

tff(c_34,plain,
    ( ~ r1_tarski('#skF_1',k1_tarski('#skF_2'))
    | r1_tarski('#skF_3',k1_tarski('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_74,plain,(
    ~ r1_tarski('#skF_1',k1_tarski('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_128,plain,(
    ~ r1_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_74])).

tff(c_131,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_128])).

tff(c_132,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_125])).

tff(c_22,plain,(
    ! [B_25] : r1_tarski(k1_xboole_0,k1_tarski(B_25)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_136,plain,(
    ! [B_25] : r1_tarski('#skF_1',k1_tarski(B_25)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_22])).

tff(c_143,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_74])).

tff(c_144,plain,(
    r1_tarski('#skF_3',k1_tarski('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_172,plain,(
    ! [B_48,A_49] :
      ( k1_tarski(B_48) = A_49
      | k1_xboole_0 = A_49
      | ~ r1_tarski(A_49,k1_tarski(B_48)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_178,plain,
    ( k1_tarski('#skF_4') = '#skF_3'
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_144,c_172])).

tff(c_194,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_64,c_178])).

tff(c_196,plain,(
    k1_tarski('#skF_4') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_28,plain,
    ( k1_tarski('#skF_2') = '#skF_1'
    | k1_xboole_0 = '#skF_1'
    | k1_tarski('#skF_4') != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_213,plain,
    ( k1_tarski('#skF_2') = '#skF_1'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_196,c_28])).

tff(c_214,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_213])).

tff(c_217,plain,(
    ! [B_25] : r1_tarski('#skF_1',k1_tarski(B_25)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_214,c_22])).

tff(c_195,plain,(
    ~ r1_tarski('#skF_1',k1_tarski('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_224,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_217,c_195])).

tff(c_225,plain,(
    k1_tarski('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_213])).

tff(c_227,plain,(
    ~ r1_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_225,c_195])).

tff(c_230,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_227])).

tff(c_232,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_32,plain,
    ( k1_tarski('#skF_2') = '#skF_1'
    | k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_249,plain,
    ( k1_tarski('#skF_2') = '#skF_1'
    | '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_232,c_232,c_32])).

tff(c_250,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_249])).

tff(c_233,plain,(
    ! [B_25] : r1_tarski('#skF_3',k1_tarski(B_25)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_232,c_22])).

tff(c_251,plain,(
    ! [B_25] : r1_tarski('#skF_1',k1_tarski(B_25)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_250,c_233])).

tff(c_231,plain,(
    ~ r1_tarski('#skF_1',k1_tarski('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_263,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_251,c_231])).

tff(c_264,plain,(
    k1_tarski('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_249])).

tff(c_266,plain,(
    ~ r1_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_264,c_231])).

tff(c_269,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_266])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:13:56 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.16/1.31  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.16/1.31  
% 2.16/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.16/1.32  %$ r1_tarski > k4_enumset1 > k3_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.16/1.32  
% 2.16/1.32  %Foreground sorts:
% 2.16/1.32  
% 2.16/1.32  
% 2.16/1.32  %Background operators:
% 2.16/1.32  
% 2.16/1.32  
% 2.16/1.32  %Foreground operators:
% 2.16/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.16/1.32  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.16/1.32  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.16/1.32  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.16/1.32  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.16/1.32  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.16/1.32  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.16/1.32  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.16/1.32  tff('#skF_2', type, '#skF_2': $i).
% 2.16/1.32  tff('#skF_3', type, '#skF_3': $i).
% 2.16/1.32  tff('#skF_1', type, '#skF_1': $i).
% 2.16/1.32  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.16/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.16/1.32  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.16/1.32  tff('#skF_4', type, '#skF_4': $i).
% 2.16/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.16/1.32  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.16/1.32  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.16/1.32  
% 2.16/1.33  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, k2_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_xboole_1)).
% 2.16/1.33  tff(f_27, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 2.16/1.33  tff(f_56, negated_conjecture, ~(![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_zfmisc_1)).
% 2.16/1.33  tff(f_47, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 2.16/1.33  tff(c_40, plain, (![A_32, B_33]: (k3_xboole_0(A_32, k2_xboole_0(A_32, B_33))=A_32)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.16/1.33  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k3_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.16/1.33  tff(c_46, plain, (![A_32]: (r1_tarski(A_32, A_32))), inference(superposition, [status(thm), theory('equality')], [c_40, c_2])).
% 2.16/1.33  tff(c_30, plain, (~r1_tarski('#skF_1', k1_tarski('#skF_2')) | k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.16/1.33  tff(c_54, plain, (k1_xboole_0!='#skF_3'), inference(splitLeft, [status(thm)], [c_30])).
% 2.16/1.33  tff(c_26, plain, (~r1_tarski('#skF_1', k1_tarski('#skF_2')) | k1_tarski('#skF_4')!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.16/1.33  tff(c_64, plain, (k1_tarski('#skF_4')!='#skF_3'), inference(splitLeft, [status(thm)], [c_26])).
% 2.16/1.33  tff(c_36, plain, (k1_tarski('#skF_2')='#skF_1' | k1_xboole_0='#skF_1' | r1_tarski('#skF_3', k1_tarski('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.16/1.33  tff(c_117, plain, (r1_tarski('#skF_3', k1_tarski('#skF_4'))), inference(splitLeft, [status(thm)], [c_36])).
% 2.16/1.33  tff(c_18, plain, (![B_25, A_24]: (k1_tarski(B_25)=A_24 | k1_xboole_0=A_24 | ~r1_tarski(A_24, k1_tarski(B_25)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.16/1.33  tff(c_120, plain, (k1_tarski('#skF_4')='#skF_3' | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_117, c_18])).
% 2.16/1.33  tff(c_124, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_64, c_120])).
% 2.16/1.33  tff(c_125, plain, (k1_xboole_0='#skF_1' | k1_tarski('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_36])).
% 2.16/1.33  tff(c_127, plain, (k1_tarski('#skF_2')='#skF_1'), inference(splitLeft, [status(thm)], [c_125])).
% 2.16/1.33  tff(c_34, plain, (~r1_tarski('#skF_1', k1_tarski('#skF_2')) | r1_tarski('#skF_3', k1_tarski('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.16/1.33  tff(c_74, plain, (~r1_tarski('#skF_1', k1_tarski('#skF_2'))), inference(splitLeft, [status(thm)], [c_34])).
% 2.16/1.33  tff(c_128, plain, (~r1_tarski('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_127, c_74])).
% 2.16/1.33  tff(c_131, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_128])).
% 2.16/1.33  tff(c_132, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_125])).
% 2.16/1.33  tff(c_22, plain, (![B_25]: (r1_tarski(k1_xboole_0, k1_tarski(B_25)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.16/1.33  tff(c_136, plain, (![B_25]: (r1_tarski('#skF_1', k1_tarski(B_25)))), inference(demodulation, [status(thm), theory('equality')], [c_132, c_22])).
% 2.16/1.33  tff(c_143, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_136, c_74])).
% 2.16/1.33  tff(c_144, plain, (r1_tarski('#skF_3', k1_tarski('#skF_4'))), inference(splitRight, [status(thm)], [c_34])).
% 2.16/1.33  tff(c_172, plain, (![B_48, A_49]: (k1_tarski(B_48)=A_49 | k1_xboole_0=A_49 | ~r1_tarski(A_49, k1_tarski(B_48)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.16/1.33  tff(c_178, plain, (k1_tarski('#skF_4')='#skF_3' | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_144, c_172])).
% 2.16/1.33  tff(c_194, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_64, c_178])).
% 2.16/1.33  tff(c_196, plain, (k1_tarski('#skF_4')='#skF_3'), inference(splitRight, [status(thm)], [c_26])).
% 2.16/1.33  tff(c_28, plain, (k1_tarski('#skF_2')='#skF_1' | k1_xboole_0='#skF_1' | k1_tarski('#skF_4')!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.16/1.33  tff(c_213, plain, (k1_tarski('#skF_2')='#skF_1' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_196, c_28])).
% 2.16/1.33  tff(c_214, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_213])).
% 2.16/1.33  tff(c_217, plain, (![B_25]: (r1_tarski('#skF_1', k1_tarski(B_25)))), inference(demodulation, [status(thm), theory('equality')], [c_214, c_22])).
% 2.16/1.33  tff(c_195, plain, (~r1_tarski('#skF_1', k1_tarski('#skF_2'))), inference(splitRight, [status(thm)], [c_26])).
% 2.16/1.33  tff(c_224, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_217, c_195])).
% 2.16/1.33  tff(c_225, plain, (k1_tarski('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_213])).
% 2.16/1.33  tff(c_227, plain, (~r1_tarski('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_225, c_195])).
% 2.16/1.33  tff(c_230, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_227])).
% 2.16/1.33  tff(c_232, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_30])).
% 2.16/1.33  tff(c_32, plain, (k1_tarski('#skF_2')='#skF_1' | k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.16/1.33  tff(c_249, plain, (k1_tarski('#skF_2')='#skF_1' | '#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_232, c_232, c_32])).
% 2.16/1.33  tff(c_250, plain, ('#skF_3'='#skF_1'), inference(splitLeft, [status(thm)], [c_249])).
% 2.16/1.33  tff(c_233, plain, (![B_25]: (r1_tarski('#skF_3', k1_tarski(B_25)))), inference(demodulation, [status(thm), theory('equality')], [c_232, c_22])).
% 2.16/1.33  tff(c_251, plain, (![B_25]: (r1_tarski('#skF_1', k1_tarski(B_25)))), inference(demodulation, [status(thm), theory('equality')], [c_250, c_233])).
% 2.16/1.33  tff(c_231, plain, (~r1_tarski('#skF_1', k1_tarski('#skF_2'))), inference(splitRight, [status(thm)], [c_30])).
% 2.16/1.33  tff(c_263, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_251, c_231])).
% 2.16/1.33  tff(c_264, plain, (k1_tarski('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_249])).
% 2.16/1.33  tff(c_266, plain, (~r1_tarski('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_264, c_231])).
% 2.16/1.33  tff(c_269, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_266])).
% 2.16/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.16/1.33  
% 2.16/1.33  Inference rules
% 2.16/1.33  ----------------------
% 2.16/1.33  #Ref     : 0
% 2.16/1.33  #Sup     : 45
% 2.16/1.33  #Fact    : 0
% 2.16/1.33  #Define  : 0
% 2.16/1.33  #Split   : 7
% 2.16/1.33  #Chain   : 0
% 2.16/1.33  #Close   : 0
% 2.16/1.33  
% 2.16/1.33  Ordering : KBO
% 2.16/1.33  
% 2.16/1.33  Simplification rules
% 2.16/1.33  ----------------------
% 2.16/1.33  #Subsume      : 5
% 2.16/1.33  #Demod        : 25
% 2.16/1.33  #Tautology    : 36
% 2.16/1.33  #SimpNegUnit  : 2
% 2.16/1.33  #BackRed      : 15
% 2.16/1.33  
% 2.16/1.33  #Partial instantiations: 0
% 2.16/1.33  #Strategies tried      : 1
% 2.16/1.33  
% 2.16/1.33  Timing (in seconds)
% 2.16/1.33  ----------------------
% 2.16/1.33  Preprocessing        : 0.34
% 2.16/1.33  Parsing              : 0.19
% 2.16/1.33  CNF conversion       : 0.02
% 2.16/1.33  Main loop            : 0.16
% 2.16/1.33  Inferencing          : 0.05
% 2.16/1.33  Reduction            : 0.05
% 2.16/1.33  Demodulation         : 0.04
% 2.16/1.33  BG Simplification    : 0.01
% 2.16/1.33  Subsumption          : 0.03
% 2.16/1.33  Abstraction          : 0.01
% 2.16/1.33  MUC search           : 0.00
% 2.16/1.33  Cooper               : 0.00
% 2.16/1.33  Total                : 0.54
% 2.16/1.33  Index Insertion      : 0.00
% 2.16/1.33  Index Deletion       : 0.00
% 2.16/1.33  Index Matching       : 0.00
% 2.16/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
