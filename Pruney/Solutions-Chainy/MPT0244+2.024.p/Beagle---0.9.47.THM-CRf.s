%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:59 EST 2020

% Result     : Theorem 2.52s
% Output     : CNFRefutation 2.71s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 216 expanded)
%              Number of leaves         :   16 (  72 expanded)
%              Depth                    :    7
%              Number of atoms          :  105 ( 409 expanded)
%              Number of equality atoms :   63 ( 278 expanded)
%              Maximal formula depth    :   10 (   3 average)
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

tff(f_53,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(A,k1_tarski(B))
      <=> ( A = k1_xboole_0
          | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_zfmisc_1)).

tff(f_27,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_tarski(B,C))
    <=> ~ ( A != k1_xboole_0
          & A != k1_tarski(B)
          & A != k1_tarski(C)
          & A != k2_tarski(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l45_zfmisc_1)).

tff(c_22,plain,
    ( ~ r1_tarski('#skF_1',k1_tarski('#skF_2'))
    | k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_52,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_22])).

tff(c_18,plain,
    ( ~ r1_tarski('#skF_1',k1_tarski('#skF_2'))
    | k1_tarski('#skF_4') != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_53,plain,(
    k1_tarski('#skF_4') != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_18])).

tff(c_28,plain,
    ( k1_tarski('#skF_2') = '#skF_1'
    | k1_xboole_0 = '#skF_1'
    | r1_tarski('#skF_3',k1_tarski('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_82,plain,(
    r1_tarski('#skF_3',k1_tarski('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_2,plain,(
    ! [A_1] : k2_tarski(A_1,A_1) = k1_tarski(A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_83,plain,(
    ! [B_26,C_27,A_28] :
      ( k2_tarski(B_26,C_27) = A_28
      | k1_tarski(C_27) = A_28
      | k1_tarski(B_26) = A_28
      | k1_xboole_0 = A_28
      | ~ r1_tarski(A_28,k2_tarski(B_26,C_27)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_95,plain,(
    ! [A_1,A_28] :
      ( k2_tarski(A_1,A_1) = A_28
      | k1_tarski(A_1) = A_28
      | k1_tarski(A_1) = A_28
      | k1_xboole_0 = A_28
      | ~ r1_tarski(A_28,k1_tarski(A_1)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_83])).

tff(c_108,plain,(
    ! [A_29,A_30] :
      ( k1_tarski(A_29) = A_30
      | k1_tarski(A_29) = A_30
      | k1_tarski(A_29) = A_30
      | k1_xboole_0 = A_30
      | ~ r1_tarski(A_30,k1_tarski(A_29)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_95])).

tff(c_111,plain,
    ( k1_tarski('#skF_4') = '#skF_3'
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_82,c_108])).

tff(c_121,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_53,c_53,c_53,c_111])).

tff(c_122,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_tarski('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_124,plain,(
    k1_tarski('#skF_2') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_122])).

tff(c_26,plain,
    ( ~ r1_tarski('#skF_1',k1_tarski('#skF_2'))
    | r1_tarski('#skF_3',k1_tarski('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_72,plain,(
    ~ r1_tarski('#skF_1',k1_tarski('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_26])).

tff(c_125,plain,(
    ~ r1_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_72])).

tff(c_42,plain,(
    ! [C_14,B_15] : r1_tarski(k1_tarski(C_14),k2_tarski(B_15,C_14)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_45,plain,(
    ! [A_1] : r1_tarski(k1_tarski(A_1),k1_tarski(A_1)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_42])).

tff(c_132,plain,(
    r1_tarski('#skF_1',k1_tarski('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_124,c_45])).

tff(c_143,plain,(
    r1_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_132])).

tff(c_171,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_125,c_143])).

tff(c_172,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_122])).

tff(c_30,plain,(
    ! [A_12] : k2_tarski(A_12,A_12) = k1_tarski(A_12) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_16,plain,(
    ! [B_8,C_9] : r1_tarski(k1_xboole_0,k2_tarski(B_8,C_9)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_35,plain,(
    ! [A_12] : r1_tarski(k1_xboole_0,k1_tarski(A_12)) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_16])).

tff(c_175,plain,(
    ! [A_12] : r1_tarski('#skF_1',k1_tarski(A_12)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_172,c_35])).

tff(c_183,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_175,c_72])).

tff(c_184,plain,(
    r1_tarski('#skF_3',k1_tarski('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_196,plain,(
    ! [B_37,C_38,A_39] :
      ( k2_tarski(B_37,C_38) = A_39
      | k1_tarski(C_38) = A_39
      | k1_tarski(B_37) = A_39
      | k1_xboole_0 = A_39
      | ~ r1_tarski(A_39,k2_tarski(B_37,C_38)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_208,plain,(
    ! [A_1,A_39] :
      ( k2_tarski(A_1,A_1) = A_39
      | k1_tarski(A_1) = A_39
      | k1_tarski(A_1) = A_39
      | k1_xboole_0 = A_39
      | ~ r1_tarski(A_39,k1_tarski(A_1)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_196])).

tff(c_221,plain,(
    ! [A_40,A_41] :
      ( k1_tarski(A_40) = A_41
      | k1_tarski(A_40) = A_41
      | k1_tarski(A_40) = A_41
      | k1_xboole_0 = A_41
      | ~ r1_tarski(A_41,k1_tarski(A_40)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_208])).

tff(c_227,plain,
    ( k1_tarski('#skF_4') = '#skF_3'
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_184,c_221])).

tff(c_238,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_53,c_53,c_53,c_227])).

tff(c_240,plain,(
    k1_tarski('#skF_4') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_18])).

tff(c_20,plain,
    ( k1_tarski('#skF_2') = '#skF_1'
    | k1_xboole_0 = '#skF_1'
    | k1_tarski('#skF_4') != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_262,plain,
    ( k1_tarski('#skF_2') = '#skF_1'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_240,c_20])).

tff(c_263,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_262])).

tff(c_265,plain,(
    ! [A_12] : r1_tarski('#skF_1',k1_tarski(A_12)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_263,c_35])).

tff(c_239,plain,(
    ~ r1_tarski('#skF_1',k1_tarski('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_18])).

tff(c_278,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_265,c_239])).

tff(c_279,plain,(
    k1_tarski('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_262])).

tff(c_290,plain,(
    r1_tarski(k1_tarski('#skF_2'),'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_279,c_45])).

tff(c_299,plain,(
    r1_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_279,c_290])).

tff(c_305,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_299,c_279,c_239])).

tff(c_307,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_22])).

tff(c_24,plain,
    ( k1_tarski('#skF_2') = '#skF_1'
    | k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_316,plain,
    ( k1_tarski('#skF_2') = '#skF_1'
    | '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_307,c_307,c_24])).

tff(c_317,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_316])).

tff(c_308,plain,(
    ! [A_12] : r1_tarski('#skF_3',k1_tarski(A_12)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_307,c_35])).

tff(c_318,plain,(
    ! [A_12] : r1_tarski('#skF_1',k1_tarski(A_12)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_317,c_308])).

tff(c_306,plain,(
    ~ r1_tarski('#skF_1',k1_tarski('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_22])).

tff(c_330,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_318,c_306])).

tff(c_331,plain,(
    k1_tarski('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_316])).

tff(c_333,plain,(
    ~ r1_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_331,c_306])).

tff(c_345,plain,(
    r1_tarski(k1_tarski('#skF_2'),'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_331,c_45])).

tff(c_352,plain,(
    r1_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_331,c_345])).

tff(c_354,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_333,c_352])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:21:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.52/1.66  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.52/1.67  
% 2.52/1.67  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.52/1.68  %$ r1_tarski > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.52/1.68  
% 2.52/1.68  %Foreground sorts:
% 2.52/1.68  
% 2.52/1.68  
% 2.52/1.68  %Background operators:
% 2.52/1.68  
% 2.52/1.68  
% 2.52/1.68  %Foreground operators:
% 2.52/1.68  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.52/1.68  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.52/1.68  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.52/1.68  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.52/1.68  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.52/1.68  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.52/1.68  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.52/1.68  tff('#skF_2', type, '#skF_2': $i).
% 2.52/1.68  tff('#skF_3', type, '#skF_3': $i).
% 2.52/1.68  tff('#skF_1', type, '#skF_1': $i).
% 2.52/1.68  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.52/1.68  tff('#skF_4', type, '#skF_4': $i).
% 2.52/1.68  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.52/1.68  
% 2.71/1.70  tff(f_53, negated_conjecture, ~(![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_zfmisc_1)).
% 2.71/1.70  tff(f_27, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.71/1.70  tff(f_46, axiom, (![A, B, C]: (r1_tarski(A, k2_tarski(B, C)) <=> ~(((~(A = k1_xboole_0) & ~(A = k1_tarski(B))) & ~(A = k1_tarski(C))) & ~(A = k2_tarski(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l45_zfmisc_1)).
% 2.71/1.70  tff(c_22, plain, (~r1_tarski('#skF_1', k1_tarski('#skF_2')) | k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.71/1.70  tff(c_52, plain, (k1_xboole_0!='#skF_3'), inference(splitLeft, [status(thm)], [c_22])).
% 2.71/1.70  tff(c_18, plain, (~r1_tarski('#skF_1', k1_tarski('#skF_2')) | k1_tarski('#skF_4')!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.71/1.70  tff(c_53, plain, (k1_tarski('#skF_4')!='#skF_3'), inference(splitLeft, [status(thm)], [c_18])).
% 2.71/1.70  tff(c_28, plain, (k1_tarski('#skF_2')='#skF_1' | k1_xboole_0='#skF_1' | r1_tarski('#skF_3', k1_tarski('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.71/1.70  tff(c_82, plain, (r1_tarski('#skF_3', k1_tarski('#skF_4'))), inference(splitLeft, [status(thm)], [c_28])).
% 2.71/1.70  tff(c_2, plain, (![A_1]: (k2_tarski(A_1, A_1)=k1_tarski(A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.71/1.70  tff(c_83, plain, (![B_26, C_27, A_28]: (k2_tarski(B_26, C_27)=A_28 | k1_tarski(C_27)=A_28 | k1_tarski(B_26)=A_28 | k1_xboole_0=A_28 | ~r1_tarski(A_28, k2_tarski(B_26, C_27)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.71/1.70  tff(c_95, plain, (![A_1, A_28]: (k2_tarski(A_1, A_1)=A_28 | k1_tarski(A_1)=A_28 | k1_tarski(A_1)=A_28 | k1_xboole_0=A_28 | ~r1_tarski(A_28, k1_tarski(A_1)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_83])).
% 2.71/1.70  tff(c_108, plain, (![A_29, A_30]: (k1_tarski(A_29)=A_30 | k1_tarski(A_29)=A_30 | k1_tarski(A_29)=A_30 | k1_xboole_0=A_30 | ~r1_tarski(A_30, k1_tarski(A_29)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_95])).
% 2.71/1.70  tff(c_111, plain, (k1_tarski('#skF_4')='#skF_3' | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_82, c_108])).
% 2.71/1.70  tff(c_121, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_53, c_53, c_53, c_111])).
% 2.71/1.70  tff(c_122, plain, (k1_xboole_0='#skF_1' | k1_tarski('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_28])).
% 2.71/1.70  tff(c_124, plain, (k1_tarski('#skF_2')='#skF_1'), inference(splitLeft, [status(thm)], [c_122])).
% 2.71/1.70  tff(c_26, plain, (~r1_tarski('#skF_1', k1_tarski('#skF_2')) | r1_tarski('#skF_3', k1_tarski('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.71/1.70  tff(c_72, plain, (~r1_tarski('#skF_1', k1_tarski('#skF_2'))), inference(splitLeft, [status(thm)], [c_26])).
% 2.71/1.70  tff(c_125, plain, (~r1_tarski('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_124, c_72])).
% 2.71/1.70  tff(c_42, plain, (![C_14, B_15]: (r1_tarski(k1_tarski(C_14), k2_tarski(B_15, C_14)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.71/1.70  tff(c_45, plain, (![A_1]: (r1_tarski(k1_tarski(A_1), k1_tarski(A_1)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_42])).
% 2.71/1.70  tff(c_132, plain, (r1_tarski('#skF_1', k1_tarski('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_124, c_45])).
% 2.71/1.70  tff(c_143, plain, (r1_tarski('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_124, c_132])).
% 2.71/1.70  tff(c_171, plain, $false, inference(negUnitSimplification, [status(thm)], [c_125, c_143])).
% 2.71/1.70  tff(c_172, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_122])).
% 2.71/1.70  tff(c_30, plain, (![A_12]: (k2_tarski(A_12, A_12)=k1_tarski(A_12))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.71/1.70  tff(c_16, plain, (![B_8, C_9]: (r1_tarski(k1_xboole_0, k2_tarski(B_8, C_9)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.71/1.70  tff(c_35, plain, (![A_12]: (r1_tarski(k1_xboole_0, k1_tarski(A_12)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_16])).
% 2.71/1.70  tff(c_175, plain, (![A_12]: (r1_tarski('#skF_1', k1_tarski(A_12)))), inference(demodulation, [status(thm), theory('equality')], [c_172, c_35])).
% 2.71/1.70  tff(c_183, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_175, c_72])).
% 2.71/1.70  tff(c_184, plain, (r1_tarski('#skF_3', k1_tarski('#skF_4'))), inference(splitRight, [status(thm)], [c_26])).
% 2.71/1.70  tff(c_196, plain, (![B_37, C_38, A_39]: (k2_tarski(B_37, C_38)=A_39 | k1_tarski(C_38)=A_39 | k1_tarski(B_37)=A_39 | k1_xboole_0=A_39 | ~r1_tarski(A_39, k2_tarski(B_37, C_38)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.71/1.70  tff(c_208, plain, (![A_1, A_39]: (k2_tarski(A_1, A_1)=A_39 | k1_tarski(A_1)=A_39 | k1_tarski(A_1)=A_39 | k1_xboole_0=A_39 | ~r1_tarski(A_39, k1_tarski(A_1)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_196])).
% 2.71/1.70  tff(c_221, plain, (![A_40, A_41]: (k1_tarski(A_40)=A_41 | k1_tarski(A_40)=A_41 | k1_tarski(A_40)=A_41 | k1_xboole_0=A_41 | ~r1_tarski(A_41, k1_tarski(A_40)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_208])).
% 2.71/1.70  tff(c_227, plain, (k1_tarski('#skF_4')='#skF_3' | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_184, c_221])).
% 2.71/1.70  tff(c_238, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_53, c_53, c_53, c_227])).
% 2.71/1.70  tff(c_240, plain, (k1_tarski('#skF_4')='#skF_3'), inference(splitRight, [status(thm)], [c_18])).
% 2.71/1.70  tff(c_20, plain, (k1_tarski('#skF_2')='#skF_1' | k1_xboole_0='#skF_1' | k1_tarski('#skF_4')!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.71/1.70  tff(c_262, plain, (k1_tarski('#skF_2')='#skF_1' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_240, c_20])).
% 2.71/1.70  tff(c_263, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_262])).
% 2.71/1.70  tff(c_265, plain, (![A_12]: (r1_tarski('#skF_1', k1_tarski(A_12)))), inference(demodulation, [status(thm), theory('equality')], [c_263, c_35])).
% 2.71/1.70  tff(c_239, plain, (~r1_tarski('#skF_1', k1_tarski('#skF_2'))), inference(splitRight, [status(thm)], [c_18])).
% 2.71/1.70  tff(c_278, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_265, c_239])).
% 2.71/1.70  tff(c_279, plain, (k1_tarski('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_262])).
% 2.71/1.70  tff(c_290, plain, (r1_tarski(k1_tarski('#skF_2'), '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_279, c_45])).
% 2.71/1.70  tff(c_299, plain, (r1_tarski('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_279, c_290])).
% 2.71/1.70  tff(c_305, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_299, c_279, c_239])).
% 2.71/1.70  tff(c_307, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_22])).
% 2.71/1.70  tff(c_24, plain, (k1_tarski('#skF_2')='#skF_1' | k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.71/1.70  tff(c_316, plain, (k1_tarski('#skF_2')='#skF_1' | '#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_307, c_307, c_24])).
% 2.71/1.70  tff(c_317, plain, ('#skF_3'='#skF_1'), inference(splitLeft, [status(thm)], [c_316])).
% 2.71/1.70  tff(c_308, plain, (![A_12]: (r1_tarski('#skF_3', k1_tarski(A_12)))), inference(demodulation, [status(thm), theory('equality')], [c_307, c_35])).
% 2.71/1.70  tff(c_318, plain, (![A_12]: (r1_tarski('#skF_1', k1_tarski(A_12)))), inference(demodulation, [status(thm), theory('equality')], [c_317, c_308])).
% 2.71/1.70  tff(c_306, plain, (~r1_tarski('#skF_1', k1_tarski('#skF_2'))), inference(splitRight, [status(thm)], [c_22])).
% 2.71/1.70  tff(c_330, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_318, c_306])).
% 2.71/1.70  tff(c_331, plain, (k1_tarski('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_316])).
% 2.71/1.70  tff(c_333, plain, (~r1_tarski('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_331, c_306])).
% 2.71/1.70  tff(c_345, plain, (r1_tarski(k1_tarski('#skF_2'), '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_331, c_45])).
% 2.71/1.70  tff(c_352, plain, (r1_tarski('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_331, c_345])).
% 2.71/1.70  tff(c_354, plain, $false, inference(negUnitSimplification, [status(thm)], [c_333, c_352])).
% 2.71/1.70  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.71/1.70  
% 2.71/1.70  Inference rules
% 2.71/1.70  ----------------------
% 2.71/1.70  #Ref     : 0
% 2.71/1.70  #Sup     : 74
% 2.71/1.70  #Fact    : 0
% 2.71/1.70  #Define  : 0
% 2.71/1.70  #Split   : 7
% 2.71/1.70  #Chain   : 0
% 2.71/1.70  #Close   : 0
% 2.71/1.70  
% 2.71/1.70  Ordering : KBO
% 2.71/1.70  
% 2.71/1.70  Simplification rules
% 2.71/1.70  ----------------------
% 2.71/1.70  #Subsume      : 2
% 2.71/1.70  #Demod        : 44
% 2.71/1.70  #Tautology    : 46
% 2.71/1.70  #SimpNegUnit  : 4
% 2.71/1.70  #BackRed      : 15
% 2.71/1.70  
% 2.71/1.70  #Partial instantiations: 0
% 2.71/1.70  #Strategies tried      : 1
% 2.71/1.70  
% 2.71/1.70  Timing (in seconds)
% 2.71/1.70  ----------------------
% 2.71/1.71  Preprocessing        : 0.46
% 2.71/1.71  Parsing              : 0.23
% 2.71/1.71  CNF conversion       : 0.03
% 2.71/1.71  Main loop            : 0.34
% 2.71/1.71  Inferencing          : 0.12
% 2.71/1.71  Reduction            : 0.11
% 2.71/1.71  Demodulation         : 0.08
% 2.71/1.71  BG Simplification    : 0.03
% 2.71/1.71  Subsumption          : 0.06
% 2.71/1.71  Abstraction          : 0.02
% 2.71/1.71  MUC search           : 0.00
% 2.71/1.71  Cooper               : 0.00
% 2.71/1.71  Total                : 0.86
% 2.71/1.71  Index Insertion      : 0.00
% 2.71/1.71  Index Deletion       : 0.00
% 2.71/1.71  Index Matching       : 0.00
% 2.71/1.71  BG Taut test         : 0.00
%------------------------------------------------------------------------------
