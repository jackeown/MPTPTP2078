%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:19 EST 2020

% Result     : Theorem 2.36s
% Output     : CNFRefutation 2.36s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 103 expanded)
%              Number of leaves         :   20 (  42 expanded)
%              Depth                    :    9
%              Number of atoms          :   86 ( 237 expanded)
%              Number of equality atoms :   54 ( 192 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_74,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k1_tarski(A) = k2_xboole_0(B,C)
          & ~ ( B = k1_tarski(A)
              & C = k1_tarski(A) )
          & ~ ( B = k1_xboole_0
              & C = k1_tarski(A) )
          & ~ ( B = k1_tarski(A)
              & C = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

tff(c_30,plain,
    ( k1_tarski('#skF_1') != '#skF_3'
    | k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_57,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_28,plain,
    ( k1_xboole_0 != '#skF_3'
    | k1_tarski('#skF_1') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_39,plain,(
    k1_tarski('#skF_1') != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_34,plain,(
    k2_xboole_0('#skF_2','#skF_3') = k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_12,plain,(
    ! [A_8,B_9] : r1_tarski(A_8,k2_xboole_0(A_8,B_9)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_53,plain,(
    r1_tarski('#skF_2',k1_tarski('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_12])).

tff(c_236,plain,(
    ! [B_46,A_47] :
      ( k1_tarski(B_46) = A_47
      | k1_xboole_0 = A_47
      | ~ r1_tarski(A_47,k1_tarski(B_46)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_242,plain,
    ( k1_tarski('#skF_1') = '#skF_2'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_53,c_236])).

tff(c_254,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_57,c_39,c_242])).

tff(c_255,plain,(
    k1_tarski('#skF_1') != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_264,plain,(
    ! [A_49,B_50] :
      ( k2_xboole_0(A_49,B_50) = B_50
      | ~ r1_tarski(A_49,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_276,plain,(
    ! [B_2] : k2_xboole_0(B_2,B_2) = B_2 ),
    inference(resolution,[status(thm)],[c_6,c_264])).

tff(c_348,plain,(
    ! [A_61,C_62,B_63] :
      ( r1_tarski(A_61,k2_xboole_0(C_62,B_63))
      | ~ r1_tarski(A_61,B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_362,plain,(
    ! [A_61] :
      ( r1_tarski(A_61,k1_tarski('#skF_1'))
      | ~ r1_tarski(A_61,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_348])).

tff(c_256,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_20,plain,(
    ! [B_17,A_16] :
      ( k1_tarski(B_17) = A_16
      | k1_xboole_0 = A_16
      | ~ r1_tarski(A_16,k1_tarski(B_17)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_410,plain,(
    ! [B_67,A_68] :
      ( k1_tarski(B_67) = A_68
      | A_68 = '#skF_2'
      | ~ r1_tarski(A_68,k1_tarski(B_67)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_256,c_20])).

tff(c_426,plain,(
    ! [A_69] :
      ( k1_tarski('#skF_1') = A_69
      | A_69 = '#skF_2'
      | ~ r1_tarski(A_69,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_362,c_410])).

tff(c_430,plain,
    ( k1_tarski('#skF_1') = '#skF_3'
    | '#skF_2' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_6,c_426])).

tff(c_433,plain,(
    '#skF_2' = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_255,c_430])).

tff(c_440,plain,(
    k2_xboole_0('#skF_3','#skF_3') = k1_tarski('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_433,c_34])).

tff(c_442,plain,(
    k1_tarski('#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_276,c_440])).

tff(c_444,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_255,c_442])).

tff(c_445,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_446,plain,(
    k1_tarski('#skF_1') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_32,plain,
    ( k1_tarski('#skF_1') != '#skF_3'
    | k1_tarski('#skF_1') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_475,plain,(
    '#skF_2' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_446,c_446,c_32])).

tff(c_455,plain,(
    k2_xboole_0('#skF_2','#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_446,c_34])).

tff(c_552,plain,(
    ! [A_81,C_82,B_83] :
      ( r1_tarski(A_81,k2_xboole_0(C_82,B_83))
      | ~ r1_tarski(A_81,B_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_586,plain,(
    ! [A_85] :
      ( r1_tarski(A_85,'#skF_2')
      | ~ r1_tarski(A_85,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_455,c_552])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( k2_xboole_0(A_6,B_7) = B_7
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_591,plain,(
    ! [A_86] :
      ( k2_xboole_0(A_86,'#skF_2') = '#skF_2'
      | ~ r1_tarski(A_86,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_586,c_10])).

tff(c_596,plain,(
    k2_xboole_0('#skF_3','#skF_2') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_6,c_591])).

tff(c_603,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_596,c_12])).

tff(c_708,plain,(
    ! [B_93,A_94] :
      ( k1_tarski(B_93) = A_94
      | k1_xboole_0 = A_94
      | ~ r1_tarski(A_94,k1_tarski(B_93)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_711,plain,(
    ! [A_94] :
      ( k1_tarski('#skF_1') = A_94
      | k1_xboole_0 = A_94
      | ~ r1_tarski(A_94,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_446,c_708])).

tff(c_724,plain,(
    ! [A_95] :
      ( A_95 = '#skF_2'
      | k1_xboole_0 = A_95
      | ~ r1_tarski(A_95,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_446,c_711])).

tff(c_727,plain,
    ( '#skF_2' = '#skF_3'
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_603,c_724])).

tff(c_741,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_445,c_475,c_727])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:25:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.36/1.33  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.36/1.33  
% 2.36/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.36/1.33  %$ r1_tarski > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.36/1.33  
% 2.36/1.33  %Foreground sorts:
% 2.36/1.33  
% 2.36/1.33  
% 2.36/1.33  %Background operators:
% 2.36/1.33  
% 2.36/1.33  
% 2.36/1.33  %Foreground operators:
% 2.36/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.36/1.33  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.36/1.33  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.36/1.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.36/1.33  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.36/1.33  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.36/1.33  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.36/1.33  tff('#skF_2', type, '#skF_2': $i).
% 2.36/1.33  tff('#skF_3', type, '#skF_3': $i).
% 2.36/1.33  tff('#skF_1', type, '#skF_1': $i).
% 2.36/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.36/1.33  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.36/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.36/1.33  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.36/1.33  
% 2.36/1.35  tff(f_74, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~((B = k1_tarski(A)) & (C = k1_tarski(A)))) & ~((B = k1_xboole_0) & (C = k1_tarski(A)))) & ~((B = k1_tarski(A)) & (C = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_zfmisc_1)).
% 2.36/1.35  tff(f_41, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.36/1.35  tff(f_53, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 2.36/1.35  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.36/1.35  tff(f_39, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.36/1.35  tff(f_35, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_xboole_1)).
% 2.36/1.35  tff(c_30, plain, (k1_tarski('#skF_1')!='#skF_3' | k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.36/1.35  tff(c_57, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_30])).
% 2.36/1.35  tff(c_28, plain, (k1_xboole_0!='#skF_3' | k1_tarski('#skF_1')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.36/1.35  tff(c_39, plain, (k1_tarski('#skF_1')!='#skF_2'), inference(splitLeft, [status(thm)], [c_28])).
% 2.36/1.35  tff(c_34, plain, (k2_xboole_0('#skF_2', '#skF_3')=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.36/1.35  tff(c_12, plain, (![A_8, B_9]: (r1_tarski(A_8, k2_xboole_0(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.36/1.35  tff(c_53, plain, (r1_tarski('#skF_2', k1_tarski('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_34, c_12])).
% 2.36/1.35  tff(c_236, plain, (![B_46, A_47]: (k1_tarski(B_46)=A_47 | k1_xboole_0=A_47 | ~r1_tarski(A_47, k1_tarski(B_46)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.36/1.35  tff(c_242, plain, (k1_tarski('#skF_1')='#skF_2' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_53, c_236])).
% 2.36/1.35  tff(c_254, plain, $false, inference(negUnitSimplification, [status(thm)], [c_57, c_39, c_242])).
% 2.36/1.35  tff(c_255, plain, (k1_tarski('#skF_1')!='#skF_3'), inference(splitRight, [status(thm)], [c_30])).
% 2.36/1.35  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.36/1.35  tff(c_264, plain, (![A_49, B_50]: (k2_xboole_0(A_49, B_50)=B_50 | ~r1_tarski(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.36/1.35  tff(c_276, plain, (![B_2]: (k2_xboole_0(B_2, B_2)=B_2)), inference(resolution, [status(thm)], [c_6, c_264])).
% 2.36/1.35  tff(c_348, plain, (![A_61, C_62, B_63]: (r1_tarski(A_61, k2_xboole_0(C_62, B_63)) | ~r1_tarski(A_61, B_63))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.36/1.35  tff(c_362, plain, (![A_61]: (r1_tarski(A_61, k1_tarski('#skF_1')) | ~r1_tarski(A_61, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_34, c_348])).
% 2.36/1.35  tff(c_256, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_30])).
% 2.36/1.35  tff(c_20, plain, (![B_17, A_16]: (k1_tarski(B_17)=A_16 | k1_xboole_0=A_16 | ~r1_tarski(A_16, k1_tarski(B_17)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.36/1.35  tff(c_410, plain, (![B_67, A_68]: (k1_tarski(B_67)=A_68 | A_68='#skF_2' | ~r1_tarski(A_68, k1_tarski(B_67)))), inference(demodulation, [status(thm), theory('equality')], [c_256, c_20])).
% 2.36/1.35  tff(c_426, plain, (![A_69]: (k1_tarski('#skF_1')=A_69 | A_69='#skF_2' | ~r1_tarski(A_69, '#skF_3'))), inference(resolution, [status(thm)], [c_362, c_410])).
% 2.36/1.35  tff(c_430, plain, (k1_tarski('#skF_1')='#skF_3' | '#skF_2'='#skF_3'), inference(resolution, [status(thm)], [c_6, c_426])).
% 2.36/1.35  tff(c_433, plain, ('#skF_2'='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_255, c_430])).
% 2.36/1.35  tff(c_440, plain, (k2_xboole_0('#skF_3', '#skF_3')=k1_tarski('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_433, c_34])).
% 2.36/1.35  tff(c_442, plain, (k1_tarski('#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_276, c_440])).
% 2.36/1.35  tff(c_444, plain, $false, inference(negUnitSimplification, [status(thm)], [c_255, c_442])).
% 2.36/1.35  tff(c_445, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_28])).
% 2.36/1.35  tff(c_446, plain, (k1_tarski('#skF_1')='#skF_2'), inference(splitRight, [status(thm)], [c_28])).
% 2.36/1.35  tff(c_32, plain, (k1_tarski('#skF_1')!='#skF_3' | k1_tarski('#skF_1')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.36/1.35  tff(c_475, plain, ('#skF_2'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_446, c_446, c_32])).
% 2.36/1.35  tff(c_455, plain, (k2_xboole_0('#skF_2', '#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_446, c_34])).
% 2.36/1.35  tff(c_552, plain, (![A_81, C_82, B_83]: (r1_tarski(A_81, k2_xboole_0(C_82, B_83)) | ~r1_tarski(A_81, B_83))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.36/1.35  tff(c_586, plain, (![A_85]: (r1_tarski(A_85, '#skF_2') | ~r1_tarski(A_85, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_455, c_552])).
% 2.36/1.35  tff(c_10, plain, (![A_6, B_7]: (k2_xboole_0(A_6, B_7)=B_7 | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.36/1.35  tff(c_591, plain, (![A_86]: (k2_xboole_0(A_86, '#skF_2')='#skF_2' | ~r1_tarski(A_86, '#skF_3'))), inference(resolution, [status(thm)], [c_586, c_10])).
% 2.36/1.35  tff(c_596, plain, (k2_xboole_0('#skF_3', '#skF_2')='#skF_2'), inference(resolution, [status(thm)], [c_6, c_591])).
% 2.36/1.35  tff(c_603, plain, (r1_tarski('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_596, c_12])).
% 2.36/1.35  tff(c_708, plain, (![B_93, A_94]: (k1_tarski(B_93)=A_94 | k1_xboole_0=A_94 | ~r1_tarski(A_94, k1_tarski(B_93)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.36/1.35  tff(c_711, plain, (![A_94]: (k1_tarski('#skF_1')=A_94 | k1_xboole_0=A_94 | ~r1_tarski(A_94, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_446, c_708])).
% 2.36/1.35  tff(c_724, plain, (![A_95]: (A_95='#skF_2' | k1_xboole_0=A_95 | ~r1_tarski(A_95, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_446, c_711])).
% 2.36/1.35  tff(c_727, plain, ('#skF_2'='#skF_3' | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_603, c_724])).
% 2.36/1.35  tff(c_741, plain, $false, inference(negUnitSimplification, [status(thm)], [c_445, c_475, c_727])).
% 2.36/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.36/1.35  
% 2.36/1.35  Inference rules
% 2.36/1.35  ----------------------
% 2.36/1.35  #Ref     : 0
% 2.36/1.35  #Sup     : 168
% 2.36/1.35  #Fact    : 0
% 2.36/1.35  #Define  : 0
% 2.36/1.35  #Split   : 3
% 2.36/1.35  #Chain   : 0
% 2.36/1.35  #Close   : 0
% 2.36/1.35  
% 2.36/1.35  Ordering : KBO
% 2.36/1.35  
% 2.36/1.35  Simplification rules
% 2.36/1.35  ----------------------
% 2.36/1.35  #Subsume      : 5
% 2.36/1.35  #Demod        : 78
% 2.36/1.35  #Tautology    : 112
% 2.36/1.35  #SimpNegUnit  : 8
% 2.36/1.35  #BackRed      : 9
% 2.36/1.35  
% 2.36/1.35  #Partial instantiations: 0
% 2.36/1.35  #Strategies tried      : 1
% 2.36/1.35  
% 2.36/1.35  Timing (in seconds)
% 2.36/1.35  ----------------------
% 2.36/1.35  Preprocessing        : 0.28
% 2.36/1.35  Parsing              : 0.15
% 2.36/1.35  CNF conversion       : 0.02
% 2.36/1.35  Main loop            : 0.29
% 2.36/1.35  Inferencing          : 0.11
% 2.36/1.35  Reduction            : 0.09
% 2.36/1.35  Demodulation         : 0.07
% 2.36/1.35  BG Simplification    : 0.01
% 2.36/1.35  Subsumption          : 0.05
% 2.36/1.35  Abstraction          : 0.01
% 2.36/1.35  MUC search           : 0.00
% 2.36/1.35  Cooper               : 0.00
% 2.36/1.35  Total                : 0.60
% 2.36/1.35  Index Insertion      : 0.00
% 2.36/1.35  Index Deletion       : 0.00
% 2.36/1.35  Index Matching       : 0.00
% 2.36/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
