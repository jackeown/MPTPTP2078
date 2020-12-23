%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:08 EST 2020

% Result     : Theorem 3.08s
% Output     : CNFRefutation 3.41s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 102 expanded)
%              Number of leaves         :   26 (  44 expanded)
%              Depth                    :    8
%              Number of atoms          :   72 ( 210 expanded)
%              Number of equality atoms :   53 ( 189 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_83,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k1_tarski(A) = k2_xboole_0(B,C)
          & ~ ( B = k1_tarski(A)
              & C = k1_tarski(A) )
          & ~ ( B = k1_xboole_0
              & C = k1_tarski(A) )
          & ~ ( B = k1_tarski(A)
              & C = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).

tff(f_46,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_44,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_40,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_48,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(c_40,plain,
    ( k1_tarski('#skF_1') != '#skF_3'
    | k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_57,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_38,plain,
    ( k1_xboole_0 != '#skF_3'
    | k1_tarski('#skF_1') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_56,plain,(
    k1_tarski('#skF_1') != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_44,plain,(
    k2_xboole_0('#skF_2','#skF_3') = k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_72,plain,(
    ! [A_33,B_34] : r1_tarski(A_33,k2_xboole_0(A_33,B_34)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_75,plain,(
    r1_tarski('#skF_2',k1_tarski('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_72])).

tff(c_758,plain,(
    ! [B_74,A_75] :
      ( k1_tarski(B_74) = A_75
      | k1_xboole_0 = A_75
      | ~ r1_tarski(A_75,k1_tarski(B_74)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_772,plain,
    ( k1_tarski('#skF_1') = '#skF_2'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_75,c_758])).

tff(c_784,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_57,c_56,c_772])).

tff(c_785,plain,(
    k1_tarski('#skF_1') != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_786,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_16,plain,(
    ! [A_10] : k5_xboole_0(A_10,k1_xboole_0) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_787,plain,(
    ! [A_10] : k5_xboole_0(A_10,'#skF_2') = A_10 ),
    inference(demodulation,[status(thm),theory(equality)],[c_786,c_16])).

tff(c_12,plain,(
    ! [A_7] : r1_tarski(k1_xboole_0,A_7) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_788,plain,(
    ! [A_7] : r1_tarski('#skF_2',A_7) ),
    inference(demodulation,[status(thm),theory(equality)],[c_786,c_12])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( k4_xboole_0(A_5,B_6) = k1_xboole_0
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_943,plain,(
    ! [A_94,B_95] :
      ( k4_xboole_0(A_94,B_95) = '#skF_2'
      | ~ r1_tarski(A_94,B_95) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_786,c_10])).

tff(c_967,plain,(
    ! [A_7] : k4_xboole_0('#skF_2',A_7) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_788,c_943])).

tff(c_1142,plain,(
    ! [A_109,B_110] : k5_xboole_0(A_109,k4_xboole_0(B_110,A_109)) = k2_xboole_0(A_109,B_110) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_1169,plain,(
    ! [A_7] : k5_xboole_0(A_7,'#skF_2') = k2_xboole_0(A_7,'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_967,c_1142])).

tff(c_1178,plain,(
    ! [A_7] : k2_xboole_0(A_7,'#skF_2') = A_7 ),
    inference(demodulation,[status(thm),theory(equality)],[c_787,c_1169])).

tff(c_828,plain,(
    ! [B_84,A_85] : k2_xboole_0(B_84,A_85) = k2_xboole_0(A_85,B_84) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_858,plain,(
    k2_xboole_0('#skF_3','#skF_2') = k1_tarski('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_828,c_44])).

tff(c_1179,plain,(
    k1_tarski('#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1178,c_858])).

tff(c_1181,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_785,c_1179])).

tff(c_1182,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_1183,plain,(
    k1_tarski('#skF_1') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_42,plain,
    ( k1_tarski('#skF_1') != '#skF_3'
    | k1_tarski('#skF_1') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_1225,plain,(
    '#skF_2' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1183,c_1183,c_42])).

tff(c_1226,plain,(
    ! [B_117,A_118] : k2_xboole_0(B_117,A_118) = k2_xboole_0(A_118,B_117) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_1210,plain,(
    k2_xboole_0('#skF_2','#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1183,c_44])).

tff(c_1247,plain,(
    k2_xboole_0('#skF_3','#skF_2') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_1226,c_1210])).

tff(c_18,plain,(
    ! [A_11,B_12] : r1_tarski(A_11,k2_xboole_0(A_11,B_12)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1289,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1247,c_18])).

tff(c_1965,plain,(
    ! [B_151,A_152] :
      ( k1_tarski(B_151) = A_152
      | k1_xboole_0 = A_152
      | ~ r1_tarski(A_152,k1_tarski(B_151)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_1976,plain,(
    ! [A_152] :
      ( k1_tarski('#skF_1') = A_152
      | k1_xboole_0 = A_152
      | ~ r1_tarski(A_152,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1183,c_1965])).

tff(c_1990,plain,(
    ! [A_153] :
      ( A_153 = '#skF_2'
      | k1_xboole_0 = A_153
      | ~ r1_tarski(A_153,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1183,c_1976])).

tff(c_2001,plain,
    ( '#skF_2' = '#skF_3'
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_1289,c_1990])).

tff(c_2014,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1182,c_1225,c_2001])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 17:21:05 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.08/1.62  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.08/1.63  
% 3.08/1.63  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.41/1.63  %$ r1_tarski > v1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.41/1.63  
% 3.41/1.63  %Foreground sorts:
% 3.41/1.63  
% 3.41/1.63  
% 3.41/1.63  %Background operators:
% 3.41/1.63  
% 3.41/1.63  
% 3.41/1.63  %Foreground operators:
% 3.41/1.63  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.41/1.63  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.41/1.63  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.41/1.63  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.41/1.63  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.41/1.63  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.41/1.63  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.41/1.63  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.41/1.63  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.41/1.63  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.41/1.63  tff('#skF_2', type, '#skF_2': $i).
% 3.41/1.63  tff('#skF_3', type, '#skF_3': $i).
% 3.41/1.63  tff('#skF_1', type, '#skF_1': $i).
% 3.41/1.63  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.41/1.63  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.41/1.63  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.41/1.63  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.41/1.63  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.41/1.63  
% 3.41/1.64  tff(f_83, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~((B = k1_tarski(A)) & (C = k1_tarski(A)))) & ~((B = k1_xboole_0) & (C = k1_tarski(A)))) & ~((B = k1_tarski(A)) & (C = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_zfmisc_1)).
% 3.41/1.64  tff(f_46, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 3.41/1.64  tff(f_62, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 3.41/1.64  tff(f_44, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 3.41/1.64  tff(f_40, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.41/1.64  tff(f_38, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 3.41/1.64  tff(f_48, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 3.41/1.64  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 3.41/1.64  tff(c_40, plain, (k1_tarski('#skF_1')!='#skF_3' | k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.41/1.64  tff(c_57, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_40])).
% 3.41/1.64  tff(c_38, plain, (k1_xboole_0!='#skF_3' | k1_tarski('#skF_1')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.41/1.64  tff(c_56, plain, (k1_tarski('#skF_1')!='#skF_2'), inference(splitLeft, [status(thm)], [c_38])).
% 3.41/1.64  tff(c_44, plain, (k2_xboole_0('#skF_2', '#skF_3')=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.41/1.64  tff(c_72, plain, (![A_33, B_34]: (r1_tarski(A_33, k2_xboole_0(A_33, B_34)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.41/1.64  tff(c_75, plain, (r1_tarski('#skF_2', k1_tarski('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_44, c_72])).
% 3.41/1.64  tff(c_758, plain, (![B_74, A_75]: (k1_tarski(B_74)=A_75 | k1_xboole_0=A_75 | ~r1_tarski(A_75, k1_tarski(B_74)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.41/1.64  tff(c_772, plain, (k1_tarski('#skF_1')='#skF_2' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_75, c_758])).
% 3.41/1.64  tff(c_784, plain, $false, inference(negUnitSimplification, [status(thm)], [c_57, c_56, c_772])).
% 3.41/1.64  tff(c_785, plain, (k1_tarski('#skF_1')!='#skF_3'), inference(splitRight, [status(thm)], [c_40])).
% 3.41/1.64  tff(c_786, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_40])).
% 3.41/1.64  tff(c_16, plain, (![A_10]: (k5_xboole_0(A_10, k1_xboole_0)=A_10)), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.41/1.64  tff(c_787, plain, (![A_10]: (k5_xboole_0(A_10, '#skF_2')=A_10)), inference(demodulation, [status(thm), theory('equality')], [c_786, c_16])).
% 3.41/1.64  tff(c_12, plain, (![A_7]: (r1_tarski(k1_xboole_0, A_7))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.41/1.64  tff(c_788, plain, (![A_7]: (r1_tarski('#skF_2', A_7))), inference(demodulation, [status(thm), theory('equality')], [c_786, c_12])).
% 3.41/1.64  tff(c_10, plain, (![A_5, B_6]: (k4_xboole_0(A_5, B_6)=k1_xboole_0 | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.41/1.64  tff(c_943, plain, (![A_94, B_95]: (k4_xboole_0(A_94, B_95)='#skF_2' | ~r1_tarski(A_94, B_95))), inference(demodulation, [status(thm), theory('equality')], [c_786, c_10])).
% 3.41/1.64  tff(c_967, plain, (![A_7]: (k4_xboole_0('#skF_2', A_7)='#skF_2')), inference(resolution, [status(thm)], [c_788, c_943])).
% 3.41/1.64  tff(c_1142, plain, (![A_109, B_110]: (k5_xboole_0(A_109, k4_xboole_0(B_110, A_109))=k2_xboole_0(A_109, B_110))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.41/1.64  tff(c_1169, plain, (![A_7]: (k5_xboole_0(A_7, '#skF_2')=k2_xboole_0(A_7, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_967, c_1142])).
% 3.41/1.64  tff(c_1178, plain, (![A_7]: (k2_xboole_0(A_7, '#skF_2')=A_7)), inference(demodulation, [status(thm), theory('equality')], [c_787, c_1169])).
% 3.41/1.64  tff(c_828, plain, (![B_84, A_85]: (k2_xboole_0(B_84, A_85)=k2_xboole_0(A_85, B_84))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.41/1.64  tff(c_858, plain, (k2_xboole_0('#skF_3', '#skF_2')=k1_tarski('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_828, c_44])).
% 3.41/1.64  tff(c_1179, plain, (k1_tarski('#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1178, c_858])).
% 3.41/1.64  tff(c_1181, plain, $false, inference(negUnitSimplification, [status(thm)], [c_785, c_1179])).
% 3.41/1.64  tff(c_1182, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_38])).
% 3.41/1.64  tff(c_1183, plain, (k1_tarski('#skF_1')='#skF_2'), inference(splitRight, [status(thm)], [c_38])).
% 3.41/1.64  tff(c_42, plain, (k1_tarski('#skF_1')!='#skF_3' | k1_tarski('#skF_1')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.41/1.64  tff(c_1225, plain, ('#skF_2'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1183, c_1183, c_42])).
% 3.41/1.64  tff(c_1226, plain, (![B_117, A_118]: (k2_xboole_0(B_117, A_118)=k2_xboole_0(A_118, B_117))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.41/1.64  tff(c_1210, plain, (k2_xboole_0('#skF_2', '#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1183, c_44])).
% 3.41/1.64  tff(c_1247, plain, (k2_xboole_0('#skF_3', '#skF_2')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_1226, c_1210])).
% 3.41/1.64  tff(c_18, plain, (![A_11, B_12]: (r1_tarski(A_11, k2_xboole_0(A_11, B_12)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.41/1.64  tff(c_1289, plain, (r1_tarski('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1247, c_18])).
% 3.41/1.64  tff(c_1965, plain, (![B_151, A_152]: (k1_tarski(B_151)=A_152 | k1_xboole_0=A_152 | ~r1_tarski(A_152, k1_tarski(B_151)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.41/1.64  tff(c_1976, plain, (![A_152]: (k1_tarski('#skF_1')=A_152 | k1_xboole_0=A_152 | ~r1_tarski(A_152, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1183, c_1965])).
% 3.41/1.64  tff(c_1990, plain, (![A_153]: (A_153='#skF_2' | k1_xboole_0=A_153 | ~r1_tarski(A_153, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_1183, c_1976])).
% 3.41/1.64  tff(c_2001, plain, ('#skF_2'='#skF_3' | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_1289, c_1990])).
% 3.41/1.64  tff(c_2014, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1182, c_1225, c_2001])).
% 3.41/1.64  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.41/1.64  
% 3.41/1.64  Inference rules
% 3.41/1.64  ----------------------
% 3.41/1.64  #Ref     : 0
% 3.41/1.64  #Sup     : 501
% 3.41/1.64  #Fact    : 0
% 3.41/1.64  #Define  : 0
% 3.41/1.64  #Split   : 7
% 3.41/1.64  #Chain   : 0
% 3.41/1.64  #Close   : 0
% 3.41/1.64  
% 3.41/1.64  Ordering : KBO
% 3.41/1.64  
% 3.41/1.64  Simplification rules
% 3.41/1.64  ----------------------
% 3.41/1.64  #Subsume      : 41
% 3.41/1.64  #Demod        : 236
% 3.41/1.64  #Tautology    : 371
% 3.41/1.64  #SimpNegUnit  : 11
% 3.41/1.64  #BackRed      : 15
% 3.41/1.64  
% 3.41/1.64  #Partial instantiations: 0
% 3.41/1.64  #Strategies tried      : 1
% 3.41/1.64  
% 3.41/1.64  Timing (in seconds)
% 3.41/1.64  ----------------------
% 3.41/1.64  Preprocessing        : 0.34
% 3.41/1.64  Parsing              : 0.18
% 3.41/1.64  CNF conversion       : 0.02
% 3.41/1.64  Main loop            : 0.45
% 3.41/1.64  Inferencing          : 0.16
% 3.41/1.64  Reduction            : 0.17
% 3.41/1.64  Demodulation         : 0.13
% 3.41/1.65  BG Simplification    : 0.02
% 3.41/1.65  Subsumption          : 0.07
% 3.41/1.65  Abstraction          : 0.02
% 3.41/1.65  MUC search           : 0.00
% 3.41/1.65  Cooper               : 0.00
% 3.41/1.65  Total                : 0.82
% 3.41/1.65  Index Insertion      : 0.00
% 3.41/1.65  Index Deletion       : 0.00
% 3.41/1.65  Index Matching       : 0.00
% 3.41/1.65  BG Taut test         : 0.00
%------------------------------------------------------------------------------
