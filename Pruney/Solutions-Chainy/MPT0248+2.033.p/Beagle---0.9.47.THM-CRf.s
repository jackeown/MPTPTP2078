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
% DateTime   : Thu Dec  3 09:50:08 EST 2020

% Result     : Theorem 3.16s
% Output     : CNFRefutation 3.16s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 169 expanded)
%              Number of leaves         :   24 (  64 expanded)
%              Depth                    :    8
%              Number of atoms          :   76 ( 376 expanded)
%              Number of equality atoms :   61 ( 337 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(f_78,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k1_tarski(A) = k2_xboole_0(B,C)
          & ~ ( B = k1_tarski(A)
              & C = k1_tarski(A) )
          & ~ ( B = k1_xboole_0
              & C = k1_tarski(A) )
          & ~ ( B = k1_tarski(A)
              & C = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_33,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_43,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_39,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(c_36,plain,
    ( k1_tarski('#skF_1') != '#skF_3'
    | k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_61,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_34,plain,
    ( k1_xboole_0 != '#skF_3'
    | k1_tarski('#skF_1') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_60,plain,(
    k1_tarski('#skF_1') != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_40,plain,(
    k2_xboole_0('#skF_2','#skF_3') = k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_14,plain,(
    ! [A_12,B_13] : r1_tarski(A_12,k2_xboole_0(A_12,B_13)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_75,plain,(
    r1_tarski('#skF_2',k1_tarski('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_14])).

tff(c_414,plain,(
    ! [B_58,A_59] :
      ( k1_tarski(B_58) = A_59
      | k1_xboole_0 = A_59
      | ~ r1_tarski(A_59,k1_tarski(B_58)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_423,plain,
    ( k1_tarski('#skF_1') = '#skF_2'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_75,c_414])).

tff(c_433,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_61,c_60,c_423])).

tff(c_434,plain,(
    k1_tarski('#skF_1') != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_481,plain,(
    ! [B_67,A_68] : k2_xboole_0(B_67,A_68) = k2_xboole_0(A_68,B_67) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_496,plain,(
    k2_xboole_0('#skF_3','#skF_2') = k1_tarski('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_481,c_40])).

tff(c_535,plain,(
    r1_tarski('#skF_3',k1_tarski('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_496,c_14])).

tff(c_435,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_26,plain,(
    ! [B_27,A_26] :
      ( k1_tarski(B_27) = A_26
      | k1_xboole_0 = A_26
      | ~ r1_tarski(A_26,k1_tarski(B_27)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1083,plain,(
    ! [B_100,A_101] :
      ( k1_tarski(B_100) = A_101
      | A_101 = '#skF_2'
      | ~ r1_tarski(A_101,k1_tarski(B_100)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_435,c_26])).

tff(c_1086,plain,
    ( k1_tarski('#skF_1') = '#skF_3'
    | '#skF_2' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_535,c_1083])).

tff(c_1095,plain,(
    '#skF_2' = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_434,c_1086])).

tff(c_6,plain,(
    ! [A_5] : k4_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_437,plain,(
    ! [A_5] : k4_xboole_0(A_5,'#skF_2') = A_5 ),
    inference(demodulation,[status(thm),theory(equality)],[c_435,c_6])).

tff(c_818,plain,(
    ! [A_89,B_90] : k5_xboole_0(A_89,k4_xboole_0(B_90,A_89)) = k2_xboole_0(A_89,B_90) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_854,plain,(
    ! [A_91] : k5_xboole_0('#skF_2',A_91) = k2_xboole_0('#skF_2',A_91) ),
    inference(superposition,[status(thm),theory(equality)],[c_437,c_818])).

tff(c_12,plain,(
    ! [A_11] : k5_xboole_0(A_11,k1_xboole_0) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_436,plain,(
    ! [A_11] : k5_xboole_0(A_11,'#skF_2') = A_11 ),
    inference(demodulation,[status(thm),theory(equality)],[c_435,c_12])).

tff(c_865,plain,(
    k2_xboole_0('#skF_2','#skF_2') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_854,c_436])).

tff(c_1102,plain,(
    k2_xboole_0('#skF_3','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1095,c_1095,c_1095,c_865])).

tff(c_1112,plain,(
    k2_xboole_0('#skF_3','#skF_3') = k1_tarski('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1095,c_40])).

tff(c_1217,plain,(
    k1_tarski('#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1102,c_1112])).

tff(c_1218,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_434,c_1217])).

tff(c_1219,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_1220,plain,(
    k1_tarski('#skF_1') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_38,plain,
    ( k1_tarski('#skF_1') != '#skF_3'
    | k1_tarski('#skF_1') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1248,plain,(
    '#skF_2' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1220,c_1220,c_38])).

tff(c_1258,plain,(
    ! [B_112,A_113] : k2_xboole_0(B_112,A_113) = k2_xboole_0(A_113,B_112) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_1239,plain,(
    k2_xboole_0('#skF_2','#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1220,c_40])).

tff(c_1273,plain,(
    k2_xboole_0('#skF_3','#skF_2') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_1258,c_1239])).

tff(c_1312,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1273,c_14])).

tff(c_1924,plain,(
    ! [B_140,A_141] :
      ( k1_tarski(B_140) = A_141
      | k1_xboole_0 = A_141
      | ~ r1_tarski(A_141,k1_tarski(B_140)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1930,plain,(
    ! [A_141] :
      ( k1_tarski('#skF_1') = A_141
      | k1_xboole_0 = A_141
      | ~ r1_tarski(A_141,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1220,c_1924])).

tff(c_1939,plain,(
    ! [A_142] :
      ( A_142 = '#skF_2'
      | k1_xboole_0 = A_142
      | ~ r1_tarski(A_142,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1220,c_1930])).

tff(c_1942,plain,
    ( '#skF_2' = '#skF_3'
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_1312,c_1939])).

tff(c_1952,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1219,c_1248,c_1942])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:50:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.16/1.57  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.16/1.57  
% 3.16/1.57  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.16/1.58  %$ r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.16/1.58  
% 3.16/1.58  %Foreground sorts:
% 3.16/1.58  
% 3.16/1.58  
% 3.16/1.58  %Background operators:
% 3.16/1.58  
% 3.16/1.58  
% 3.16/1.58  %Foreground operators:
% 3.16/1.58  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.16/1.58  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.16/1.58  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.16/1.58  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.16/1.58  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.16/1.58  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.16/1.58  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.16/1.58  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.16/1.58  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.16/1.58  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.16/1.58  tff('#skF_2', type, '#skF_2': $i).
% 3.16/1.58  tff('#skF_3', type, '#skF_3': $i).
% 3.16/1.58  tff('#skF_1', type, '#skF_1': $i).
% 3.16/1.58  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.16/1.58  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.16/1.58  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.16/1.58  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.16/1.58  
% 3.16/1.59  tff(f_78, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~((B = k1_tarski(A)) & (C = k1_tarski(A)))) & ~((B = k1_xboole_0) & (C = k1_tarski(A)))) & ~((B = k1_tarski(A)) & (C = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_zfmisc_1)).
% 3.16/1.59  tff(f_41, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 3.16/1.59  tff(f_57, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 3.16/1.59  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 3.16/1.59  tff(f_33, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 3.16/1.59  tff(f_43, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 3.16/1.59  tff(f_39, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 3.16/1.59  tff(c_36, plain, (k1_tarski('#skF_1')!='#skF_3' | k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.16/1.59  tff(c_61, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_36])).
% 3.16/1.59  tff(c_34, plain, (k1_xboole_0!='#skF_3' | k1_tarski('#skF_1')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.16/1.59  tff(c_60, plain, (k1_tarski('#skF_1')!='#skF_2'), inference(splitLeft, [status(thm)], [c_34])).
% 3.16/1.59  tff(c_40, plain, (k2_xboole_0('#skF_2', '#skF_3')=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.16/1.59  tff(c_14, plain, (![A_12, B_13]: (r1_tarski(A_12, k2_xboole_0(A_12, B_13)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.16/1.59  tff(c_75, plain, (r1_tarski('#skF_2', k1_tarski('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_40, c_14])).
% 3.16/1.59  tff(c_414, plain, (![B_58, A_59]: (k1_tarski(B_58)=A_59 | k1_xboole_0=A_59 | ~r1_tarski(A_59, k1_tarski(B_58)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.16/1.59  tff(c_423, plain, (k1_tarski('#skF_1')='#skF_2' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_75, c_414])).
% 3.16/1.59  tff(c_433, plain, $false, inference(negUnitSimplification, [status(thm)], [c_61, c_60, c_423])).
% 3.16/1.59  tff(c_434, plain, (k1_tarski('#skF_1')!='#skF_3'), inference(splitRight, [status(thm)], [c_36])).
% 3.16/1.59  tff(c_481, plain, (![B_67, A_68]: (k2_xboole_0(B_67, A_68)=k2_xboole_0(A_68, B_67))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.16/1.59  tff(c_496, plain, (k2_xboole_0('#skF_3', '#skF_2')=k1_tarski('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_481, c_40])).
% 3.16/1.59  tff(c_535, plain, (r1_tarski('#skF_3', k1_tarski('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_496, c_14])).
% 3.16/1.59  tff(c_435, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_36])).
% 3.16/1.59  tff(c_26, plain, (![B_27, A_26]: (k1_tarski(B_27)=A_26 | k1_xboole_0=A_26 | ~r1_tarski(A_26, k1_tarski(B_27)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.16/1.59  tff(c_1083, plain, (![B_100, A_101]: (k1_tarski(B_100)=A_101 | A_101='#skF_2' | ~r1_tarski(A_101, k1_tarski(B_100)))), inference(demodulation, [status(thm), theory('equality')], [c_435, c_26])).
% 3.16/1.59  tff(c_1086, plain, (k1_tarski('#skF_1')='#skF_3' | '#skF_2'='#skF_3'), inference(resolution, [status(thm)], [c_535, c_1083])).
% 3.16/1.59  tff(c_1095, plain, ('#skF_2'='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_434, c_1086])).
% 3.16/1.59  tff(c_6, plain, (![A_5]: (k4_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.16/1.59  tff(c_437, plain, (![A_5]: (k4_xboole_0(A_5, '#skF_2')=A_5)), inference(demodulation, [status(thm), theory('equality')], [c_435, c_6])).
% 3.16/1.59  tff(c_818, plain, (![A_89, B_90]: (k5_xboole_0(A_89, k4_xboole_0(B_90, A_89))=k2_xboole_0(A_89, B_90))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.16/1.59  tff(c_854, plain, (![A_91]: (k5_xboole_0('#skF_2', A_91)=k2_xboole_0('#skF_2', A_91))), inference(superposition, [status(thm), theory('equality')], [c_437, c_818])).
% 3.16/1.59  tff(c_12, plain, (![A_11]: (k5_xboole_0(A_11, k1_xboole_0)=A_11)), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.16/1.59  tff(c_436, plain, (![A_11]: (k5_xboole_0(A_11, '#skF_2')=A_11)), inference(demodulation, [status(thm), theory('equality')], [c_435, c_12])).
% 3.16/1.59  tff(c_865, plain, (k2_xboole_0('#skF_2', '#skF_2')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_854, c_436])).
% 3.16/1.59  tff(c_1102, plain, (k2_xboole_0('#skF_3', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1095, c_1095, c_1095, c_865])).
% 3.16/1.59  tff(c_1112, plain, (k2_xboole_0('#skF_3', '#skF_3')=k1_tarski('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1095, c_40])).
% 3.16/1.59  tff(c_1217, plain, (k1_tarski('#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1102, c_1112])).
% 3.16/1.59  tff(c_1218, plain, $false, inference(negUnitSimplification, [status(thm)], [c_434, c_1217])).
% 3.16/1.59  tff(c_1219, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_34])).
% 3.16/1.59  tff(c_1220, plain, (k1_tarski('#skF_1')='#skF_2'), inference(splitRight, [status(thm)], [c_34])).
% 3.16/1.59  tff(c_38, plain, (k1_tarski('#skF_1')!='#skF_3' | k1_tarski('#skF_1')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.16/1.59  tff(c_1248, plain, ('#skF_2'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1220, c_1220, c_38])).
% 3.16/1.59  tff(c_1258, plain, (![B_112, A_113]: (k2_xboole_0(B_112, A_113)=k2_xboole_0(A_113, B_112))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.16/1.59  tff(c_1239, plain, (k2_xboole_0('#skF_2', '#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1220, c_40])).
% 3.16/1.59  tff(c_1273, plain, (k2_xboole_0('#skF_3', '#skF_2')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_1258, c_1239])).
% 3.16/1.59  tff(c_1312, plain, (r1_tarski('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1273, c_14])).
% 3.16/1.59  tff(c_1924, plain, (![B_140, A_141]: (k1_tarski(B_140)=A_141 | k1_xboole_0=A_141 | ~r1_tarski(A_141, k1_tarski(B_140)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.16/1.59  tff(c_1930, plain, (![A_141]: (k1_tarski('#skF_1')=A_141 | k1_xboole_0=A_141 | ~r1_tarski(A_141, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1220, c_1924])).
% 3.16/1.59  tff(c_1939, plain, (![A_142]: (A_142='#skF_2' | k1_xboole_0=A_142 | ~r1_tarski(A_142, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_1220, c_1930])).
% 3.16/1.59  tff(c_1942, plain, ('#skF_2'='#skF_3' | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_1312, c_1939])).
% 3.16/1.59  tff(c_1952, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1219, c_1248, c_1942])).
% 3.16/1.59  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.16/1.59  
% 3.16/1.59  Inference rules
% 3.16/1.59  ----------------------
% 3.16/1.59  #Ref     : 0
% 3.16/1.59  #Sup     : 503
% 3.16/1.59  #Fact    : 0
% 3.16/1.59  #Define  : 0
% 3.16/1.59  #Split   : 3
% 3.16/1.59  #Chain   : 0
% 3.16/1.59  #Close   : 0
% 3.16/1.59  
% 3.16/1.59  Ordering : KBO
% 3.16/1.59  
% 3.16/1.59  Simplification rules
% 3.16/1.59  ----------------------
% 3.16/1.59  #Subsume      : 9
% 3.16/1.59  #Demod        : 288
% 3.16/1.59  #Tautology    : 383
% 3.16/1.59  #SimpNegUnit  : 4
% 3.16/1.59  #BackRed      : 21
% 3.16/1.59  
% 3.16/1.59  #Partial instantiations: 0
% 3.16/1.59  #Strategies tried      : 1
% 3.16/1.59  
% 3.16/1.59  Timing (in seconds)
% 3.16/1.59  ----------------------
% 3.16/1.59  Preprocessing        : 0.31
% 3.16/1.59  Parsing              : 0.17
% 3.16/1.59  CNF conversion       : 0.02
% 3.16/1.59  Main loop            : 0.46
% 3.16/1.59  Inferencing          : 0.16
% 3.16/1.59  Reduction            : 0.18
% 3.16/1.59  Demodulation         : 0.14
% 3.16/1.59  BG Simplification    : 0.02
% 3.16/1.59  Subsumption          : 0.06
% 3.16/1.59  Abstraction          : 0.02
% 3.16/1.59  MUC search           : 0.00
% 3.16/1.59  Cooper               : 0.00
% 3.16/1.59  Total                : 0.80
% 3.16/1.59  Index Insertion      : 0.00
% 3.16/1.59  Index Deletion       : 0.00
% 3.16/1.59  Index Matching       : 0.00
% 3.16/1.59  BG Taut test         : 0.00
%------------------------------------------------------------------------------
