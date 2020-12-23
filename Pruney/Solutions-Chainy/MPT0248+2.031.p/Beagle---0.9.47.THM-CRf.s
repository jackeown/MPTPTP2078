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
% DateTime   : Thu Dec  3 09:50:08 EST 2020

% Result     : Theorem 2.45s
% Output     : CNFRefutation 2.45s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 184 expanded)
%              Number of leaves         :   26 (  69 expanded)
%              Depth                    :    9
%              Number of atoms          :   82 ( 404 expanded)
%              Number of equality atoms :   66 ( 365 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_72,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k1_tarski(A) = k2_xboole_0(B,C)
          & ~ ( B = k1_tarski(A)
              & C = k1_tarski(A) )
          & ~ ( B = k1_xboole_0
              & C = k1_tarski(A) )
          & ~ ( B = k1_tarski(A)
              & C = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_33,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_37,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_31,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(c_32,plain,
    ( k1_tarski('#skF_1') != '#skF_3'
    | k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_59,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_30,plain,
    ( k1_xboole_0 != '#skF_3'
    | k1_tarski('#skF_1') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_54,plain,(
    k1_tarski('#skF_1') != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_36,plain,(
    k2_xboole_0('#skF_2','#skF_3') = k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_60,plain,(
    ! [A_28,B_29] : r1_tarski(A_28,k2_xboole_0(A_28,B_29)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_63,plain,(
    r1_tarski('#skF_2',k1_tarski('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_60])).

tff(c_253,plain,(
    ! [B_47,A_48] :
      ( k1_tarski(B_47) = A_48
      | k1_xboole_0 = A_48
      | ~ r1_tarski(A_48,k1_tarski(B_47)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_262,plain,
    ( k1_tarski('#skF_1') = '#skF_2'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_63,c_253])).

tff(c_272,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_59,c_54,c_262])).

tff(c_273,plain,(
    k1_tarski('#skF_1') != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_314,plain,(
    ! [B_56,A_57] : k2_xboole_0(B_56,A_57) = k2_xboole_0(A_57,B_56) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_335,plain,(
    k2_xboole_0('#skF_3','#skF_2') = k1_tarski('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_314,c_36])).

tff(c_10,plain,(
    ! [A_7,B_8] : r1_tarski(A_7,k2_xboole_0(A_7,B_8)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_368,plain,(
    r1_tarski('#skF_3',k1_tarski('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_335,c_10])).

tff(c_274,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_22,plain,(
    ! [B_22,A_21] :
      ( k1_tarski(B_22) = A_21
      | k1_xboole_0 = A_21
      | ~ r1_tarski(A_21,k1_tarski(B_22)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_494,plain,(
    ! [B_71,A_72] :
      ( k1_tarski(B_71) = A_72
      | A_72 = '#skF_2'
      | ~ r1_tarski(A_72,k1_tarski(B_71)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_274,c_22])).

tff(c_497,plain,
    ( k1_tarski('#skF_1') = '#skF_3'
    | '#skF_2' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_368,c_494])).

tff(c_506,plain,(
    '#skF_2' = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_273,c_497])).

tff(c_8,plain,(
    ! [A_6] : k4_xboole_0(A_6,k1_xboole_0) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_275,plain,(
    ! [A_6] : k4_xboole_0(A_6,'#skF_2') = A_6 ),
    inference(demodulation,[status(thm),theory(equality)],[c_274,c_8])).

tff(c_414,plain,(
    ! [A_64,B_65] : k5_xboole_0(A_64,k4_xboole_0(B_65,A_64)) = k2_xboole_0(A_64,B_65) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_423,plain,(
    ! [A_6] : k5_xboole_0('#skF_2',A_6) = k2_xboole_0('#skF_2',A_6) ),
    inference(superposition,[status(thm),theory(equality)],[c_275,c_414])).

tff(c_586,plain,(
    ! [A_80] : k5_xboole_0('#skF_3',A_80) = k2_xboole_0('#skF_3',A_80) ),
    inference(demodulation,[status(thm),theory(equality)],[c_506,c_506,c_423])).

tff(c_6,plain,(
    ! [A_5] : k3_xboole_0(A_5,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_276,plain,(
    ! [A_5] : k3_xboole_0(A_5,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_274,c_274,c_6])).

tff(c_472,plain,(
    ! [A_69,B_70] : k5_xboole_0(A_69,k3_xboole_0(A_69,B_70)) = k4_xboole_0(A_69,B_70) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_489,plain,(
    ! [A_5] : k5_xboole_0(A_5,'#skF_2') = k4_xboole_0(A_5,'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_276,c_472])).

tff(c_492,plain,(
    ! [A_5] : k5_xboole_0(A_5,'#skF_2') = A_5 ),
    inference(demodulation,[status(thm),theory(equality)],[c_275,c_489])).

tff(c_528,plain,(
    ! [A_5] : k5_xboole_0(A_5,'#skF_3') = A_5 ),
    inference(demodulation,[status(thm),theory(equality)],[c_506,c_492])).

tff(c_593,plain,(
    k2_xboole_0('#skF_3','#skF_3') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_586,c_528])).

tff(c_518,plain,(
    k2_xboole_0('#skF_3','#skF_3') = k1_tarski('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_506,c_36])).

tff(c_621,plain,(
    k1_tarski('#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_593,c_518])).

tff(c_623,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_273,c_621])).

tff(c_624,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_625,plain,(
    k1_tarski('#skF_1') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_34,plain,
    ( k1_tarski('#skF_1') != '#skF_3'
    | k1_tarski('#skF_1') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_668,plain,(
    '#skF_2' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_625,c_625,c_34])).

tff(c_669,plain,(
    ! [B_85,A_86] : k2_xboole_0(B_85,A_86) = k2_xboole_0(A_86,B_85) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_630,plain,(
    k2_xboole_0('#skF_2','#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_625,c_36])).

tff(c_690,plain,(
    k2_xboole_0('#skF_3','#skF_2') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_669,c_630])).

tff(c_723,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_690,c_10])).

tff(c_904,plain,(
    ! [B_104,A_105] :
      ( k1_tarski(B_104) = A_105
      | k1_xboole_0 = A_105
      | ~ r1_tarski(A_105,k1_tarski(B_104)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_910,plain,(
    ! [A_105] :
      ( k1_tarski('#skF_1') = A_105
      | k1_xboole_0 = A_105
      | ~ r1_tarski(A_105,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_625,c_904])).

tff(c_919,plain,(
    ! [A_106] :
      ( A_106 = '#skF_2'
      | k1_xboole_0 = A_106
      | ~ r1_tarski(A_106,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_625,c_910])).

tff(c_922,plain,
    ( '#skF_2' = '#skF_3'
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_723,c_919])).

tff(c_932,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_624,c_668,c_922])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:09:11 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.45/1.33  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.45/1.34  
% 2.45/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.45/1.34  %$ r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.45/1.34  
% 2.45/1.34  %Foreground sorts:
% 2.45/1.34  
% 2.45/1.34  
% 2.45/1.34  %Background operators:
% 2.45/1.34  
% 2.45/1.34  
% 2.45/1.34  %Foreground operators:
% 2.45/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.45/1.34  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.45/1.34  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.45/1.34  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.45/1.34  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.45/1.34  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.45/1.34  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.45/1.34  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.45/1.34  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.45/1.34  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.45/1.34  tff('#skF_2', type, '#skF_2': $i).
% 2.45/1.34  tff('#skF_3', type, '#skF_3': $i).
% 2.45/1.34  tff('#skF_1', type, '#skF_1': $i).
% 2.45/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.45/1.34  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.45/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.45/1.34  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.45/1.34  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.45/1.34  
% 2.45/1.35  tff(f_72, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~((B = k1_tarski(A)) & (C = k1_tarski(A)))) & ~((B = k1_xboole_0) & (C = k1_tarski(A)))) & ~((B = k1_tarski(A)) & (C = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_zfmisc_1)).
% 2.45/1.35  tff(f_35, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.45/1.35  tff(f_51, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 2.45/1.35  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.45/1.35  tff(f_33, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 2.45/1.35  tff(f_37, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 2.45/1.35  tff(f_31, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 2.45/1.35  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.45/1.35  tff(c_32, plain, (k1_tarski('#skF_1')!='#skF_3' | k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.45/1.35  tff(c_59, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_32])).
% 2.45/1.35  tff(c_30, plain, (k1_xboole_0!='#skF_3' | k1_tarski('#skF_1')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.45/1.35  tff(c_54, plain, (k1_tarski('#skF_1')!='#skF_2'), inference(splitLeft, [status(thm)], [c_30])).
% 2.45/1.35  tff(c_36, plain, (k2_xboole_0('#skF_2', '#skF_3')=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.45/1.35  tff(c_60, plain, (![A_28, B_29]: (r1_tarski(A_28, k2_xboole_0(A_28, B_29)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.45/1.35  tff(c_63, plain, (r1_tarski('#skF_2', k1_tarski('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_36, c_60])).
% 2.45/1.35  tff(c_253, plain, (![B_47, A_48]: (k1_tarski(B_47)=A_48 | k1_xboole_0=A_48 | ~r1_tarski(A_48, k1_tarski(B_47)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.45/1.35  tff(c_262, plain, (k1_tarski('#skF_1')='#skF_2' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_63, c_253])).
% 2.45/1.35  tff(c_272, plain, $false, inference(negUnitSimplification, [status(thm)], [c_59, c_54, c_262])).
% 2.45/1.35  tff(c_273, plain, (k1_tarski('#skF_1')!='#skF_3'), inference(splitRight, [status(thm)], [c_32])).
% 2.45/1.35  tff(c_314, plain, (![B_56, A_57]: (k2_xboole_0(B_56, A_57)=k2_xboole_0(A_57, B_56))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.45/1.35  tff(c_335, plain, (k2_xboole_0('#skF_3', '#skF_2')=k1_tarski('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_314, c_36])).
% 2.45/1.35  tff(c_10, plain, (![A_7, B_8]: (r1_tarski(A_7, k2_xboole_0(A_7, B_8)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.45/1.35  tff(c_368, plain, (r1_tarski('#skF_3', k1_tarski('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_335, c_10])).
% 2.45/1.35  tff(c_274, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_32])).
% 2.45/1.35  tff(c_22, plain, (![B_22, A_21]: (k1_tarski(B_22)=A_21 | k1_xboole_0=A_21 | ~r1_tarski(A_21, k1_tarski(B_22)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.45/1.35  tff(c_494, plain, (![B_71, A_72]: (k1_tarski(B_71)=A_72 | A_72='#skF_2' | ~r1_tarski(A_72, k1_tarski(B_71)))), inference(demodulation, [status(thm), theory('equality')], [c_274, c_22])).
% 2.45/1.35  tff(c_497, plain, (k1_tarski('#skF_1')='#skF_3' | '#skF_2'='#skF_3'), inference(resolution, [status(thm)], [c_368, c_494])).
% 2.45/1.35  tff(c_506, plain, ('#skF_2'='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_273, c_497])).
% 2.45/1.35  tff(c_8, plain, (![A_6]: (k4_xboole_0(A_6, k1_xboole_0)=A_6)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.45/1.35  tff(c_275, plain, (![A_6]: (k4_xboole_0(A_6, '#skF_2')=A_6)), inference(demodulation, [status(thm), theory('equality')], [c_274, c_8])).
% 2.45/1.35  tff(c_414, plain, (![A_64, B_65]: (k5_xboole_0(A_64, k4_xboole_0(B_65, A_64))=k2_xboole_0(A_64, B_65))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.45/1.35  tff(c_423, plain, (![A_6]: (k5_xboole_0('#skF_2', A_6)=k2_xboole_0('#skF_2', A_6))), inference(superposition, [status(thm), theory('equality')], [c_275, c_414])).
% 2.45/1.35  tff(c_586, plain, (![A_80]: (k5_xboole_0('#skF_3', A_80)=k2_xboole_0('#skF_3', A_80))), inference(demodulation, [status(thm), theory('equality')], [c_506, c_506, c_423])).
% 2.45/1.35  tff(c_6, plain, (![A_5]: (k3_xboole_0(A_5, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.45/1.35  tff(c_276, plain, (![A_5]: (k3_xboole_0(A_5, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_274, c_274, c_6])).
% 2.45/1.35  tff(c_472, plain, (![A_69, B_70]: (k5_xboole_0(A_69, k3_xboole_0(A_69, B_70))=k4_xboole_0(A_69, B_70))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.45/1.35  tff(c_489, plain, (![A_5]: (k5_xboole_0(A_5, '#skF_2')=k4_xboole_0(A_5, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_276, c_472])).
% 2.45/1.35  tff(c_492, plain, (![A_5]: (k5_xboole_0(A_5, '#skF_2')=A_5)), inference(demodulation, [status(thm), theory('equality')], [c_275, c_489])).
% 2.45/1.35  tff(c_528, plain, (![A_5]: (k5_xboole_0(A_5, '#skF_3')=A_5)), inference(demodulation, [status(thm), theory('equality')], [c_506, c_492])).
% 2.45/1.35  tff(c_593, plain, (k2_xboole_0('#skF_3', '#skF_3')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_586, c_528])).
% 2.45/1.35  tff(c_518, plain, (k2_xboole_0('#skF_3', '#skF_3')=k1_tarski('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_506, c_36])).
% 2.45/1.35  tff(c_621, plain, (k1_tarski('#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_593, c_518])).
% 2.45/1.35  tff(c_623, plain, $false, inference(negUnitSimplification, [status(thm)], [c_273, c_621])).
% 2.45/1.35  tff(c_624, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_30])).
% 2.45/1.35  tff(c_625, plain, (k1_tarski('#skF_1')='#skF_2'), inference(splitRight, [status(thm)], [c_30])).
% 2.45/1.35  tff(c_34, plain, (k1_tarski('#skF_1')!='#skF_3' | k1_tarski('#skF_1')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.45/1.35  tff(c_668, plain, ('#skF_2'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_625, c_625, c_34])).
% 2.45/1.35  tff(c_669, plain, (![B_85, A_86]: (k2_xboole_0(B_85, A_86)=k2_xboole_0(A_86, B_85))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.45/1.35  tff(c_630, plain, (k2_xboole_0('#skF_2', '#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_625, c_36])).
% 2.45/1.35  tff(c_690, plain, (k2_xboole_0('#skF_3', '#skF_2')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_669, c_630])).
% 2.45/1.35  tff(c_723, plain, (r1_tarski('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_690, c_10])).
% 2.45/1.35  tff(c_904, plain, (![B_104, A_105]: (k1_tarski(B_104)=A_105 | k1_xboole_0=A_105 | ~r1_tarski(A_105, k1_tarski(B_104)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.45/1.35  tff(c_910, plain, (![A_105]: (k1_tarski('#skF_1')=A_105 | k1_xboole_0=A_105 | ~r1_tarski(A_105, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_625, c_904])).
% 2.45/1.35  tff(c_919, plain, (![A_106]: (A_106='#skF_2' | k1_xboole_0=A_106 | ~r1_tarski(A_106, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_625, c_910])).
% 2.45/1.35  tff(c_922, plain, ('#skF_2'='#skF_3' | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_723, c_919])).
% 2.45/1.35  tff(c_932, plain, $false, inference(negUnitSimplification, [status(thm)], [c_624, c_668, c_922])).
% 2.45/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.45/1.35  
% 2.45/1.35  Inference rules
% 2.45/1.35  ----------------------
% 2.45/1.35  #Ref     : 0
% 2.45/1.35  #Sup     : 220
% 2.45/1.35  #Fact    : 0
% 2.45/1.35  #Define  : 0
% 2.45/1.35  #Split   : 3
% 2.45/1.35  #Chain   : 0
% 2.45/1.35  #Close   : 0
% 2.45/1.35  
% 2.45/1.35  Ordering : KBO
% 2.45/1.35  
% 2.45/1.35  Simplification rules
% 2.45/1.35  ----------------------
% 2.45/1.35  #Subsume      : 9
% 2.45/1.35  #Demod        : 79
% 2.45/1.35  #Tautology    : 169
% 2.45/1.35  #SimpNegUnit  : 4
% 2.45/1.35  #BackRed      : 14
% 2.45/1.35  
% 2.45/1.35  #Partial instantiations: 0
% 2.45/1.35  #Strategies tried      : 1
% 2.45/1.35  
% 2.45/1.35  Timing (in seconds)
% 2.45/1.35  ----------------------
% 2.45/1.35  Preprocessing        : 0.28
% 2.45/1.36  Parsing              : 0.15
% 2.45/1.36  CNF conversion       : 0.02
% 2.45/1.36  Main loop            : 0.31
% 2.45/1.36  Inferencing          : 0.11
% 2.45/1.36  Reduction            : 0.11
% 2.45/1.36  Demodulation         : 0.08
% 2.45/1.36  BG Simplification    : 0.02
% 2.45/1.36  Subsumption          : 0.05
% 2.45/1.36  Abstraction          : 0.01
% 2.45/1.36  MUC search           : 0.00
% 2.45/1.36  Cooper               : 0.00
% 2.45/1.36  Total                : 0.63
% 2.45/1.36  Index Insertion      : 0.00
% 2.45/1.36  Index Deletion       : 0.00
% 2.45/1.36  Index Matching       : 0.00
% 2.45/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
