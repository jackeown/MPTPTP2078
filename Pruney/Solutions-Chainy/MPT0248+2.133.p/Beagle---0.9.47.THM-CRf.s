%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:22 EST 2020

% Result     : Theorem 2.45s
% Output     : CNFRefutation 2.45s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 117 expanded)
%              Number of leaves         :   26 (  50 expanded)
%              Depth                    :    9
%              Number of atoms          :   87 ( 240 expanded)
%              Number of equality atoms :   55 ( 195 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_80,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k1_tarski(A) = k2_xboole_0(B,C)
          & ~ ( B = k1_tarski(A)
              & C = k1_tarski(A) )
          & ~ ( B = k1_xboole_0
              & C = k1_tarski(A) )
          & ~ ( B = k1_tarski(A)
              & C = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

tff(c_36,plain,
    ( k1_tarski('#skF_1') != '#skF_3'
    | k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_66,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_34,plain,
    ( k1_xboole_0 != '#skF_3'
    | k1_tarski('#skF_1') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_57,plain,(
    k1_tarski('#skF_1') != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_40,plain,(
    k2_xboole_0('#skF_2','#skF_3') = k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_10,plain,(
    ! [A_10,B_11] : r1_tarski(A_10,k2_xboole_0(A_10,B_11)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_62,plain,(
    r1_tarski('#skF_2',k1_tarski('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_10])).

tff(c_257,plain,(
    ! [B_72,A_73] :
      ( k1_tarski(B_72) = A_73
      | k1_xboole_0 = A_73
      | ~ r1_tarski(A_73,k1_tarski(B_72)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_263,plain,
    ( k1_tarski('#skF_1') = '#skF_2'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_62,c_257])).

tff(c_279,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_57,c_263])).

tff(c_280,plain,(
    k1_tarski('#skF_1') != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_52,plain,(
    ! [A_48,B_49] : r1_tarski(k3_xboole_0(A_48,B_49),A_48) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_55,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_52])).

tff(c_298,plain,(
    ! [A_76,B_77] :
      ( k2_xboole_0(A_76,B_77) = B_77
      | ~ r1_tarski(A_76,B_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_312,plain,(
    ! [A_1] : k2_xboole_0(A_1,A_1) = A_1 ),
    inference(resolution,[status(thm)],[c_55,c_298])).

tff(c_380,plain,(
    ! [A_86,C_87,B_88] :
      ( r1_tarski(A_86,k2_xboole_0(C_87,B_88))
      | ~ r1_tarski(A_86,B_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_395,plain,(
    ! [A_86] :
      ( r1_tarski(A_86,k1_tarski('#skF_1'))
      | ~ r1_tarski(A_86,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_380])).

tff(c_281,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_26,plain,(
    ! [B_41,A_40] :
      ( k1_tarski(B_41) = A_40
      | k1_xboole_0 = A_40
      | ~ r1_tarski(A_40,k1_tarski(B_41)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_452,plain,(
    ! [B_93,A_94] :
      ( k1_tarski(B_93) = A_94
      | A_94 = '#skF_2'
      | ~ r1_tarski(A_94,k1_tarski(B_93)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_281,c_26])).

tff(c_473,plain,(
    ! [A_95] :
      ( k1_tarski('#skF_1') = A_95
      | A_95 = '#skF_2'
      | ~ r1_tarski(A_95,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_395,c_452])).

tff(c_477,plain,
    ( k1_tarski('#skF_1') = '#skF_3'
    | '#skF_2' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_55,c_473])).

tff(c_484,plain,(
    '#skF_2' = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_280,c_477])).

tff(c_500,plain,(
    k2_xboole_0('#skF_3','#skF_3') = k1_tarski('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_484,c_40])).

tff(c_502,plain,(
    k1_tarski('#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_312,c_500])).

tff(c_504,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_280,c_502])).

tff(c_505,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_506,plain,(
    k1_tarski('#skF_1') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_38,plain,
    ( k1_tarski('#skF_1') != '#skF_3'
    | k1_tarski('#skF_1') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_535,plain,(
    '#skF_2' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_506,c_506,c_38])).

tff(c_513,plain,(
    k2_xboole_0('#skF_2','#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_506,c_40])).

tff(c_648,plain,(
    ! [A_109,C_110,B_111] :
      ( r1_tarski(A_109,k2_xboole_0(C_110,B_111))
      | ~ r1_tarski(A_109,B_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_703,plain,(
    ! [A_115] :
      ( r1_tarski(A_115,'#skF_2')
      | ~ r1_tarski(A_115,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_513,c_648])).

tff(c_6,plain,(
    ! [A_6,B_7] :
      ( k2_xboole_0(A_6,B_7) = B_7
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_729,plain,(
    ! [A_117] :
      ( k2_xboole_0(A_117,'#skF_2') = '#skF_2'
      | ~ r1_tarski(A_117,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_703,c_6])).

tff(c_738,plain,(
    k2_xboole_0('#skF_3','#skF_2') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_55,c_729])).

tff(c_746,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_738,c_10])).

tff(c_755,plain,(
    ! [B_118,A_119] :
      ( k1_tarski(B_118) = A_119
      | k1_xboole_0 = A_119
      | ~ r1_tarski(A_119,k1_tarski(B_118)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_758,plain,(
    ! [A_119] :
      ( k1_tarski('#skF_1') = A_119
      | k1_xboole_0 = A_119
      | ~ r1_tarski(A_119,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_506,c_755])).

tff(c_805,plain,(
    ! [A_122] :
      ( A_122 = '#skF_2'
      | k1_xboole_0 = A_122
      | ~ r1_tarski(A_122,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_506,c_758])).

tff(c_811,plain,
    ( '#skF_2' = '#skF_3'
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_746,c_805])).

tff(c_830,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_505,c_535,c_811])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.15  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.36  % Computer   : n022.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % DateTime   : Tue Dec  1 13:33:40 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.15/0.37  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.45/1.36  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.45/1.37  
% 2.45/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.45/1.37  %$ r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.45/1.37  
% 2.45/1.37  %Foreground sorts:
% 2.45/1.37  
% 2.45/1.37  
% 2.45/1.37  %Background operators:
% 2.45/1.37  
% 2.45/1.37  
% 2.45/1.37  %Foreground operators:
% 2.45/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.45/1.37  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.45/1.37  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.45/1.37  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.45/1.37  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.45/1.37  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.45/1.37  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.45/1.37  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.45/1.37  tff('#skF_2', type, '#skF_2': $i).
% 2.45/1.37  tff('#skF_3', type, '#skF_3': $i).
% 2.45/1.37  tff('#skF_1', type, '#skF_1': $i).
% 2.45/1.37  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.45/1.37  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.45/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.45/1.37  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.45/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.45/1.37  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.45/1.37  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.45/1.37  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.45/1.37  
% 2.45/1.38  tff(f_80, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~((B = k1_tarski(A)) & (C = k1_tarski(A)))) & ~((B = k1_xboole_0) & (C = k1_tarski(A)))) & ~((B = k1_tarski(A)) & (C = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_zfmisc_1)).
% 2.45/1.38  tff(f_39, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.45/1.38  tff(f_59, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 2.45/1.38  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 2.45/1.38  tff(f_37, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 2.45/1.38  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.45/1.38  tff(f_31, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_xboole_1)).
% 2.45/1.38  tff(c_36, plain, (k1_tarski('#skF_1')!='#skF_3' | k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.45/1.38  tff(c_66, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_36])).
% 2.45/1.38  tff(c_34, plain, (k1_xboole_0!='#skF_3' | k1_tarski('#skF_1')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.45/1.38  tff(c_57, plain, (k1_tarski('#skF_1')!='#skF_2'), inference(splitLeft, [status(thm)], [c_34])).
% 2.45/1.38  tff(c_40, plain, (k2_xboole_0('#skF_2', '#skF_3')=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.45/1.38  tff(c_10, plain, (![A_10, B_11]: (r1_tarski(A_10, k2_xboole_0(A_10, B_11)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.45/1.38  tff(c_62, plain, (r1_tarski('#skF_2', k1_tarski('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_40, c_10])).
% 2.45/1.38  tff(c_257, plain, (![B_72, A_73]: (k1_tarski(B_72)=A_73 | k1_xboole_0=A_73 | ~r1_tarski(A_73, k1_tarski(B_72)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.45/1.38  tff(c_263, plain, (k1_tarski('#skF_1')='#skF_2' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_62, c_257])).
% 2.45/1.38  tff(c_279, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_57, c_263])).
% 2.45/1.38  tff(c_280, plain, (k1_tarski('#skF_1')!='#skF_3'), inference(splitRight, [status(thm)], [c_36])).
% 2.45/1.38  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.45/1.38  tff(c_52, plain, (![A_48, B_49]: (r1_tarski(k3_xboole_0(A_48, B_49), A_48))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.45/1.38  tff(c_55, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_52])).
% 2.45/1.38  tff(c_298, plain, (![A_76, B_77]: (k2_xboole_0(A_76, B_77)=B_77 | ~r1_tarski(A_76, B_77))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.45/1.38  tff(c_312, plain, (![A_1]: (k2_xboole_0(A_1, A_1)=A_1)), inference(resolution, [status(thm)], [c_55, c_298])).
% 2.45/1.38  tff(c_380, plain, (![A_86, C_87, B_88]: (r1_tarski(A_86, k2_xboole_0(C_87, B_88)) | ~r1_tarski(A_86, B_88))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.45/1.38  tff(c_395, plain, (![A_86]: (r1_tarski(A_86, k1_tarski('#skF_1')) | ~r1_tarski(A_86, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_40, c_380])).
% 2.45/1.38  tff(c_281, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_36])).
% 2.45/1.38  tff(c_26, plain, (![B_41, A_40]: (k1_tarski(B_41)=A_40 | k1_xboole_0=A_40 | ~r1_tarski(A_40, k1_tarski(B_41)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.45/1.38  tff(c_452, plain, (![B_93, A_94]: (k1_tarski(B_93)=A_94 | A_94='#skF_2' | ~r1_tarski(A_94, k1_tarski(B_93)))), inference(demodulation, [status(thm), theory('equality')], [c_281, c_26])).
% 2.45/1.38  tff(c_473, plain, (![A_95]: (k1_tarski('#skF_1')=A_95 | A_95='#skF_2' | ~r1_tarski(A_95, '#skF_3'))), inference(resolution, [status(thm)], [c_395, c_452])).
% 2.45/1.38  tff(c_477, plain, (k1_tarski('#skF_1')='#skF_3' | '#skF_2'='#skF_3'), inference(resolution, [status(thm)], [c_55, c_473])).
% 2.45/1.38  tff(c_484, plain, ('#skF_2'='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_280, c_477])).
% 2.45/1.38  tff(c_500, plain, (k2_xboole_0('#skF_3', '#skF_3')=k1_tarski('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_484, c_40])).
% 2.45/1.38  tff(c_502, plain, (k1_tarski('#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_312, c_500])).
% 2.45/1.38  tff(c_504, plain, $false, inference(negUnitSimplification, [status(thm)], [c_280, c_502])).
% 2.45/1.38  tff(c_505, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_34])).
% 2.45/1.38  tff(c_506, plain, (k1_tarski('#skF_1')='#skF_2'), inference(splitRight, [status(thm)], [c_34])).
% 2.45/1.38  tff(c_38, plain, (k1_tarski('#skF_1')!='#skF_3' | k1_tarski('#skF_1')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.45/1.38  tff(c_535, plain, ('#skF_2'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_506, c_506, c_38])).
% 2.45/1.38  tff(c_513, plain, (k2_xboole_0('#skF_2', '#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_506, c_40])).
% 2.45/1.38  tff(c_648, plain, (![A_109, C_110, B_111]: (r1_tarski(A_109, k2_xboole_0(C_110, B_111)) | ~r1_tarski(A_109, B_111))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.45/1.38  tff(c_703, plain, (![A_115]: (r1_tarski(A_115, '#skF_2') | ~r1_tarski(A_115, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_513, c_648])).
% 2.45/1.38  tff(c_6, plain, (![A_6, B_7]: (k2_xboole_0(A_6, B_7)=B_7 | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.45/1.38  tff(c_729, plain, (![A_117]: (k2_xboole_0(A_117, '#skF_2')='#skF_2' | ~r1_tarski(A_117, '#skF_3'))), inference(resolution, [status(thm)], [c_703, c_6])).
% 2.45/1.38  tff(c_738, plain, (k2_xboole_0('#skF_3', '#skF_2')='#skF_2'), inference(resolution, [status(thm)], [c_55, c_729])).
% 2.45/1.38  tff(c_746, plain, (r1_tarski('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_738, c_10])).
% 2.45/1.38  tff(c_755, plain, (![B_118, A_119]: (k1_tarski(B_118)=A_119 | k1_xboole_0=A_119 | ~r1_tarski(A_119, k1_tarski(B_118)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.45/1.38  tff(c_758, plain, (![A_119]: (k1_tarski('#skF_1')=A_119 | k1_xboole_0=A_119 | ~r1_tarski(A_119, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_506, c_755])).
% 2.45/1.38  tff(c_805, plain, (![A_122]: (A_122='#skF_2' | k1_xboole_0=A_122 | ~r1_tarski(A_122, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_506, c_758])).
% 2.45/1.38  tff(c_811, plain, ('#skF_2'='#skF_3' | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_746, c_805])).
% 2.45/1.38  tff(c_830, plain, $false, inference(negUnitSimplification, [status(thm)], [c_505, c_535, c_811])).
% 2.45/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.45/1.38  
% 2.45/1.38  Inference rules
% 2.45/1.38  ----------------------
% 2.45/1.38  #Ref     : 0
% 2.45/1.38  #Sup     : 188
% 2.45/1.38  #Fact    : 0
% 2.45/1.38  #Define  : 0
% 2.45/1.38  #Split   : 3
% 2.45/1.38  #Chain   : 0
% 2.45/1.38  #Close   : 0
% 2.45/1.38  
% 2.45/1.38  Ordering : KBO
% 2.45/1.38  
% 2.45/1.38  Simplification rules
% 2.45/1.38  ----------------------
% 2.45/1.38  #Subsume      : 2
% 2.45/1.38  #Demod        : 81
% 2.45/1.38  #Tautology    : 139
% 2.45/1.38  #SimpNegUnit  : 4
% 2.45/1.38  #BackRed      : 12
% 2.45/1.38  
% 2.45/1.38  #Partial instantiations: 0
% 2.45/1.38  #Strategies tried      : 1
% 2.45/1.38  
% 2.45/1.38  Timing (in seconds)
% 2.45/1.38  ----------------------
% 2.45/1.39  Preprocessing        : 0.31
% 2.45/1.39  Parsing              : 0.17
% 2.45/1.39  CNF conversion       : 0.02
% 2.45/1.39  Main loop            : 0.29
% 2.45/1.39  Inferencing          : 0.11
% 2.45/1.39  Reduction            : 0.09
% 2.45/1.39  Demodulation         : 0.07
% 2.45/1.39  BG Simplification    : 0.02
% 2.45/1.39  Subsumption          : 0.04
% 2.45/1.39  Abstraction          : 0.02
% 2.45/1.39  MUC search           : 0.00
% 2.45/1.39  Cooper               : 0.00
% 2.45/1.39  Total                : 0.63
% 2.45/1.39  Index Insertion      : 0.00
% 2.45/1.39  Index Deletion       : 0.00
% 2.45/1.39  Index Matching       : 0.00
% 2.45/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
