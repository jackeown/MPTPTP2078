%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:05 EST 2020

% Result     : Theorem 2.37s
% Output     : CNFRefutation 2.66s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 113 expanded)
%              Number of leaves         :   26 (  47 expanded)
%              Depth                    :    8
%              Number of atoms          :   72 ( 233 expanded)
%              Number of equality atoms :   59 ( 218 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(f_70,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k1_tarski(A) = k2_xboole_0(B,C)
          & ~ ( B = k1_tarski(A)
              & C = k1_tarski(A) )
          & ~ ( B = k1_xboole_0
              & C = k1_tarski(A) )
          & ~ ( B = k1_tarski(A)
              & C = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_33,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_29,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_27,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_51,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(c_30,plain,
    ( k1_tarski('#skF_1') != '#skF_3'
    | k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_57,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_28,plain,
    ( k1_xboole_0 != '#skF_3'
    | k1_tarski('#skF_1') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_52,plain,(
    k1_tarski('#skF_1') != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_34,plain,(
    k2_xboole_0('#skF_2','#skF_3') = k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_59,plain,(
    ! [A_25,B_26] : r1_tarski(A_25,k2_xboole_0(A_25,B_26)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_62,plain,(
    r1_tarski('#skF_2',k1_tarski('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_59])).

tff(c_398,plain,(
    ! [B_54,A_55] :
      ( k1_tarski(B_54) = A_55
      | k1_xboole_0 = A_55
      | ~ r1_tarski(A_55,k1_tarski(B_54)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_416,plain,
    ( k1_tarski('#skF_1') = '#skF_2'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_62,c_398])).

tff(c_426,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_57,c_52,c_416])).

tff(c_427,plain,(
    k1_tarski('#skF_1') != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_428,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_8,plain,(
    ! [A_6] : k5_xboole_0(A_6,k1_xboole_0) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_429,plain,(
    ! [A_6] : k5_xboole_0(A_6,'#skF_2') = A_6 ),
    inference(demodulation,[status(thm),theory(equality)],[c_428,c_8])).

tff(c_4,plain,(
    ! [A_3] : k3_xboole_0(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_430,plain,(
    ! [A_3] : k3_xboole_0(A_3,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_428,c_428,c_4])).

tff(c_548,plain,(
    ! [A_70,B_71] : k5_xboole_0(A_70,k3_xboole_0(A_70,B_71)) = k4_xboole_0(A_70,B_71) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_557,plain,(
    ! [A_3] : k5_xboole_0(A_3,'#skF_2') = k4_xboole_0(A_3,'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_430,c_548])).

tff(c_560,plain,(
    ! [A_3] : k4_xboole_0(A_3,'#skF_2') = A_3 ),
    inference(demodulation,[status(thm),theory(equality)],[c_429,c_557])).

tff(c_668,plain,(
    ! [A_80,B_81] : k2_xboole_0(k3_xboole_0(A_80,B_81),k4_xboole_0(A_80,B_81)) = A_80 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_686,plain,(
    ! [A_3] : k2_xboole_0('#skF_2',k4_xboole_0(A_3,'#skF_2')) = A_3 ),
    inference(superposition,[status(thm),theory(equality)],[c_430,c_668])).

tff(c_690,plain,(
    ! [A_3] : k2_xboole_0('#skF_2',A_3) = A_3 ),
    inference(demodulation,[status(thm),theory(equality)],[c_560,c_686])).

tff(c_691,plain,(
    k1_tarski('#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_690,c_34])).

tff(c_693,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_427,c_691])).

tff(c_694,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_695,plain,(
    k1_tarski('#skF_1') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_32,plain,
    ( k1_tarski('#skF_1') != '#skF_3'
    | k1_tarski('#skF_1') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_767,plain,(
    '#skF_2' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_695,c_695,c_32])).

tff(c_12,plain,(
    ! [B_10,A_9] : k2_tarski(B_10,A_9) = k2_tarski(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_768,plain,(
    ! [A_88,B_89] : k3_tarski(k2_tarski(A_88,B_89)) = k2_xboole_0(A_88,B_89) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_834,plain,(
    ! [B_94,A_95] : k3_tarski(k2_tarski(B_94,A_95)) = k2_xboole_0(A_95,B_94) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_768])).

tff(c_26,plain,(
    ! [A_19,B_20] : k3_tarski(k2_tarski(A_19,B_20)) = k2_xboole_0(A_19,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_860,plain,(
    ! [B_96,A_97] : k2_xboole_0(B_96,A_97) = k2_xboole_0(A_97,B_96) ),
    inference(superposition,[status(thm),theory(equality)],[c_834,c_26])).

tff(c_702,plain,(
    k2_xboole_0('#skF_2','#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_695,c_34])).

tff(c_881,plain,(
    k2_xboole_0('#skF_3','#skF_2') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_860,c_702])).

tff(c_10,plain,(
    ! [A_7,B_8] : r1_tarski(A_7,k2_xboole_0(A_7,B_8)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_914,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_881,c_10])).

tff(c_1074,plain,(
    ! [B_109,A_110] :
      ( k1_tarski(B_109) = A_110
      | k1_xboole_0 = A_110
      | ~ r1_tarski(A_110,k1_tarski(B_109)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1085,plain,(
    ! [A_110] :
      ( k1_tarski('#skF_1') = A_110
      | k1_xboole_0 = A_110
      | ~ r1_tarski(A_110,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_695,c_1074])).

tff(c_1094,plain,(
    ! [A_111] :
      ( A_111 = '#skF_2'
      | k1_xboole_0 = A_111
      | ~ r1_tarski(A_111,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_695,c_1085])).

tff(c_1105,plain,
    ( '#skF_2' = '#skF_3'
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_914,c_1094])).

tff(c_1117,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_694,c_767,c_1105])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:04:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.37/1.34  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.66/1.35  
% 2.66/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.66/1.35  %$ r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.66/1.35  
% 2.66/1.35  %Foreground sorts:
% 2.66/1.35  
% 2.66/1.35  
% 2.66/1.35  %Background operators:
% 2.66/1.35  
% 2.66/1.35  
% 2.66/1.35  %Foreground operators:
% 2.66/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.66/1.35  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.66/1.35  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.66/1.35  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.66/1.35  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.66/1.35  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.66/1.35  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.66/1.35  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.66/1.35  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.66/1.35  tff('#skF_2', type, '#skF_2': $i).
% 2.66/1.35  tff('#skF_3', type, '#skF_3': $i).
% 2.66/1.35  tff('#skF_1', type, '#skF_1': $i).
% 2.66/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.66/1.35  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.66/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.66/1.35  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.66/1.35  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.66/1.35  
% 2.66/1.36  tff(f_70, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~((B = k1_tarski(A)) & (C = k1_tarski(A)))) & ~((B = k1_xboole_0) & (C = k1_tarski(A)))) & ~((B = k1_tarski(A)) & (C = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_zfmisc_1)).
% 2.66/1.36  tff(f_35, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.66/1.36  tff(f_49, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 2.66/1.36  tff(f_33, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 2.66/1.36  tff(f_29, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 2.66/1.36  tff(f_27, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.66/1.36  tff(f_31, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_xboole_1)).
% 2.66/1.36  tff(f_37, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.66/1.36  tff(f_51, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 2.66/1.36  tff(c_30, plain, (k1_tarski('#skF_1')!='#skF_3' | k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.66/1.36  tff(c_57, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_30])).
% 2.66/1.36  tff(c_28, plain, (k1_xboole_0!='#skF_3' | k1_tarski('#skF_1')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.66/1.36  tff(c_52, plain, (k1_tarski('#skF_1')!='#skF_2'), inference(splitLeft, [status(thm)], [c_28])).
% 2.66/1.36  tff(c_34, plain, (k2_xboole_0('#skF_2', '#skF_3')=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.66/1.36  tff(c_59, plain, (![A_25, B_26]: (r1_tarski(A_25, k2_xboole_0(A_25, B_26)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.66/1.36  tff(c_62, plain, (r1_tarski('#skF_2', k1_tarski('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_34, c_59])).
% 2.66/1.36  tff(c_398, plain, (![B_54, A_55]: (k1_tarski(B_54)=A_55 | k1_xboole_0=A_55 | ~r1_tarski(A_55, k1_tarski(B_54)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.66/1.36  tff(c_416, plain, (k1_tarski('#skF_1')='#skF_2' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_62, c_398])).
% 2.66/1.36  tff(c_426, plain, $false, inference(negUnitSimplification, [status(thm)], [c_57, c_52, c_416])).
% 2.66/1.36  tff(c_427, plain, (k1_tarski('#skF_1')!='#skF_3'), inference(splitRight, [status(thm)], [c_30])).
% 2.66/1.36  tff(c_428, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_30])).
% 2.66/1.36  tff(c_8, plain, (![A_6]: (k5_xboole_0(A_6, k1_xboole_0)=A_6)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.66/1.36  tff(c_429, plain, (![A_6]: (k5_xboole_0(A_6, '#skF_2')=A_6)), inference(demodulation, [status(thm), theory('equality')], [c_428, c_8])).
% 2.66/1.36  tff(c_4, plain, (![A_3]: (k3_xboole_0(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.66/1.36  tff(c_430, plain, (![A_3]: (k3_xboole_0(A_3, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_428, c_428, c_4])).
% 2.66/1.36  tff(c_548, plain, (![A_70, B_71]: (k5_xboole_0(A_70, k3_xboole_0(A_70, B_71))=k4_xboole_0(A_70, B_71))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.66/1.36  tff(c_557, plain, (![A_3]: (k5_xboole_0(A_3, '#skF_2')=k4_xboole_0(A_3, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_430, c_548])).
% 2.66/1.36  tff(c_560, plain, (![A_3]: (k4_xboole_0(A_3, '#skF_2')=A_3)), inference(demodulation, [status(thm), theory('equality')], [c_429, c_557])).
% 2.66/1.36  tff(c_668, plain, (![A_80, B_81]: (k2_xboole_0(k3_xboole_0(A_80, B_81), k4_xboole_0(A_80, B_81))=A_80)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.66/1.36  tff(c_686, plain, (![A_3]: (k2_xboole_0('#skF_2', k4_xboole_0(A_3, '#skF_2'))=A_3)), inference(superposition, [status(thm), theory('equality')], [c_430, c_668])).
% 2.66/1.36  tff(c_690, plain, (![A_3]: (k2_xboole_0('#skF_2', A_3)=A_3)), inference(demodulation, [status(thm), theory('equality')], [c_560, c_686])).
% 2.66/1.36  tff(c_691, plain, (k1_tarski('#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_690, c_34])).
% 2.66/1.36  tff(c_693, plain, $false, inference(negUnitSimplification, [status(thm)], [c_427, c_691])).
% 2.66/1.36  tff(c_694, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_28])).
% 2.66/1.36  tff(c_695, plain, (k1_tarski('#skF_1')='#skF_2'), inference(splitRight, [status(thm)], [c_28])).
% 2.66/1.36  tff(c_32, plain, (k1_tarski('#skF_1')!='#skF_3' | k1_tarski('#skF_1')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.66/1.36  tff(c_767, plain, ('#skF_2'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_695, c_695, c_32])).
% 2.66/1.36  tff(c_12, plain, (![B_10, A_9]: (k2_tarski(B_10, A_9)=k2_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.66/1.36  tff(c_768, plain, (![A_88, B_89]: (k3_tarski(k2_tarski(A_88, B_89))=k2_xboole_0(A_88, B_89))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.66/1.36  tff(c_834, plain, (![B_94, A_95]: (k3_tarski(k2_tarski(B_94, A_95))=k2_xboole_0(A_95, B_94))), inference(superposition, [status(thm), theory('equality')], [c_12, c_768])).
% 2.66/1.36  tff(c_26, plain, (![A_19, B_20]: (k3_tarski(k2_tarski(A_19, B_20))=k2_xboole_0(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.66/1.36  tff(c_860, plain, (![B_96, A_97]: (k2_xboole_0(B_96, A_97)=k2_xboole_0(A_97, B_96))), inference(superposition, [status(thm), theory('equality')], [c_834, c_26])).
% 2.66/1.36  tff(c_702, plain, (k2_xboole_0('#skF_2', '#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_695, c_34])).
% 2.66/1.36  tff(c_881, plain, (k2_xboole_0('#skF_3', '#skF_2')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_860, c_702])).
% 2.66/1.36  tff(c_10, plain, (![A_7, B_8]: (r1_tarski(A_7, k2_xboole_0(A_7, B_8)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.66/1.36  tff(c_914, plain, (r1_tarski('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_881, c_10])).
% 2.66/1.36  tff(c_1074, plain, (![B_109, A_110]: (k1_tarski(B_109)=A_110 | k1_xboole_0=A_110 | ~r1_tarski(A_110, k1_tarski(B_109)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.66/1.36  tff(c_1085, plain, (![A_110]: (k1_tarski('#skF_1')=A_110 | k1_xboole_0=A_110 | ~r1_tarski(A_110, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_695, c_1074])).
% 2.66/1.36  tff(c_1094, plain, (![A_111]: (A_111='#skF_2' | k1_xboole_0=A_111 | ~r1_tarski(A_111, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_695, c_1085])).
% 2.66/1.36  tff(c_1105, plain, ('#skF_2'='#skF_3' | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_914, c_1094])).
% 2.66/1.36  tff(c_1117, plain, $false, inference(negUnitSimplification, [status(thm)], [c_694, c_767, c_1105])).
% 2.66/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.66/1.36  
% 2.66/1.36  Inference rules
% 2.66/1.36  ----------------------
% 2.66/1.36  #Ref     : 0
% 2.66/1.36  #Sup     : 261
% 2.66/1.36  #Fact    : 0
% 2.66/1.36  #Define  : 0
% 2.66/1.36  #Split   : 3
% 2.66/1.36  #Chain   : 0
% 2.66/1.36  #Close   : 0
% 2.66/1.36  
% 2.66/1.36  Ordering : KBO
% 2.66/1.36  
% 2.66/1.36  Simplification rules
% 2.66/1.36  ----------------------
% 2.66/1.36  #Subsume      : 6
% 2.66/1.36  #Demod        : 79
% 2.66/1.36  #Tautology    : 200
% 2.66/1.36  #SimpNegUnit  : 5
% 2.66/1.36  #BackRed      : 5
% 2.66/1.36  
% 2.66/1.36  #Partial instantiations: 0
% 2.66/1.36  #Strategies tried      : 1
% 2.66/1.36  
% 2.66/1.36  Timing (in seconds)
% 2.66/1.36  ----------------------
% 2.73/1.36  Preprocessing        : 0.29
% 2.73/1.36  Parsing              : 0.16
% 2.73/1.36  CNF conversion       : 0.02
% 2.73/1.36  Main loop            : 0.32
% 2.73/1.37  Inferencing          : 0.12
% 2.73/1.37  Reduction            : 0.11
% 2.73/1.37  Demodulation         : 0.08
% 2.73/1.37  BG Simplification    : 0.02
% 2.73/1.37  Subsumption          : 0.04
% 2.73/1.37  Abstraction          : 0.01
% 2.73/1.37  MUC search           : 0.00
% 2.73/1.37  Cooper               : 0.00
% 2.73/1.37  Total                : 0.64
% 2.73/1.37  Index Insertion      : 0.00
% 2.73/1.37  Index Deletion       : 0.00
% 2.73/1.37  Index Matching       : 0.00
% 2.73/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
