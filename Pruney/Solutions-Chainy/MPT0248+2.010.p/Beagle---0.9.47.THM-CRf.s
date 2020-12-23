%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:05 EST 2020

% Result     : Theorem 2.64s
% Output     : CNFRefutation 2.64s
% Verified   : 
% Statistics : Number of formulae       :   62 (  99 expanded)
%              Number of leaves         :   21 (  41 expanded)
%              Depth                    :    7
%              Number of atoms          :   75 ( 202 expanded)
%              Number of equality atoms :   65 ( 189 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k1_enumset1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_66,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k1_tarski(A) = k2_xboole_0(B,C)
          & ~ ( B = k1_tarski(A)
              & C = k1_tarski(A) )
          & ~ ( B = k1_xboole_0
              & C = k1_tarski(A) )
          & ~ ( B = k1_tarski(A)
              & C = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_31,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_35,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_47,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(c_26,plain,
    ( k1_tarski('#skF_1') != '#skF_3'
    | k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_42,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_26])).

tff(c_24,plain,
    ( k1_xboole_0 != '#skF_3'
    | k1_tarski('#skF_1') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_41,plain,(
    k1_tarski('#skF_1') != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_24])).

tff(c_30,plain,(
    k2_xboole_0('#skF_2','#skF_3') = k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_90,plain,(
    ! [A_21,B_22] : k4_xboole_0(A_21,k2_xboole_0(A_21,B_22)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_97,plain,(
    k4_xboole_0('#skF_2',k1_tarski('#skF_1')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_90])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,B_2)
      | k4_xboole_0(A_1,B_2) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_326,plain,(
    ! [B_40,A_41] :
      ( k1_tarski(B_40) = A_41
      | k1_xboole_0 = A_41
      | ~ r1_tarski(A_41,k1_tarski(B_40)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_443,plain,(
    ! [B_45,A_46] :
      ( k1_tarski(B_45) = A_46
      | k1_xboole_0 = A_46
      | k4_xboole_0(A_46,k1_tarski(B_45)) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_2,c_326])).

tff(c_453,plain,
    ( k1_tarski('#skF_1') = '#skF_2'
    | k1_xboole_0 = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_97,c_443])).

tff(c_464,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_41,c_453])).

tff(c_465,plain,(
    k1_tarski('#skF_1') != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_466,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_6,plain,(
    ! [A_3] : k2_xboole_0(A_3,k1_xboole_0) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_471,plain,(
    ! [A_3] : k2_xboole_0(A_3,'#skF_2') = A_3 ),
    inference(demodulation,[status(thm),theory(equality)],[c_466,c_6])).

tff(c_10,plain,(
    ! [B_7,A_6] : k2_tarski(B_7,A_6) = k2_tarski(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_589,plain,(
    ! [A_63,B_64] : k3_tarski(k2_tarski(A_63,B_64)) = k2_xboole_0(A_63,B_64) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_638,plain,(
    ! [B_67,A_68] : k3_tarski(k2_tarski(B_67,A_68)) = k2_xboole_0(A_68,B_67) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_589])).

tff(c_22,plain,(
    ! [A_13,B_14] : k3_tarski(k2_tarski(A_13,B_14)) = k2_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_681,plain,(
    ! [B_71,A_72] : k2_xboole_0(B_71,A_72) = k2_xboole_0(A_72,B_71) ),
    inference(superposition,[status(thm),theory(equality)],[c_638,c_22])).

tff(c_710,plain,(
    k2_xboole_0('#skF_3','#skF_2') = k1_tarski('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_681,c_30])).

tff(c_742,plain,(
    k1_tarski('#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_471,c_710])).

tff(c_744,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_465,c_742])).

tff(c_745,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_746,plain,(
    k1_tarski('#skF_1') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_28,plain,
    ( k1_tarski('#skF_1') != '#skF_3'
    | k1_tarski('#skF_1') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_779,plain,(
    '#skF_2' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_746,c_746,c_28])).

tff(c_877,plain,(
    ! [A_85,B_86] : k3_tarski(k2_tarski(A_85,B_86)) = k2_xboole_0(A_85,B_86) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_953,plain,(
    ! [B_91,A_92] : k3_tarski(k2_tarski(B_91,A_92)) = k2_xboole_0(A_92,B_91) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_877])).

tff(c_979,plain,(
    ! [B_93,A_94] : k2_xboole_0(B_93,A_94) = k2_xboole_0(A_94,B_93) ),
    inference(superposition,[status(thm),theory(equality)],[c_953,c_22])).

tff(c_753,plain,(
    k2_xboole_0('#skF_2','#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_746,c_30])).

tff(c_1000,plain,(
    k2_xboole_0('#skF_3','#skF_2') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_979,c_753])).

tff(c_8,plain,(
    ! [A_4,B_5] : k4_xboole_0(A_4,k2_xboole_0(A_4,B_5)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1047,plain,(
    k4_xboole_0('#skF_3','#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1000,c_8])).

tff(c_1096,plain,(
    ! [B_96,A_97] :
      ( k1_tarski(B_96) = A_97
      | k1_xboole_0 = A_97
      | ~ r1_tarski(A_97,k1_tarski(B_96)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1106,plain,(
    ! [A_97] :
      ( k1_tarski('#skF_1') = A_97
      | k1_xboole_0 = A_97
      | ~ r1_tarski(A_97,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_746,c_1096])).

tff(c_1154,plain,(
    ! [A_99] :
      ( A_99 = '#skF_2'
      | k1_xboole_0 = A_99
      | ~ r1_tarski(A_99,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_746,c_1106])).

tff(c_1231,plain,(
    ! [A_102] :
      ( A_102 = '#skF_2'
      | k1_xboole_0 = A_102
      | k4_xboole_0(A_102,'#skF_2') != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_2,c_1154])).

tff(c_1238,plain,
    ( '#skF_2' = '#skF_3'
    | k1_xboole_0 = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_1047,c_1231])).

tff(c_1250,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_745,c_779,c_1238])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:41:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.64/1.43  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.64/1.43  
% 2.64/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.64/1.43  %$ r1_tarski > k1_enumset1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.64/1.43  
% 2.64/1.43  %Foreground sorts:
% 2.64/1.43  
% 2.64/1.43  
% 2.64/1.43  %Background operators:
% 2.64/1.43  
% 2.64/1.43  
% 2.64/1.43  %Foreground operators:
% 2.64/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.64/1.43  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.64/1.43  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.64/1.43  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.64/1.43  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.64/1.43  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.64/1.43  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.64/1.43  tff('#skF_2', type, '#skF_2': $i).
% 2.64/1.43  tff('#skF_3', type, '#skF_3': $i).
% 2.64/1.43  tff('#skF_1', type, '#skF_1': $i).
% 2.64/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.64/1.43  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.64/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.64/1.43  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.64/1.43  
% 2.64/1.45  tff(f_66, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~((B = k1_tarski(A)) & (C = k1_tarski(A)))) & ~((B = k1_xboole_0) & (C = k1_tarski(A)))) & ~((B = k1_tarski(A)) & (C = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_zfmisc_1)).
% 2.64/1.45  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 2.64/1.45  tff(f_29, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.64/1.45  tff(f_45, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 2.64/1.45  tff(f_31, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 2.64/1.45  tff(f_35, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.64/1.45  tff(f_47, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 2.64/1.45  tff(c_26, plain, (k1_tarski('#skF_1')!='#skF_3' | k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.64/1.45  tff(c_42, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_26])).
% 2.64/1.45  tff(c_24, plain, (k1_xboole_0!='#skF_3' | k1_tarski('#skF_1')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.64/1.45  tff(c_41, plain, (k1_tarski('#skF_1')!='#skF_2'), inference(splitLeft, [status(thm)], [c_24])).
% 2.64/1.45  tff(c_30, plain, (k2_xboole_0('#skF_2', '#skF_3')=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.64/1.45  tff(c_90, plain, (![A_21, B_22]: (k4_xboole_0(A_21, k2_xboole_0(A_21, B_22))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.64/1.45  tff(c_97, plain, (k4_xboole_0('#skF_2', k1_tarski('#skF_1'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_30, c_90])).
% 2.64/1.45  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(A_1, B_2) | k4_xboole_0(A_1, B_2)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.64/1.45  tff(c_326, plain, (![B_40, A_41]: (k1_tarski(B_40)=A_41 | k1_xboole_0=A_41 | ~r1_tarski(A_41, k1_tarski(B_40)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.64/1.45  tff(c_443, plain, (![B_45, A_46]: (k1_tarski(B_45)=A_46 | k1_xboole_0=A_46 | k4_xboole_0(A_46, k1_tarski(B_45))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_326])).
% 2.64/1.45  tff(c_453, plain, (k1_tarski('#skF_1')='#skF_2' | k1_xboole_0='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_97, c_443])).
% 2.64/1.45  tff(c_464, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_41, c_453])).
% 2.64/1.45  tff(c_465, plain, (k1_tarski('#skF_1')!='#skF_3'), inference(splitRight, [status(thm)], [c_26])).
% 2.64/1.45  tff(c_466, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_26])).
% 2.64/1.45  tff(c_6, plain, (![A_3]: (k2_xboole_0(A_3, k1_xboole_0)=A_3)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.64/1.45  tff(c_471, plain, (![A_3]: (k2_xboole_0(A_3, '#skF_2')=A_3)), inference(demodulation, [status(thm), theory('equality')], [c_466, c_6])).
% 2.64/1.45  tff(c_10, plain, (![B_7, A_6]: (k2_tarski(B_7, A_6)=k2_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.64/1.45  tff(c_589, plain, (![A_63, B_64]: (k3_tarski(k2_tarski(A_63, B_64))=k2_xboole_0(A_63, B_64))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.64/1.45  tff(c_638, plain, (![B_67, A_68]: (k3_tarski(k2_tarski(B_67, A_68))=k2_xboole_0(A_68, B_67))), inference(superposition, [status(thm), theory('equality')], [c_10, c_589])).
% 2.64/1.45  tff(c_22, plain, (![A_13, B_14]: (k3_tarski(k2_tarski(A_13, B_14))=k2_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.64/1.45  tff(c_681, plain, (![B_71, A_72]: (k2_xboole_0(B_71, A_72)=k2_xboole_0(A_72, B_71))), inference(superposition, [status(thm), theory('equality')], [c_638, c_22])).
% 2.64/1.45  tff(c_710, plain, (k2_xboole_0('#skF_3', '#skF_2')=k1_tarski('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_681, c_30])).
% 2.64/1.45  tff(c_742, plain, (k1_tarski('#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_471, c_710])).
% 2.64/1.45  tff(c_744, plain, $false, inference(negUnitSimplification, [status(thm)], [c_465, c_742])).
% 2.64/1.45  tff(c_745, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_24])).
% 2.64/1.45  tff(c_746, plain, (k1_tarski('#skF_1')='#skF_2'), inference(splitRight, [status(thm)], [c_24])).
% 2.64/1.45  tff(c_28, plain, (k1_tarski('#skF_1')!='#skF_3' | k1_tarski('#skF_1')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.64/1.45  tff(c_779, plain, ('#skF_2'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_746, c_746, c_28])).
% 2.64/1.45  tff(c_877, plain, (![A_85, B_86]: (k3_tarski(k2_tarski(A_85, B_86))=k2_xboole_0(A_85, B_86))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.64/1.45  tff(c_953, plain, (![B_91, A_92]: (k3_tarski(k2_tarski(B_91, A_92))=k2_xboole_0(A_92, B_91))), inference(superposition, [status(thm), theory('equality')], [c_10, c_877])).
% 2.64/1.45  tff(c_979, plain, (![B_93, A_94]: (k2_xboole_0(B_93, A_94)=k2_xboole_0(A_94, B_93))), inference(superposition, [status(thm), theory('equality')], [c_953, c_22])).
% 2.64/1.45  tff(c_753, plain, (k2_xboole_0('#skF_2', '#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_746, c_30])).
% 2.64/1.45  tff(c_1000, plain, (k2_xboole_0('#skF_3', '#skF_2')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_979, c_753])).
% 2.64/1.45  tff(c_8, plain, (![A_4, B_5]: (k4_xboole_0(A_4, k2_xboole_0(A_4, B_5))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.64/1.45  tff(c_1047, plain, (k4_xboole_0('#skF_3', '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_1000, c_8])).
% 2.64/1.45  tff(c_1096, plain, (![B_96, A_97]: (k1_tarski(B_96)=A_97 | k1_xboole_0=A_97 | ~r1_tarski(A_97, k1_tarski(B_96)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.64/1.45  tff(c_1106, plain, (![A_97]: (k1_tarski('#skF_1')=A_97 | k1_xboole_0=A_97 | ~r1_tarski(A_97, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_746, c_1096])).
% 2.64/1.45  tff(c_1154, plain, (![A_99]: (A_99='#skF_2' | k1_xboole_0=A_99 | ~r1_tarski(A_99, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_746, c_1106])).
% 2.64/1.45  tff(c_1231, plain, (![A_102]: (A_102='#skF_2' | k1_xboole_0=A_102 | k4_xboole_0(A_102, '#skF_2')!=k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_1154])).
% 2.64/1.45  tff(c_1238, plain, ('#skF_2'='#skF_3' | k1_xboole_0='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_1047, c_1231])).
% 2.64/1.45  tff(c_1250, plain, $false, inference(negUnitSimplification, [status(thm)], [c_745, c_779, c_1238])).
% 2.64/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.64/1.45  
% 2.64/1.45  Inference rules
% 2.64/1.45  ----------------------
% 2.64/1.45  #Ref     : 0
% 2.64/1.45  #Sup     : 309
% 2.64/1.45  #Fact    : 0
% 2.64/1.45  #Define  : 0
% 2.64/1.45  #Split   : 3
% 2.64/1.45  #Chain   : 0
% 2.64/1.45  #Close   : 0
% 2.64/1.45  
% 2.64/1.45  Ordering : KBO
% 2.64/1.45  
% 2.64/1.45  Simplification rules
% 2.64/1.45  ----------------------
% 2.64/1.45  #Subsume      : 7
% 2.64/1.45  #Demod        : 74
% 2.64/1.45  #Tautology    : 247
% 2.64/1.45  #SimpNegUnit  : 6
% 2.64/1.45  #BackRed      : 2
% 2.64/1.45  
% 2.64/1.45  #Partial instantiations: 0
% 2.64/1.45  #Strategies tried      : 1
% 2.64/1.45  
% 2.64/1.45  Timing (in seconds)
% 2.64/1.45  ----------------------
% 2.64/1.45  Preprocessing        : 0.30
% 2.64/1.45  Parsing              : 0.16
% 2.64/1.45  CNF conversion       : 0.02
% 2.64/1.45  Main loop            : 0.36
% 2.64/1.45  Inferencing          : 0.14
% 2.64/1.45  Reduction            : 0.12
% 2.64/1.45  Demodulation         : 0.09
% 2.64/1.45  BG Simplification    : 0.02
% 2.64/1.45  Subsumption          : 0.05
% 2.64/1.45  Abstraction          : 0.02
% 2.64/1.45  MUC search           : 0.00
% 2.64/1.45  Cooper               : 0.00
% 2.64/1.45  Total                : 0.69
% 2.64/1.45  Index Insertion      : 0.00
% 2.64/1.45  Index Deletion       : 0.00
% 2.64/1.45  Index Matching       : 0.00
% 2.64/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
