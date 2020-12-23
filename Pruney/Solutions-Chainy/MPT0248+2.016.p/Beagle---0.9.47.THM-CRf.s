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
% DateTime   : Thu Dec  3 09:50:06 EST 2020

% Result     : Theorem 2.48s
% Output     : CNFRefutation 2.72s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 103 expanded)
%              Number of leaves         :   21 (  42 expanded)
%              Depth                    :    7
%              Number of atoms          :   69 ( 205 expanded)
%              Number of equality atoms :   56 ( 190 expanded)
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

tff(f_64,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k1_tarski(A) = k2_xboole_0(B,C)
          & ~ ( B = k1_tarski(A)
              & C = k1_tarski(A) )
          & ~ ( B = k1_xboole_0
              & C = k1_tarski(A) )
          & ~ ( B = k1_tarski(A)
              & C = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_27,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_45,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(c_24,plain,
    ( k1_tarski('#skF_1') != '#skF_3'
    | k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_40,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_24])).

tff(c_22,plain,
    ( k1_xboole_0 != '#skF_3'
    | k1_tarski('#skF_1') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_39,plain,(
    k1_tarski('#skF_1') != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_22])).

tff(c_28,plain,(
    k2_xboole_0('#skF_2','#skF_3') = k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_46,plain,(
    ! [A_18,B_19] : r1_tarski(A_18,k2_xboole_0(A_18,B_19)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_49,plain,(
    r1_tarski('#skF_2',k1_tarski('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_46])).

tff(c_376,plain,(
    ! [B_41,A_42] :
      ( k1_tarski(B_41) = A_42
      | k1_xboole_0 = A_42
      | ~ r1_tarski(A_42,k1_tarski(B_41)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_390,plain,
    ( k1_tarski('#skF_1') = '#skF_2'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_49,c_376])).

tff(c_399,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_39,c_390])).

tff(c_400,plain,(
    k1_tarski('#skF_1') != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_401,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_2,plain,(
    ! [A_1] : k4_xboole_0(A_1,k1_xboole_0) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_402,plain,(
    ! [A_1] : k4_xboole_0(A_1,'#skF_2') = A_1 ),
    inference(demodulation,[status(thm),theory(equality)],[c_401,c_2])).

tff(c_517,plain,(
    ! [A_56,B_57] : k4_xboole_0(k2_xboole_0(A_56,B_57),B_57) = k4_xboole_0(A_56,B_57) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_524,plain,(
    ! [A_56] : k4_xboole_0(A_56,'#skF_2') = k2_xboole_0(A_56,'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_517,c_402])).

tff(c_539,plain,(
    ! [A_56] : k2_xboole_0(A_56,'#skF_2') = A_56 ),
    inference(demodulation,[status(thm),theory(equality)],[c_402,c_524])).

tff(c_8,plain,(
    ! [B_7,A_6] : k2_tarski(B_7,A_6) = k2_tarski(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_479,plain,(
    ! [A_53,B_54] : k3_tarski(k2_tarski(A_53,B_54)) = k2_xboole_0(A_53,B_54) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_583,plain,(
    ! [B_63,A_64] : k3_tarski(k2_tarski(B_63,A_64)) = k2_xboole_0(A_64,B_63) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_479])).

tff(c_20,plain,(
    ! [A_13,B_14] : k3_tarski(k2_tarski(A_13,B_14)) = k2_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_609,plain,(
    ! [B_65,A_66] : k2_xboole_0(B_65,A_66) = k2_xboole_0(A_66,B_65) ),
    inference(superposition,[status(thm),theory(equality)],[c_583,c_20])).

tff(c_644,plain,(
    k2_xboole_0('#skF_3','#skF_2') = k1_tarski('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_609,c_28])).

tff(c_676,plain,(
    k1_tarski('#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_539,c_644])).

tff(c_678,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_400,c_676])).

tff(c_679,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_22])).

tff(c_680,plain,(
    k1_tarski('#skF_1') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_22])).

tff(c_26,plain,
    ( k1_tarski('#skF_1') != '#skF_3'
    | k1_tarski('#skF_1') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_718,plain,(
    '#skF_2' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_680,c_680,c_26])).

tff(c_752,plain,(
    ! [A_73,B_74] : k3_tarski(k2_tarski(A_73,B_74)) = k2_xboole_0(A_73,B_74) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_818,plain,(
    ! [A_79,B_80] : k3_tarski(k2_tarski(A_79,B_80)) = k2_xboole_0(B_80,A_79) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_752])).

tff(c_844,plain,(
    ! [B_81,A_82] : k2_xboole_0(B_81,A_82) = k2_xboole_0(A_82,B_81) ),
    inference(superposition,[status(thm),theory(equality)],[c_818,c_20])).

tff(c_708,plain,(
    k2_xboole_0('#skF_2','#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_680,c_28])).

tff(c_859,plain,(
    k2_xboole_0('#skF_3','#skF_2') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_844,c_708])).

tff(c_6,plain,(
    ! [A_4,B_5] : r1_tarski(A_4,k2_xboole_0(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_898,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_859,c_6])).

tff(c_1063,plain,(
    ! [B_91,A_92] :
      ( k1_tarski(B_91) = A_92
      | k1_xboole_0 = A_92
      | ~ r1_tarski(A_92,k1_tarski(B_91)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1074,plain,(
    ! [A_92] :
      ( k1_tarski('#skF_1') = A_92
      | k1_xboole_0 = A_92
      | ~ r1_tarski(A_92,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_680,c_1063])).

tff(c_1098,plain,(
    ! [A_94] :
      ( A_94 = '#skF_2'
      | k1_xboole_0 = A_94
      | ~ r1_tarski(A_94,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_680,c_1074])).

tff(c_1109,plain,
    ( '#skF_2' = '#skF_3'
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_898,c_1098])).

tff(c_1121,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_679,c_718,c_1109])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:37:04 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.48/1.37  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.48/1.37  
% 2.48/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.48/1.37  %$ r1_tarski > k1_enumset1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.48/1.37  
% 2.48/1.37  %Foreground sorts:
% 2.48/1.37  
% 2.48/1.37  
% 2.48/1.37  %Background operators:
% 2.48/1.37  
% 2.48/1.37  
% 2.48/1.37  %Foreground operators:
% 2.48/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.48/1.37  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.48/1.37  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.48/1.37  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.48/1.37  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.48/1.37  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.48/1.37  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.48/1.37  tff('#skF_2', type, '#skF_2': $i).
% 2.48/1.37  tff('#skF_3', type, '#skF_3': $i).
% 2.48/1.37  tff('#skF_1', type, '#skF_1': $i).
% 2.48/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.48/1.37  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.48/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.48/1.37  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.48/1.37  
% 2.72/1.39  tff(f_64, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~((B = k1_tarski(A)) & (C = k1_tarski(A)))) & ~((B = k1_xboole_0) & (C = k1_tarski(A)))) & ~((B = k1_tarski(A)) & (C = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_zfmisc_1)).
% 2.72/1.39  tff(f_31, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.72/1.39  tff(f_43, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 2.72/1.39  tff(f_27, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 2.72/1.39  tff(f_29, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_xboole_1)).
% 2.72/1.39  tff(f_33, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.72/1.39  tff(f_45, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 2.72/1.39  tff(c_24, plain, (k1_tarski('#skF_1')!='#skF_3' | k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.72/1.39  tff(c_40, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_24])).
% 2.72/1.39  tff(c_22, plain, (k1_xboole_0!='#skF_3' | k1_tarski('#skF_1')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.72/1.39  tff(c_39, plain, (k1_tarski('#skF_1')!='#skF_2'), inference(splitLeft, [status(thm)], [c_22])).
% 2.72/1.39  tff(c_28, plain, (k2_xboole_0('#skF_2', '#skF_3')=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.72/1.39  tff(c_46, plain, (![A_18, B_19]: (r1_tarski(A_18, k2_xboole_0(A_18, B_19)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.72/1.39  tff(c_49, plain, (r1_tarski('#skF_2', k1_tarski('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_28, c_46])).
% 2.72/1.39  tff(c_376, plain, (![B_41, A_42]: (k1_tarski(B_41)=A_42 | k1_xboole_0=A_42 | ~r1_tarski(A_42, k1_tarski(B_41)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.72/1.39  tff(c_390, plain, (k1_tarski('#skF_1')='#skF_2' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_49, c_376])).
% 2.72/1.39  tff(c_399, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_39, c_390])).
% 2.72/1.39  tff(c_400, plain, (k1_tarski('#skF_1')!='#skF_3'), inference(splitRight, [status(thm)], [c_24])).
% 2.72/1.39  tff(c_401, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_24])).
% 2.72/1.39  tff(c_2, plain, (![A_1]: (k4_xboole_0(A_1, k1_xboole_0)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.72/1.39  tff(c_402, plain, (![A_1]: (k4_xboole_0(A_1, '#skF_2')=A_1)), inference(demodulation, [status(thm), theory('equality')], [c_401, c_2])).
% 2.72/1.39  tff(c_517, plain, (![A_56, B_57]: (k4_xboole_0(k2_xboole_0(A_56, B_57), B_57)=k4_xboole_0(A_56, B_57))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.72/1.39  tff(c_524, plain, (![A_56]: (k4_xboole_0(A_56, '#skF_2')=k2_xboole_0(A_56, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_517, c_402])).
% 2.72/1.39  tff(c_539, plain, (![A_56]: (k2_xboole_0(A_56, '#skF_2')=A_56)), inference(demodulation, [status(thm), theory('equality')], [c_402, c_524])).
% 2.72/1.39  tff(c_8, plain, (![B_7, A_6]: (k2_tarski(B_7, A_6)=k2_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.72/1.39  tff(c_479, plain, (![A_53, B_54]: (k3_tarski(k2_tarski(A_53, B_54))=k2_xboole_0(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.72/1.39  tff(c_583, plain, (![B_63, A_64]: (k3_tarski(k2_tarski(B_63, A_64))=k2_xboole_0(A_64, B_63))), inference(superposition, [status(thm), theory('equality')], [c_8, c_479])).
% 2.72/1.39  tff(c_20, plain, (![A_13, B_14]: (k3_tarski(k2_tarski(A_13, B_14))=k2_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.72/1.39  tff(c_609, plain, (![B_65, A_66]: (k2_xboole_0(B_65, A_66)=k2_xboole_0(A_66, B_65))), inference(superposition, [status(thm), theory('equality')], [c_583, c_20])).
% 2.72/1.39  tff(c_644, plain, (k2_xboole_0('#skF_3', '#skF_2')=k1_tarski('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_609, c_28])).
% 2.72/1.39  tff(c_676, plain, (k1_tarski('#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_539, c_644])).
% 2.72/1.39  tff(c_678, plain, $false, inference(negUnitSimplification, [status(thm)], [c_400, c_676])).
% 2.72/1.39  tff(c_679, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_22])).
% 2.72/1.39  tff(c_680, plain, (k1_tarski('#skF_1')='#skF_2'), inference(splitRight, [status(thm)], [c_22])).
% 2.72/1.39  tff(c_26, plain, (k1_tarski('#skF_1')!='#skF_3' | k1_tarski('#skF_1')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.72/1.39  tff(c_718, plain, ('#skF_2'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_680, c_680, c_26])).
% 2.72/1.39  tff(c_752, plain, (![A_73, B_74]: (k3_tarski(k2_tarski(A_73, B_74))=k2_xboole_0(A_73, B_74))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.72/1.39  tff(c_818, plain, (![A_79, B_80]: (k3_tarski(k2_tarski(A_79, B_80))=k2_xboole_0(B_80, A_79))), inference(superposition, [status(thm), theory('equality')], [c_8, c_752])).
% 2.72/1.39  tff(c_844, plain, (![B_81, A_82]: (k2_xboole_0(B_81, A_82)=k2_xboole_0(A_82, B_81))), inference(superposition, [status(thm), theory('equality')], [c_818, c_20])).
% 2.72/1.39  tff(c_708, plain, (k2_xboole_0('#skF_2', '#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_680, c_28])).
% 2.72/1.39  tff(c_859, plain, (k2_xboole_0('#skF_3', '#skF_2')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_844, c_708])).
% 2.72/1.39  tff(c_6, plain, (![A_4, B_5]: (r1_tarski(A_4, k2_xboole_0(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.72/1.39  tff(c_898, plain, (r1_tarski('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_859, c_6])).
% 2.72/1.39  tff(c_1063, plain, (![B_91, A_92]: (k1_tarski(B_91)=A_92 | k1_xboole_0=A_92 | ~r1_tarski(A_92, k1_tarski(B_91)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.72/1.39  tff(c_1074, plain, (![A_92]: (k1_tarski('#skF_1')=A_92 | k1_xboole_0=A_92 | ~r1_tarski(A_92, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_680, c_1063])).
% 2.72/1.39  tff(c_1098, plain, (![A_94]: (A_94='#skF_2' | k1_xboole_0=A_94 | ~r1_tarski(A_94, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_680, c_1074])).
% 2.72/1.39  tff(c_1109, plain, ('#skF_2'='#skF_3' | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_898, c_1098])).
% 2.72/1.39  tff(c_1121, plain, $false, inference(negUnitSimplification, [status(thm)], [c_679, c_718, c_1109])).
% 2.72/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.72/1.39  
% 2.72/1.39  Inference rules
% 2.72/1.39  ----------------------
% 2.72/1.39  #Ref     : 0
% 2.72/1.39  #Sup     : 269
% 2.72/1.39  #Fact    : 0
% 2.72/1.39  #Define  : 0
% 2.72/1.39  #Split   : 3
% 2.72/1.39  #Chain   : 0
% 2.72/1.39  #Close   : 0
% 2.72/1.39  
% 2.72/1.39  Ordering : KBO
% 2.72/1.39  
% 2.72/1.39  Simplification rules
% 2.72/1.39  ----------------------
% 2.72/1.39  #Subsume      : 6
% 2.72/1.39  #Demod        : 82
% 2.72/1.39  #Tautology    : 200
% 2.72/1.39  #SimpNegUnit  : 5
% 2.72/1.39  #BackRed      : 2
% 2.72/1.39  
% 2.72/1.39  #Partial instantiations: 0
% 2.72/1.39  #Strategies tried      : 1
% 2.72/1.39  
% 2.72/1.39  Timing (in seconds)
% 2.72/1.39  ----------------------
% 2.72/1.39  Preprocessing        : 0.28
% 2.72/1.39  Parsing              : 0.15
% 2.72/1.39  CNF conversion       : 0.02
% 2.72/1.39  Main loop            : 0.33
% 2.72/1.39  Inferencing          : 0.12
% 2.72/1.39  Reduction            : 0.11
% 2.72/1.39  Demodulation         : 0.09
% 2.72/1.39  BG Simplification    : 0.02
% 2.72/1.39  Subsumption          : 0.05
% 2.72/1.39  Abstraction          : 0.02
% 2.72/1.39  MUC search           : 0.00
% 2.72/1.39  Cooper               : 0.00
% 2.72/1.39  Total                : 0.64
% 2.72/1.39  Index Insertion      : 0.00
% 2.72/1.39  Index Deletion       : 0.00
% 2.72/1.39  Index Matching       : 0.00
% 2.72/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
