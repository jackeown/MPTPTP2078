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

% Result     : Theorem 2.54s
% Output     : CNFRefutation 2.78s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 121 expanded)
%              Number of leaves         :   26 (  50 expanded)
%              Depth                    :    9
%              Number of atoms          :   70 ( 247 expanded)
%              Number of equality atoms :   57 ( 232 expanded)
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

tff(f_74,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k1_tarski(A) = k2_xboole_0(B,C)
          & ~ ( B = k1_tarski(A)
              & C = k1_tarski(A) )
          & ~ ( B = k1_xboole_0
              & C = k1_tarski(A) )
          & ~ ( B = k1_tarski(A)
              & C = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_37,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_33,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(c_34,plain,
    ( k1_tarski('#skF_1') != '#skF_3'
    | k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_57,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_32,plain,
    ( k1_xboole_0 != '#skF_3'
    | k1_tarski('#skF_1') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_56,plain,(
    k1_tarski('#skF_1') != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_38,plain,(
    k2_xboole_0('#skF_2','#skF_3') = k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_72,plain,(
    ! [A_32,B_33] : r1_tarski(A_32,k2_xboole_0(A_32,B_33)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_75,plain,(
    r1_tarski('#skF_2',k1_tarski('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_72])).

tff(c_472,plain,(
    ! [B_60,A_61] :
      ( k1_tarski(B_60) = A_61
      | k1_xboole_0 = A_61
      | ~ r1_tarski(A_61,k1_tarski(B_60)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_486,plain,
    ( k1_tarski('#skF_1') = '#skF_2'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_75,c_472])).

tff(c_495,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_57,c_56,c_486])).

tff(c_496,plain,(
    k1_tarski('#skF_1') != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_497,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_12,plain,(
    ! [A_10] : k5_xboole_0(A_10,k1_xboole_0) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_498,plain,(
    ! [A_10] : k5_xboole_0(A_10,'#skF_2') = A_10 ),
    inference(demodulation,[status(thm),theory(equality)],[c_497,c_12])).

tff(c_8,plain,(
    ! [A_7] : k3_xboole_0(A_7,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_499,plain,(
    ! [A_7] : k3_xboole_0(A_7,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_497,c_497,c_8])).

tff(c_775,plain,(
    ! [A_84,B_85] : k5_xboole_0(A_84,k3_xboole_0(A_84,B_85)) = k4_xboole_0(A_84,B_85) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_793,plain,(
    ! [A_7] : k5_xboole_0(A_7,'#skF_2') = k4_xboole_0(A_7,'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_499,c_775])).

tff(c_797,plain,(
    ! [A_7] : k4_xboole_0(A_7,'#skF_2') = A_7 ),
    inference(demodulation,[status(thm),theory(equality)],[c_498,c_793])).

tff(c_798,plain,(
    ! [A_86] : k4_xboole_0(A_86,'#skF_2') = A_86 ),
    inference(demodulation,[status(thm),theory(equality)],[c_498,c_793])).

tff(c_10,plain,(
    ! [A_8,B_9] : k4_xboole_0(k2_xboole_0(A_8,B_9),B_9) = k4_xboole_0(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_805,plain,(
    ! [A_8] : k4_xboole_0(A_8,'#skF_2') = k2_xboole_0(A_8,'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_798,c_10])).

tff(c_814,plain,(
    ! [A_8] : k2_xboole_0(A_8,'#skF_2') = A_8 ),
    inference(demodulation,[status(thm),theory(equality)],[c_797,c_805])).

tff(c_541,plain,(
    ! [B_69,A_70] : k2_xboole_0(B_69,A_70) = k2_xboole_0(A_70,B_69) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_580,plain,(
    k2_xboole_0('#skF_3','#skF_2') = k1_tarski('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_541])).

tff(c_834,plain,(
    k1_tarski('#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_814,c_580])).

tff(c_836,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_496,c_834])).

tff(c_837,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_838,plain,(
    k1_tarski('#skF_1') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_36,plain,
    ( k1_tarski('#skF_1') != '#skF_3'
    | k1_tarski('#skF_1') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_874,plain,(
    '#skF_2' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_838,c_838,c_36])).

tff(c_958,plain,(
    ! [B_95,A_96] : k2_xboole_0(B_95,A_96) = k2_xboole_0(A_96,B_95) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_856,plain,(
    k2_xboole_0('#skF_2','#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_838,c_38])).

tff(c_973,plain,(
    k2_xboole_0('#skF_3','#skF_2') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_958,c_856])).

tff(c_14,plain,(
    ! [A_11,B_12] : r1_tarski(A_11,k2_xboole_0(A_11,B_12)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1012,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_973,c_14])).

tff(c_1181,plain,(
    ! [B_110,A_111] :
      ( k1_tarski(B_110) = A_111
      | k1_xboole_0 = A_111
      | ~ r1_tarski(A_111,k1_tarski(B_110)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1187,plain,(
    ! [A_111] :
      ( k1_tarski('#skF_1') = A_111
      | k1_xboole_0 = A_111
      | ~ r1_tarski(A_111,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_838,c_1181])).

tff(c_1255,plain,(
    ! [A_115] :
      ( A_115 = '#skF_2'
      | k1_xboole_0 = A_115
      | ~ r1_tarski(A_115,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_838,c_1187])).

tff(c_1262,plain,
    ( '#skF_2' = '#skF_3'
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_1012,c_1255])).

tff(c_1273,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_837,c_874,c_1262])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n016.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 18:57:04 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.19/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.54/1.37  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.54/1.38  
% 2.54/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.54/1.38  %$ r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.54/1.38  
% 2.54/1.38  %Foreground sorts:
% 2.54/1.38  
% 2.54/1.38  
% 2.54/1.38  %Background operators:
% 2.54/1.38  
% 2.54/1.38  
% 2.54/1.38  %Foreground operators:
% 2.54/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.54/1.38  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.54/1.38  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.54/1.38  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.54/1.38  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.54/1.38  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.54/1.38  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.54/1.38  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.54/1.38  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.54/1.38  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.54/1.38  tff('#skF_2', type, '#skF_2': $i).
% 2.54/1.38  tff('#skF_3', type, '#skF_3': $i).
% 2.54/1.38  tff('#skF_1', type, '#skF_1': $i).
% 2.54/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.54/1.38  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.54/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.54/1.38  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.54/1.38  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.54/1.38  
% 2.78/1.39  tff(f_74, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~((B = k1_tarski(A)) & (C = k1_tarski(A)))) & ~((B = k1_xboole_0) & (C = k1_tarski(A)))) & ~((B = k1_tarski(A)) & (C = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_zfmisc_1)).
% 2.78/1.39  tff(f_39, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.78/1.39  tff(f_53, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 2.78/1.39  tff(f_37, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 2.78/1.39  tff(f_33, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 2.78/1.39  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.78/1.39  tff(f_35, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_xboole_1)).
% 2.78/1.39  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.78/1.39  tff(c_34, plain, (k1_tarski('#skF_1')!='#skF_3' | k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.78/1.39  tff(c_57, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_34])).
% 2.78/1.39  tff(c_32, plain, (k1_xboole_0!='#skF_3' | k1_tarski('#skF_1')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.78/1.39  tff(c_56, plain, (k1_tarski('#skF_1')!='#skF_2'), inference(splitLeft, [status(thm)], [c_32])).
% 2.78/1.39  tff(c_38, plain, (k2_xboole_0('#skF_2', '#skF_3')=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.78/1.39  tff(c_72, plain, (![A_32, B_33]: (r1_tarski(A_32, k2_xboole_0(A_32, B_33)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.78/1.39  tff(c_75, plain, (r1_tarski('#skF_2', k1_tarski('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_38, c_72])).
% 2.78/1.39  tff(c_472, plain, (![B_60, A_61]: (k1_tarski(B_60)=A_61 | k1_xboole_0=A_61 | ~r1_tarski(A_61, k1_tarski(B_60)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.78/1.39  tff(c_486, plain, (k1_tarski('#skF_1')='#skF_2' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_75, c_472])).
% 2.78/1.39  tff(c_495, plain, $false, inference(negUnitSimplification, [status(thm)], [c_57, c_56, c_486])).
% 2.78/1.39  tff(c_496, plain, (k1_tarski('#skF_1')!='#skF_3'), inference(splitRight, [status(thm)], [c_34])).
% 2.78/1.39  tff(c_497, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_34])).
% 2.78/1.39  tff(c_12, plain, (![A_10]: (k5_xboole_0(A_10, k1_xboole_0)=A_10)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.78/1.39  tff(c_498, plain, (![A_10]: (k5_xboole_0(A_10, '#skF_2')=A_10)), inference(demodulation, [status(thm), theory('equality')], [c_497, c_12])).
% 2.78/1.39  tff(c_8, plain, (![A_7]: (k3_xboole_0(A_7, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.78/1.39  tff(c_499, plain, (![A_7]: (k3_xboole_0(A_7, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_497, c_497, c_8])).
% 2.78/1.39  tff(c_775, plain, (![A_84, B_85]: (k5_xboole_0(A_84, k3_xboole_0(A_84, B_85))=k4_xboole_0(A_84, B_85))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.78/1.39  tff(c_793, plain, (![A_7]: (k5_xboole_0(A_7, '#skF_2')=k4_xboole_0(A_7, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_499, c_775])).
% 2.78/1.39  tff(c_797, plain, (![A_7]: (k4_xboole_0(A_7, '#skF_2')=A_7)), inference(demodulation, [status(thm), theory('equality')], [c_498, c_793])).
% 2.78/1.39  tff(c_798, plain, (![A_86]: (k4_xboole_0(A_86, '#skF_2')=A_86)), inference(demodulation, [status(thm), theory('equality')], [c_498, c_793])).
% 2.78/1.39  tff(c_10, plain, (![A_8, B_9]: (k4_xboole_0(k2_xboole_0(A_8, B_9), B_9)=k4_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.78/1.39  tff(c_805, plain, (![A_8]: (k4_xboole_0(A_8, '#skF_2')=k2_xboole_0(A_8, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_798, c_10])).
% 2.78/1.39  tff(c_814, plain, (![A_8]: (k2_xboole_0(A_8, '#skF_2')=A_8)), inference(demodulation, [status(thm), theory('equality')], [c_797, c_805])).
% 2.78/1.39  tff(c_541, plain, (![B_69, A_70]: (k2_xboole_0(B_69, A_70)=k2_xboole_0(A_70, B_69))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.78/1.39  tff(c_580, plain, (k2_xboole_0('#skF_3', '#skF_2')=k1_tarski('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_38, c_541])).
% 2.78/1.39  tff(c_834, plain, (k1_tarski('#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_814, c_580])).
% 2.78/1.39  tff(c_836, plain, $false, inference(negUnitSimplification, [status(thm)], [c_496, c_834])).
% 2.78/1.39  tff(c_837, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_32])).
% 2.78/1.39  tff(c_838, plain, (k1_tarski('#skF_1')='#skF_2'), inference(splitRight, [status(thm)], [c_32])).
% 2.78/1.39  tff(c_36, plain, (k1_tarski('#skF_1')!='#skF_3' | k1_tarski('#skF_1')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.78/1.39  tff(c_874, plain, ('#skF_2'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_838, c_838, c_36])).
% 2.78/1.39  tff(c_958, plain, (![B_95, A_96]: (k2_xboole_0(B_95, A_96)=k2_xboole_0(A_96, B_95))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.78/1.39  tff(c_856, plain, (k2_xboole_0('#skF_2', '#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_838, c_38])).
% 2.78/1.39  tff(c_973, plain, (k2_xboole_0('#skF_3', '#skF_2')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_958, c_856])).
% 2.78/1.39  tff(c_14, plain, (![A_11, B_12]: (r1_tarski(A_11, k2_xboole_0(A_11, B_12)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.78/1.39  tff(c_1012, plain, (r1_tarski('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_973, c_14])).
% 2.78/1.39  tff(c_1181, plain, (![B_110, A_111]: (k1_tarski(B_110)=A_111 | k1_xboole_0=A_111 | ~r1_tarski(A_111, k1_tarski(B_110)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.78/1.39  tff(c_1187, plain, (![A_111]: (k1_tarski('#skF_1')=A_111 | k1_xboole_0=A_111 | ~r1_tarski(A_111, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_838, c_1181])).
% 2.78/1.39  tff(c_1255, plain, (![A_115]: (A_115='#skF_2' | k1_xboole_0=A_115 | ~r1_tarski(A_115, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_838, c_1187])).
% 2.78/1.39  tff(c_1262, plain, ('#skF_2'='#skF_3' | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_1012, c_1255])).
% 2.78/1.39  tff(c_1273, plain, $false, inference(negUnitSimplification, [status(thm)], [c_837, c_874, c_1262])).
% 2.78/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.78/1.39  
% 2.78/1.39  Inference rules
% 2.78/1.39  ----------------------
% 2.78/1.39  #Ref     : 0
% 2.78/1.39  #Sup     : 307
% 2.78/1.39  #Fact    : 0
% 2.78/1.39  #Define  : 0
% 2.78/1.39  #Split   : 3
% 2.78/1.39  #Chain   : 0
% 2.78/1.39  #Close   : 0
% 2.78/1.39  
% 2.78/1.39  Ordering : KBO
% 2.78/1.39  
% 2.78/1.39  Simplification rules
% 2.78/1.39  ----------------------
% 2.78/1.39  #Subsume      : 8
% 2.78/1.39  #Demod        : 98
% 2.78/1.39  #Tautology    : 235
% 2.78/1.39  #SimpNegUnit  : 4
% 2.78/1.39  #BackRed      : 4
% 2.78/1.39  
% 2.78/1.39  #Partial instantiations: 0
% 2.78/1.39  #Strategies tried      : 1
% 2.78/1.39  
% 2.78/1.39  Timing (in seconds)
% 2.78/1.39  ----------------------
% 2.78/1.40  Preprocessing        : 0.29
% 2.78/1.40  Parsing              : 0.16
% 2.78/1.40  CNF conversion       : 0.02
% 2.78/1.40  Main loop            : 0.34
% 2.78/1.40  Inferencing          : 0.12
% 2.78/1.40  Reduction            : 0.12
% 2.78/1.40  Demodulation         : 0.09
% 2.78/1.40  BG Simplification    : 0.02
% 2.78/1.40  Subsumption          : 0.05
% 2.78/1.40  Abstraction          : 0.02
% 2.78/1.40  MUC search           : 0.00
% 2.78/1.40  Cooper               : 0.00
% 2.78/1.40  Total                : 0.66
% 2.78/1.40  Index Insertion      : 0.00
% 2.78/1.40  Index Deletion       : 0.00
% 2.78/1.40  Index Matching       : 0.00
% 2.78/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
