%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:56 EST 2020

% Result     : Theorem 10.12s
% Output     : CNFRefutation 10.12s
% Verified   : 
% Statistics : Number of formulae       :   59 (  74 expanded)
%              Number of leaves         :   30 (  39 expanded)
%              Depth                    :   10
%              Number of atoms          :   47 (  71 expanded)
%              Number of equality atoms :   36 (  54 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_83,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(A,B)
          & k3_xboole_0(B,C) = k1_tarski(D)
          & r2_hidden(D,A) )
       => k3_xboole_0(A,C) = k1_tarski(D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_62,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_60,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_56,axiom,(
    ! [A,B] : k3_xboole_0(A,k2_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).

tff(f_50,axiom,(
    ! [A,B,C] : k3_xboole_0(k3_xboole_0(A,B),C) = k3_xboole_0(A,k3_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).

tff(f_54,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_74,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k2_xboole_0(k1_tarski(A),B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l22_zfmisc_1)).

tff(c_54,plain,(
    k3_xboole_0('#skF_4','#skF_6') != k1_tarski('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_56,plain,(
    r2_hidden('#skF_7','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_58,plain,(
    k3_xboole_0('#skF_5','#skF_6') = k1_tarski('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_42,plain,(
    ! [A_27,B_28] : k4_xboole_0(A_27,k4_xboole_0(A_27,B_28)) = k3_xboole_0(A_27,B_28) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_842,plain,(
    ! [A_86,B_87] : k4_xboole_0(A_86,k3_xboole_0(A_86,B_87)) = k4_xboole_0(A_86,B_87) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_848,plain,(
    ! [A_86,B_87] : k4_xboole_0(A_86,k4_xboole_0(A_86,B_87)) = k3_xboole_0(A_86,k3_xboole_0(A_86,B_87)) ),
    inference(superposition,[status(thm),theory(equality)],[c_842,c_42])).

tff(c_3466,plain,(
    ! [A_182,B_183] : k3_xboole_0(A_182,k3_xboole_0(A_182,B_183)) = k3_xboole_0(A_182,B_183) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_848])).

tff(c_3622,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,k3_xboole_0(A_1,B_2)) = k3_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_3466])).

tff(c_60,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_225,plain,(
    ! [A_58,B_59] :
      ( k2_xboole_0(A_58,B_59) = B_59
      | ~ r1_tarski(A_58,B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_253,plain,(
    k2_xboole_0('#skF_4','#skF_5') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_60,c_225])).

tff(c_36,plain,(
    ! [A_22,B_23] : k3_xboole_0(A_22,k2_xboole_0(A_22,B_23)) = A_22 ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_260,plain,(
    k3_xboole_0('#skF_4','#skF_5') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_253,c_36])).

tff(c_1494,plain,(
    ! [A_115,B_116,C_117] : k3_xboole_0(k3_xboole_0(A_115,B_116),C_117) = k3_xboole_0(A_115,k3_xboole_0(B_116,C_117)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_6863,plain,(
    ! [A_230,A_228,B_229] : k3_xboole_0(A_230,k3_xboole_0(A_228,B_229)) = k3_xboole_0(A_228,k3_xboole_0(B_229,A_230)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1494])).

tff(c_19073,plain,(
    ! [A_344] : k3_xboole_0('#skF_4',k3_xboole_0('#skF_5',A_344)) = k3_xboole_0(A_344,'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_260,c_6863])).

tff(c_34,plain,(
    ! [A_21] : k2_xboole_0(A_21,k1_xboole_0) = A_21 ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_96,plain,(
    ! [A_46,B_47] : k3_xboole_0(A_46,k2_xboole_0(A_46,B_47)) = A_46 ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_108,plain,(
    ! [A_21] : k3_xboole_0(A_21,A_21) = A_21 ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_96])).

tff(c_7458,plain,(
    ! [A_21,A_230] : k3_xboole_0(A_21,k3_xboole_0(A_21,A_230)) = k3_xboole_0(A_230,A_21) ),
    inference(superposition,[status(thm),theory(equality)],[c_108,c_6863])).

tff(c_19114,plain,(
    ! [A_344] : k3_xboole_0(k3_xboole_0('#skF_5',A_344),'#skF_4') = k3_xboole_0('#skF_4',k3_xboole_0(A_344,'#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_19073,c_7458])).

tff(c_26141,plain,(
    ! [A_396] : k3_xboole_0(k3_xboole_0('#skF_5',A_396),'#skF_4') = k3_xboole_0('#skF_4',A_396) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3622,c_19114])).

tff(c_26418,plain,(
    k3_xboole_0(k1_tarski('#skF_7'),'#skF_4') = k3_xboole_0('#skF_4','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_26141])).

tff(c_292,plain,(
    ! [A_61,B_62] :
      ( k2_xboole_0(k1_tarski(A_61),B_62) = B_62
      | ~ r2_hidden(A_61,B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_305,plain,(
    ! [A_61,B_62] :
      ( k3_xboole_0(k1_tarski(A_61),B_62) = k1_tarski(A_61)
      | ~ r2_hidden(A_61,B_62) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_292,c_36])).

tff(c_26718,plain,
    ( k3_xboole_0('#skF_4','#skF_6') = k1_tarski('#skF_7')
    | ~ r2_hidden('#skF_7','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_26418,c_305])).

tff(c_26844,plain,(
    k3_xboole_0('#skF_4','#skF_6') = k1_tarski('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_26718])).

tff(c_26846,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_26844])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:49:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.12/4.37  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.12/4.37  
% 10.12/4.37  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.12/4.37  %$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 10.12/4.37  
% 10.12/4.37  %Foreground sorts:
% 10.12/4.37  
% 10.12/4.37  
% 10.12/4.37  %Background operators:
% 10.12/4.37  
% 10.12/4.37  
% 10.12/4.37  %Foreground operators:
% 10.12/4.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.12/4.37  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 10.12/4.37  tff(k1_tarski, type, k1_tarski: $i > $i).
% 10.12/4.37  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 10.12/4.37  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 10.12/4.37  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 10.12/4.37  tff('#skF_7', type, '#skF_7': $i).
% 10.12/4.37  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.12/4.37  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 10.12/4.37  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 10.12/4.37  tff('#skF_5', type, '#skF_5': $i).
% 10.12/4.37  tff('#skF_6', type, '#skF_6': $i).
% 10.12/4.37  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 10.12/4.37  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 10.12/4.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.12/4.37  tff('#skF_4', type, '#skF_4': $i).
% 10.12/4.37  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 10.12/4.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.12/4.37  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 10.12/4.37  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 10.12/4.37  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 10.12/4.37  
% 10.12/4.38  tff(f_83, negated_conjecture, ~(![A, B, C, D]: (((r1_tarski(A, B) & (k3_xboole_0(B, C) = k1_tarski(D))) & r2_hidden(D, A)) => (k3_xboole_0(A, C) = k1_tarski(D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_zfmisc_1)).
% 10.12/4.38  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 10.12/4.38  tff(f_62, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 10.12/4.38  tff(f_60, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 10.12/4.38  tff(f_48, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 10.12/4.38  tff(f_56, axiom, (![A, B]: (k3_xboole_0(A, k2_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_xboole_1)).
% 10.12/4.38  tff(f_50, axiom, (![A, B, C]: (k3_xboole_0(k3_xboole_0(A, B), C) = k3_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_xboole_1)).
% 10.12/4.38  tff(f_54, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 10.12/4.38  tff(f_74, axiom, (![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l22_zfmisc_1)).
% 10.12/4.38  tff(c_54, plain, (k3_xboole_0('#skF_4', '#skF_6')!=k1_tarski('#skF_7')), inference(cnfTransformation, [status(thm)], [f_83])).
% 10.12/4.38  tff(c_56, plain, (r2_hidden('#skF_7', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_83])).
% 10.12/4.38  tff(c_58, plain, (k3_xboole_0('#skF_5', '#skF_6')=k1_tarski('#skF_7')), inference(cnfTransformation, [status(thm)], [f_83])).
% 10.12/4.38  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 10.12/4.38  tff(c_42, plain, (![A_27, B_28]: (k4_xboole_0(A_27, k4_xboole_0(A_27, B_28))=k3_xboole_0(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_62])).
% 10.12/4.38  tff(c_842, plain, (![A_86, B_87]: (k4_xboole_0(A_86, k3_xboole_0(A_86, B_87))=k4_xboole_0(A_86, B_87))), inference(cnfTransformation, [status(thm)], [f_60])).
% 10.12/4.38  tff(c_848, plain, (![A_86, B_87]: (k4_xboole_0(A_86, k4_xboole_0(A_86, B_87))=k3_xboole_0(A_86, k3_xboole_0(A_86, B_87)))), inference(superposition, [status(thm), theory('equality')], [c_842, c_42])).
% 10.12/4.38  tff(c_3466, plain, (![A_182, B_183]: (k3_xboole_0(A_182, k3_xboole_0(A_182, B_183))=k3_xboole_0(A_182, B_183))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_848])).
% 10.12/4.38  tff(c_3622, plain, (![B_2, A_1]: (k3_xboole_0(B_2, k3_xboole_0(A_1, B_2))=k3_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_3466])).
% 10.12/4.38  tff(c_60, plain, (r1_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_83])).
% 10.12/4.38  tff(c_225, plain, (![A_58, B_59]: (k2_xboole_0(A_58, B_59)=B_59 | ~r1_tarski(A_58, B_59))), inference(cnfTransformation, [status(thm)], [f_48])).
% 10.12/4.38  tff(c_253, plain, (k2_xboole_0('#skF_4', '#skF_5')='#skF_5'), inference(resolution, [status(thm)], [c_60, c_225])).
% 10.12/4.38  tff(c_36, plain, (![A_22, B_23]: (k3_xboole_0(A_22, k2_xboole_0(A_22, B_23))=A_22)), inference(cnfTransformation, [status(thm)], [f_56])).
% 10.12/4.38  tff(c_260, plain, (k3_xboole_0('#skF_4', '#skF_5')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_253, c_36])).
% 10.12/4.38  tff(c_1494, plain, (![A_115, B_116, C_117]: (k3_xboole_0(k3_xboole_0(A_115, B_116), C_117)=k3_xboole_0(A_115, k3_xboole_0(B_116, C_117)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 10.12/4.38  tff(c_6863, plain, (![A_230, A_228, B_229]: (k3_xboole_0(A_230, k3_xboole_0(A_228, B_229))=k3_xboole_0(A_228, k3_xboole_0(B_229, A_230)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1494])).
% 10.12/4.38  tff(c_19073, plain, (![A_344]: (k3_xboole_0('#skF_4', k3_xboole_0('#skF_5', A_344))=k3_xboole_0(A_344, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_260, c_6863])).
% 10.12/4.38  tff(c_34, plain, (![A_21]: (k2_xboole_0(A_21, k1_xboole_0)=A_21)), inference(cnfTransformation, [status(thm)], [f_54])).
% 10.12/4.38  tff(c_96, plain, (![A_46, B_47]: (k3_xboole_0(A_46, k2_xboole_0(A_46, B_47))=A_46)), inference(cnfTransformation, [status(thm)], [f_56])).
% 10.12/4.38  tff(c_108, plain, (![A_21]: (k3_xboole_0(A_21, A_21)=A_21)), inference(superposition, [status(thm), theory('equality')], [c_34, c_96])).
% 10.12/4.38  tff(c_7458, plain, (![A_21, A_230]: (k3_xboole_0(A_21, k3_xboole_0(A_21, A_230))=k3_xboole_0(A_230, A_21))), inference(superposition, [status(thm), theory('equality')], [c_108, c_6863])).
% 10.12/4.38  tff(c_19114, plain, (![A_344]: (k3_xboole_0(k3_xboole_0('#skF_5', A_344), '#skF_4')=k3_xboole_0('#skF_4', k3_xboole_0(A_344, '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_19073, c_7458])).
% 10.12/4.38  tff(c_26141, plain, (![A_396]: (k3_xboole_0(k3_xboole_0('#skF_5', A_396), '#skF_4')=k3_xboole_0('#skF_4', A_396))), inference(demodulation, [status(thm), theory('equality')], [c_3622, c_19114])).
% 10.12/4.38  tff(c_26418, plain, (k3_xboole_0(k1_tarski('#skF_7'), '#skF_4')=k3_xboole_0('#skF_4', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_58, c_26141])).
% 10.12/4.38  tff(c_292, plain, (![A_61, B_62]: (k2_xboole_0(k1_tarski(A_61), B_62)=B_62 | ~r2_hidden(A_61, B_62))), inference(cnfTransformation, [status(thm)], [f_74])).
% 10.12/4.38  tff(c_305, plain, (![A_61, B_62]: (k3_xboole_0(k1_tarski(A_61), B_62)=k1_tarski(A_61) | ~r2_hidden(A_61, B_62))), inference(superposition, [status(thm), theory('equality')], [c_292, c_36])).
% 10.12/4.38  tff(c_26718, plain, (k3_xboole_0('#skF_4', '#skF_6')=k1_tarski('#skF_7') | ~r2_hidden('#skF_7', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_26418, c_305])).
% 10.12/4.38  tff(c_26844, plain, (k3_xboole_0('#skF_4', '#skF_6')=k1_tarski('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_26718])).
% 10.12/4.38  tff(c_26846, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_26844])).
% 10.12/4.38  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.12/4.38  
% 10.12/4.38  Inference rules
% 10.12/4.38  ----------------------
% 10.12/4.38  #Ref     : 0
% 10.12/4.38  #Sup     : 6598
% 10.12/4.38  #Fact    : 0
% 10.12/4.38  #Define  : 0
% 10.12/4.38  #Split   : 4
% 10.12/4.38  #Chain   : 0
% 10.12/4.38  #Close   : 0
% 10.12/4.38  
% 10.12/4.38  Ordering : KBO
% 10.12/4.38  
% 10.12/4.38  Simplification rules
% 10.12/4.38  ----------------------
% 10.12/4.38  #Subsume      : 349
% 10.12/4.38  #Demod        : 6695
% 10.12/4.38  #Tautology    : 4075
% 10.12/4.38  #SimpNegUnit  : 3
% 10.12/4.38  #BackRed      : 6
% 10.12/4.38  
% 10.12/4.38  #Partial instantiations: 0
% 10.12/4.38  #Strategies tried      : 1
% 10.12/4.38  
% 10.12/4.38  Timing (in seconds)
% 10.12/4.38  ----------------------
% 10.12/4.39  Preprocessing        : 0.31
% 10.12/4.39  Parsing              : 0.16
% 10.12/4.39  CNF conversion       : 0.02
% 10.12/4.39  Main loop            : 3.31
% 10.12/4.39  Inferencing          : 0.59
% 10.12/4.39  Reduction            : 1.94
% 10.12/4.39  Demodulation         : 1.71
% 10.12/4.39  BG Simplification    : 0.07
% 10.12/4.39  Subsumption          : 0.56
% 10.12/4.39  Abstraction          : 0.10
% 10.12/4.39  MUC search           : 0.00
% 10.12/4.39  Cooper               : 0.00
% 10.12/4.39  Total                : 3.65
% 10.12/4.39  Index Insertion      : 0.00
% 10.12/4.39  Index Deletion       : 0.00
% 10.12/4.39  Index Matching       : 0.00
% 10.12/4.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
