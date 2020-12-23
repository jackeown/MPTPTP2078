%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:56 EST 2020

% Result     : Theorem 18.35s
% Output     : CNFRefutation 18.44s
% Verified   : 
% Statistics : Number of formulae       :   60 (  68 expanded)
%              Number of leaves         :   31 (  37 expanded)
%              Depth                    :    9
%              Number of atoms          :   48 (  65 expanded)
%              Number of equality atoms :   37 (  48 expanded)
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

tff(f_89,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(A,B)
          & k3_xboole_0(B,C) = k1_tarski(D)
          & r2_hidden(D,A) )
       => k3_xboole_0(A,C) = k1_tarski(D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_zfmisc_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k2_xboole_0(k1_tarski(A),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l22_zfmisc_1)).

tff(f_58,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_46,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_60,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k2_xboole_0(B,C)) = k2_xboole_0(k3_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_xboole_1)).

tff(f_68,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_66,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_52,axiom,(
    ! [A,B,C] : k3_xboole_0(k3_xboole_0(A,B),C) = k3_xboole_0(A,k3_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(c_58,plain,(
    k3_xboole_0('#skF_4','#skF_6') != k1_tarski('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_60,plain,(
    r2_hidden('#skF_7','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_56,plain,(
    ! [A_45,B_46] :
      ( k2_xboole_0(k1_tarski(A_45),B_46) = B_46
      | ~ r2_hidden(A_45,B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_38,plain,(
    ! [A_24,B_25] : k2_xboole_0(A_24,k3_xboole_0(A_24,B_25)) = A_24 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_28,plain,(
    ! [A_14] : k3_xboole_0(A_14,A_14) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_2900,plain,(
    ! [A_158,B_159,C_160] : k2_xboole_0(k3_xboole_0(A_158,B_159),k3_xboole_0(A_158,C_160)) = k3_xboole_0(A_158,k2_xboole_0(B_159,C_160)) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_3029,plain,(
    ! [A_14,C_160] : k3_xboole_0(A_14,k2_xboole_0(A_14,C_160)) = k2_xboole_0(A_14,k3_xboole_0(A_14,C_160)) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_2900])).

tff(c_3061,plain,(
    ! [A_161,C_162] : k3_xboole_0(A_161,k2_xboole_0(A_161,C_162)) = A_161 ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_3029])).

tff(c_61920,plain,(
    ! [A_646,B_647] :
      ( k3_xboole_0(k1_tarski(A_646),B_647) = k1_tarski(A_646)
      | ~ r2_hidden(A_646,B_647) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_3061])).

tff(c_62,plain,(
    k3_xboole_0('#skF_5','#skF_6') = k1_tarski('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_46,plain,(
    ! [A_33,B_34] : k4_xboole_0(A_33,k4_xboole_0(A_33,B_34)) = k3_xboole_0(A_33,B_34) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_44,plain,(
    ! [A_31,B_32] : k4_xboole_0(A_31,k3_xboole_0(A_31,B_32)) = k4_xboole_0(A_31,B_32) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_934,plain,(
    ! [A_86,B_87] : k4_xboole_0(A_86,k4_xboole_0(A_86,B_87)) = k3_xboole_0(A_86,B_87) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_983,plain,(
    ! [A_31,B_32] : k4_xboole_0(A_31,k4_xboole_0(A_31,B_32)) = k3_xboole_0(A_31,k3_xboole_0(A_31,B_32)) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_934])).

tff(c_997,plain,(
    ! [A_31,B_32] : k3_xboole_0(A_31,k3_xboole_0(A_31,B_32)) = k3_xboole_0(A_31,B_32) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_983])).

tff(c_64,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_304,plain,(
    ! [A_64,B_65] :
      ( k3_xboole_0(A_64,B_65) = A_64
      | ~ r1_tarski(A_64,B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_329,plain,(
    k3_xboole_0('#skF_4','#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_64,c_304])).

tff(c_1845,plain,(
    ! [A_129,B_130,C_131] : k3_xboole_0(k3_xboole_0(A_129,B_130),C_131) = k3_xboole_0(A_129,k3_xboole_0(B_130,C_131)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_1961,plain,(
    ! [C_131] : k3_xboole_0('#skF_4',k3_xboole_0('#skF_5',C_131)) = k3_xboole_0('#skF_4',C_131) ),
    inference(superposition,[status(thm),theory(equality)],[c_329,c_1845])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_8000,plain,(
    ! [C_263,A_264,B_265] : k3_xboole_0(C_263,k3_xboole_0(A_264,B_265)) = k3_xboole_0(A_264,k3_xboole_0(B_265,C_263)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1845,c_2])).

tff(c_34790,plain,(
    ! [A_473,C_474] : k3_xboole_0(A_473,k3_xboole_0(A_473,C_474)) = k3_xboole_0(C_474,A_473) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_8000])).

tff(c_35246,plain,(
    ! [C_131] : k3_xboole_0(k3_xboole_0('#skF_5',C_131),'#skF_4') = k3_xboole_0('#skF_4',k3_xboole_0('#skF_4',C_131)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1961,c_34790])).

tff(c_36871,plain,(
    ! [C_480] : k3_xboole_0(k3_xboole_0('#skF_5',C_480),'#skF_4') = k3_xboole_0('#skF_4',C_480) ),
    inference(demodulation,[status(thm),theory(equality)],[c_997,c_35246])).

tff(c_37183,plain,(
    k3_xboole_0(k1_tarski('#skF_7'),'#skF_4') = k3_xboole_0('#skF_4','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_36871])).

tff(c_62033,plain,
    ( k3_xboole_0('#skF_4','#skF_6') = k1_tarski('#skF_7')
    | ~ r2_hidden('#skF_7','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_61920,c_37183])).

tff(c_62576,plain,(
    k3_xboole_0('#skF_4','#skF_6') = k1_tarski('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_62033])).

tff(c_62578,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_62576])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.19/0.34  % CPULimit   : 60
% 0.19/0.34  % DateTime   : Tue Dec  1 21:06:00 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 18.35/10.90  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 18.35/10.90  
% 18.35/10.90  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 18.35/10.91  %$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 18.35/10.91  
% 18.35/10.91  %Foreground sorts:
% 18.35/10.91  
% 18.35/10.91  
% 18.35/10.91  %Background operators:
% 18.35/10.91  
% 18.35/10.91  
% 18.35/10.91  %Foreground operators:
% 18.35/10.91  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 18.35/10.91  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 18.35/10.91  tff(k1_tarski, type, k1_tarski: $i > $i).
% 18.35/10.91  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 18.35/10.91  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 18.35/10.91  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 18.35/10.91  tff('#skF_7', type, '#skF_7': $i).
% 18.35/10.91  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 18.35/10.91  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 18.35/10.91  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 18.35/10.91  tff('#skF_5', type, '#skF_5': $i).
% 18.35/10.91  tff('#skF_6', type, '#skF_6': $i).
% 18.35/10.91  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 18.35/10.91  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 18.35/10.91  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 18.35/10.91  tff('#skF_4', type, '#skF_4': $i).
% 18.35/10.91  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 18.35/10.91  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 18.35/10.91  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 18.35/10.91  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 18.35/10.91  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 18.35/10.91  
% 18.44/10.92  tff(f_89, negated_conjecture, ~(![A, B, C, D]: (((r1_tarski(A, B) & (k3_xboole_0(B, C) = k1_tarski(D))) & r2_hidden(D, A)) => (k3_xboole_0(A, C) = k1_tarski(D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_zfmisc_1)).
% 18.44/10.92  tff(f_80, axiom, (![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l22_zfmisc_1)).
% 18.44/10.92  tff(f_58, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_xboole_1)).
% 18.44/10.92  tff(f_46, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 18.44/10.92  tff(f_60, axiom, (![A, B, C]: (k3_xboole_0(A, k2_xboole_0(B, C)) = k2_xboole_0(k3_xboole_0(A, B), k3_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_xboole_1)).
% 18.44/10.92  tff(f_68, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 18.44/10.92  tff(f_66, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 18.44/10.92  tff(f_64, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 18.44/10.92  tff(f_52, axiom, (![A, B, C]: (k3_xboole_0(k3_xboole_0(A, B), C) = k3_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_xboole_1)).
% 18.44/10.92  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 18.44/10.92  tff(c_58, plain, (k3_xboole_0('#skF_4', '#skF_6')!=k1_tarski('#skF_7')), inference(cnfTransformation, [status(thm)], [f_89])).
% 18.44/10.92  tff(c_60, plain, (r2_hidden('#skF_7', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_89])).
% 18.44/10.92  tff(c_56, plain, (![A_45, B_46]: (k2_xboole_0(k1_tarski(A_45), B_46)=B_46 | ~r2_hidden(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_80])).
% 18.44/10.92  tff(c_38, plain, (![A_24, B_25]: (k2_xboole_0(A_24, k3_xboole_0(A_24, B_25))=A_24)), inference(cnfTransformation, [status(thm)], [f_58])).
% 18.44/10.92  tff(c_28, plain, (![A_14]: (k3_xboole_0(A_14, A_14)=A_14)), inference(cnfTransformation, [status(thm)], [f_46])).
% 18.44/10.92  tff(c_2900, plain, (![A_158, B_159, C_160]: (k2_xboole_0(k3_xboole_0(A_158, B_159), k3_xboole_0(A_158, C_160))=k3_xboole_0(A_158, k2_xboole_0(B_159, C_160)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 18.44/10.92  tff(c_3029, plain, (![A_14, C_160]: (k3_xboole_0(A_14, k2_xboole_0(A_14, C_160))=k2_xboole_0(A_14, k3_xboole_0(A_14, C_160)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_2900])).
% 18.44/10.92  tff(c_3061, plain, (![A_161, C_162]: (k3_xboole_0(A_161, k2_xboole_0(A_161, C_162))=A_161)), inference(demodulation, [status(thm), theory('equality')], [c_38, c_3029])).
% 18.44/10.92  tff(c_61920, plain, (![A_646, B_647]: (k3_xboole_0(k1_tarski(A_646), B_647)=k1_tarski(A_646) | ~r2_hidden(A_646, B_647))), inference(superposition, [status(thm), theory('equality')], [c_56, c_3061])).
% 18.44/10.92  tff(c_62, plain, (k3_xboole_0('#skF_5', '#skF_6')=k1_tarski('#skF_7')), inference(cnfTransformation, [status(thm)], [f_89])).
% 18.44/10.92  tff(c_46, plain, (![A_33, B_34]: (k4_xboole_0(A_33, k4_xboole_0(A_33, B_34))=k3_xboole_0(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_68])).
% 18.44/10.92  tff(c_44, plain, (![A_31, B_32]: (k4_xboole_0(A_31, k3_xboole_0(A_31, B_32))=k4_xboole_0(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_66])).
% 18.44/10.92  tff(c_934, plain, (![A_86, B_87]: (k4_xboole_0(A_86, k4_xboole_0(A_86, B_87))=k3_xboole_0(A_86, B_87))), inference(cnfTransformation, [status(thm)], [f_68])).
% 18.44/10.92  tff(c_983, plain, (![A_31, B_32]: (k4_xboole_0(A_31, k4_xboole_0(A_31, B_32))=k3_xboole_0(A_31, k3_xboole_0(A_31, B_32)))), inference(superposition, [status(thm), theory('equality')], [c_44, c_934])).
% 18.44/10.92  tff(c_997, plain, (![A_31, B_32]: (k3_xboole_0(A_31, k3_xboole_0(A_31, B_32))=k3_xboole_0(A_31, B_32))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_983])).
% 18.44/10.92  tff(c_64, plain, (r1_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_89])).
% 18.44/10.92  tff(c_304, plain, (![A_64, B_65]: (k3_xboole_0(A_64, B_65)=A_64 | ~r1_tarski(A_64, B_65))), inference(cnfTransformation, [status(thm)], [f_64])).
% 18.44/10.92  tff(c_329, plain, (k3_xboole_0('#skF_4', '#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_64, c_304])).
% 18.44/10.92  tff(c_1845, plain, (![A_129, B_130, C_131]: (k3_xboole_0(k3_xboole_0(A_129, B_130), C_131)=k3_xboole_0(A_129, k3_xboole_0(B_130, C_131)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 18.44/10.92  tff(c_1961, plain, (![C_131]: (k3_xboole_0('#skF_4', k3_xboole_0('#skF_5', C_131))=k3_xboole_0('#skF_4', C_131))), inference(superposition, [status(thm), theory('equality')], [c_329, c_1845])).
% 18.44/10.92  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 18.44/10.92  tff(c_8000, plain, (![C_263, A_264, B_265]: (k3_xboole_0(C_263, k3_xboole_0(A_264, B_265))=k3_xboole_0(A_264, k3_xboole_0(B_265, C_263)))), inference(superposition, [status(thm), theory('equality')], [c_1845, c_2])).
% 18.44/10.92  tff(c_34790, plain, (![A_473, C_474]: (k3_xboole_0(A_473, k3_xboole_0(A_473, C_474))=k3_xboole_0(C_474, A_473))), inference(superposition, [status(thm), theory('equality')], [c_28, c_8000])).
% 18.44/10.92  tff(c_35246, plain, (![C_131]: (k3_xboole_0(k3_xboole_0('#skF_5', C_131), '#skF_4')=k3_xboole_0('#skF_4', k3_xboole_0('#skF_4', C_131)))), inference(superposition, [status(thm), theory('equality')], [c_1961, c_34790])).
% 18.44/10.92  tff(c_36871, plain, (![C_480]: (k3_xboole_0(k3_xboole_0('#skF_5', C_480), '#skF_4')=k3_xboole_0('#skF_4', C_480))), inference(demodulation, [status(thm), theory('equality')], [c_997, c_35246])).
% 18.44/10.92  tff(c_37183, plain, (k3_xboole_0(k1_tarski('#skF_7'), '#skF_4')=k3_xboole_0('#skF_4', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_62, c_36871])).
% 18.44/10.92  tff(c_62033, plain, (k3_xboole_0('#skF_4', '#skF_6')=k1_tarski('#skF_7') | ~r2_hidden('#skF_7', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_61920, c_37183])).
% 18.44/10.92  tff(c_62576, plain, (k3_xboole_0('#skF_4', '#skF_6')=k1_tarski('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_62033])).
% 18.44/10.92  tff(c_62578, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_62576])).
% 18.44/10.92  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 18.44/10.92  
% 18.44/10.92  Inference rules
% 18.44/10.92  ----------------------
% 18.44/10.92  #Ref     : 0
% 18.44/10.92  #Sup     : 15548
% 18.44/10.92  #Fact    : 0
% 18.44/10.92  #Define  : 0
% 18.44/10.92  #Split   : 2
% 18.44/10.92  #Chain   : 0
% 18.44/10.92  #Close   : 0
% 18.44/10.92  
% 18.44/10.92  Ordering : KBO
% 18.44/10.92  
% 18.44/10.92  Simplification rules
% 18.44/10.92  ----------------------
% 18.44/10.92  #Subsume      : 716
% 18.44/10.92  #Demod        : 16966
% 18.44/10.92  #Tautology    : 9609
% 18.44/10.92  #SimpNegUnit  : 7
% 18.44/10.92  #BackRed      : 14
% 18.44/10.92  
% 18.44/10.92  #Partial instantiations: 0
% 18.44/10.92  #Strategies tried      : 1
% 18.44/10.92  
% 18.44/10.92  Timing (in seconds)
% 18.44/10.92  ----------------------
% 18.44/10.92  Preprocessing        : 0.34
% 18.44/10.92  Parsing              : 0.18
% 18.44/10.92  CNF conversion       : 0.03
% 18.44/10.92  Main loop            : 9.81
% 18.44/10.92  Inferencing          : 1.26
% 18.44/10.92  Reduction            : 6.20
% 18.44/10.92  Demodulation         : 5.61
% 18.44/10.92  BG Simplification    : 0.16
% 18.44/10.92  Subsumption          : 1.79
% 18.44/10.92  Abstraction          : 0.24
% 18.44/10.92  MUC search           : 0.00
% 18.44/10.92  Cooper               : 0.00
% 18.44/10.92  Total                : 10.18
% 18.44/10.92  Index Insertion      : 0.00
% 18.44/10.92  Index Deletion       : 0.00
% 18.44/10.92  Index Matching       : 0.00
% 18.44/10.92  BG Taut test         : 0.00
%------------------------------------------------------------------------------
