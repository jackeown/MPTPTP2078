%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:57 EST 2020

% Result     : Theorem 13.61s
% Output     : CNFRefutation 13.61s
% Verified   : 
% Statistics : Number of formulae       :   65 (  90 expanded)
%              Number of leaves         :   33 (  47 expanded)
%              Depth                    :   11
%              Number of atoms          :   56 ( 100 expanded)
%              Number of equality atoms :   37 (  65 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

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

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_92,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(A,B)
          & k3_xboole_0(B,C) = k1_tarski(D)
          & r2_hidden(D,A) )
       => k3_xboole_0(A,C) = k1_tarski(D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_53,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_57,axiom,(
    ! [A,B] : k3_xboole_0(A,k2_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).

tff(f_55,axiom,(
    ! [A,B,C] : k3_xboole_0(k3_xboole_0(A,B),C) = k3_xboole_0(A,k3_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_65,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & r2_hidden(C,B) )
     => k3_xboole_0(k2_tarski(A,C),B) = k2_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_zfmisc_1)).

tff(c_54,plain,(
    k3_xboole_0('#skF_4','#skF_6') != k1_tarski('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_56,plain,(
    r2_hidden('#skF_7','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_98,plain,(
    ! [B_65,A_66] : k3_xboole_0(B_65,A_66) = k3_xboole_0(A_66,B_65) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_58,plain,(
    k3_xboole_0('#skF_5','#skF_6') = k1_tarski('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_113,plain,(
    k3_xboole_0('#skF_6','#skF_5') = k1_tarski('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_98,c_58])).

tff(c_60,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_150,plain,(
    ! [A_67,B_68] :
      ( k2_xboole_0(A_67,B_68) = B_68
      | ~ r1_tarski(A_67,B_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_162,plain,(
    k2_xboole_0('#skF_4','#skF_5') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_60,c_150])).

tff(c_30,plain,(
    ! [A_19,B_20] : k3_xboole_0(A_19,k2_xboole_0(A_19,B_20)) = A_19 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_166,plain,(
    k3_xboole_0('#skF_4','#skF_5') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_162,c_30])).

tff(c_754,plain,(
    ! [A_104,B_105,C_106] : k3_xboole_0(k3_xboole_0(A_104,B_105),C_106) = k3_xboole_0(A_104,k3_xboole_0(B_105,C_106)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_818,plain,(
    ! [C_106] : k3_xboole_0('#skF_4',k3_xboole_0('#skF_5',C_106)) = k3_xboole_0('#skF_4',C_106) ),
    inference(superposition,[status(thm),theory(equality)],[c_166,c_754])).

tff(c_36,plain,(
    ! [A_24,B_25] : k4_xboole_0(A_24,k4_xboole_0(A_24,B_25)) = k3_xboole_0(A_24,B_25) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_28,plain,(
    ! [A_16,B_17,C_18] : k3_xboole_0(k3_xboole_0(A_16,B_17),C_18) = k3_xboole_0(A_16,k3_xboole_0(B_17,C_18)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_32,plain,(
    ! [A_21,B_22] : r1_tarski(k4_xboole_0(A_21,B_22),A_21) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_204,plain,(
    ! [A_73,B_74] : k2_xboole_0(k4_xboole_0(A_73,B_74),A_73) = A_73 ),
    inference(resolution,[status(thm)],[c_32,c_150])).

tff(c_6799,plain,(
    ! [A_286,B_287] : k3_xboole_0(k4_xboole_0(A_286,B_287),A_286) = k4_xboole_0(A_286,B_287) ),
    inference(superposition,[status(thm),theory(equality)],[c_204,c_30])).

tff(c_6953,plain,(
    ! [A_24,B_25] : k4_xboole_0(A_24,k4_xboole_0(A_24,B_25)) = k3_xboole_0(k3_xboole_0(A_24,B_25),A_24) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_6799])).

tff(c_6997,plain,(
    ! [A_24,B_25] : k3_xboole_0(A_24,k3_xboole_0(B_25,A_24)) = k3_xboole_0(A_24,B_25) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_28,c_6953])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_11329,plain,(
    ! [A_354,A_352,B_353] : k3_xboole_0(A_354,k3_xboole_0(A_352,B_353)) = k3_xboole_0(A_352,k3_xboole_0(B_353,A_354)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_754])).

tff(c_13075,plain,(
    ! [A_363] : k3_xboole_0('#skF_4',k3_xboole_0('#skF_5',A_363)) = k3_xboole_0(A_363,'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_166,c_11329])).

tff(c_13240,plain,(
    ! [B_25] : k3_xboole_0(k3_xboole_0(B_25,'#skF_5'),'#skF_4') = k3_xboole_0('#skF_4',k3_xboole_0('#skF_5',B_25)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6997,c_13075])).

tff(c_35041,plain,(
    ! [B_537] : k3_xboole_0(k3_xboole_0(B_537,'#skF_5'),'#skF_4') = k3_xboole_0('#skF_4',B_537) ),
    inference(demodulation,[status(thm),theory(equality)],[c_818,c_13240])).

tff(c_35274,plain,(
    k3_xboole_0(k1_tarski('#skF_7'),'#skF_4') = k3_xboole_0('#skF_4','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_113,c_35041])).

tff(c_38,plain,(
    ! [A_26] : k2_tarski(A_26,A_26) = k1_tarski(A_26) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1925,plain,(
    ! [A_154,C_155,B_156] :
      ( k3_xboole_0(k2_tarski(A_154,C_155),B_156) = k2_tarski(A_154,C_155)
      | ~ r2_hidden(C_155,B_156)
      | ~ r2_hidden(A_154,B_156) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_2039,plain,(
    ! [A_26,B_156] :
      ( k3_xboole_0(k1_tarski(A_26),B_156) = k2_tarski(A_26,A_26)
      | ~ r2_hidden(A_26,B_156)
      | ~ r2_hidden(A_26,B_156) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_1925])).

tff(c_2051,plain,(
    ! [A_26,B_156] :
      ( k3_xboole_0(k1_tarski(A_26),B_156) = k1_tarski(A_26)
      | ~ r2_hidden(A_26,B_156)
      | ~ r2_hidden(A_26,B_156) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_2039])).

tff(c_35382,plain,
    ( k3_xboole_0('#skF_4','#skF_6') = k1_tarski('#skF_7')
    | ~ r2_hidden('#skF_7','#skF_4')
    | ~ r2_hidden('#skF_7','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_35274,c_2051])).

tff(c_35529,plain,(
    k3_xboole_0('#skF_4','#skF_6') = k1_tarski('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_56,c_35382])).

tff(c_35531,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_35529])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:27:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 13.61/5.90  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.61/5.90  
% 13.61/5.90  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.61/5.90  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3
% 13.61/5.90  
% 13.61/5.90  %Foreground sorts:
% 13.61/5.90  
% 13.61/5.90  
% 13.61/5.90  %Background operators:
% 13.61/5.90  
% 13.61/5.90  
% 13.61/5.90  %Foreground operators:
% 13.61/5.90  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 13.61/5.90  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 13.61/5.90  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 13.61/5.90  tff(k1_tarski, type, k1_tarski: $i > $i).
% 13.61/5.90  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 13.61/5.90  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 13.61/5.90  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 13.61/5.90  tff('#skF_7', type, '#skF_7': $i).
% 13.61/5.90  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 13.61/5.90  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 13.61/5.90  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 13.61/5.90  tff('#skF_5', type, '#skF_5': $i).
% 13.61/5.90  tff('#skF_6', type, '#skF_6': $i).
% 13.61/5.90  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 13.61/5.90  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 13.61/5.90  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 13.61/5.90  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 13.61/5.90  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 13.61/5.90  tff('#skF_4', type, '#skF_4': $i).
% 13.61/5.90  tff('#skF_3', type, '#skF_3': $i > $i).
% 13.61/5.90  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 13.61/5.90  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 13.61/5.90  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 13.61/5.90  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 13.61/5.90  
% 13.61/5.92  tff(f_92, negated_conjecture, ~(![A, B, C, D]: (((r1_tarski(A, B) & (k3_xboole_0(B, C) = k1_tarski(D))) & r2_hidden(D, A)) => (k3_xboole_0(A, C) = k1_tarski(D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_zfmisc_1)).
% 13.61/5.92  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 13.61/5.92  tff(f_53, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 13.61/5.92  tff(f_57, axiom, (![A, B]: (k3_xboole_0(A, k2_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_xboole_1)).
% 13.61/5.92  tff(f_55, axiom, (![A, B, C]: (k3_xboole_0(k3_xboole_0(A, B), C) = k3_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_xboole_1)).
% 13.61/5.92  tff(f_63, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 13.61/5.92  tff(f_59, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 13.61/5.92  tff(f_65, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 13.61/5.92  tff(f_83, axiom, (![A, B, C]: ((r2_hidden(A, B) & r2_hidden(C, B)) => (k3_xboole_0(k2_tarski(A, C), B) = k2_tarski(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t53_zfmisc_1)).
% 13.61/5.92  tff(c_54, plain, (k3_xboole_0('#skF_4', '#skF_6')!=k1_tarski('#skF_7')), inference(cnfTransformation, [status(thm)], [f_92])).
% 13.61/5.92  tff(c_56, plain, (r2_hidden('#skF_7', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_92])).
% 13.61/5.92  tff(c_98, plain, (![B_65, A_66]: (k3_xboole_0(B_65, A_66)=k3_xboole_0(A_66, B_65))), inference(cnfTransformation, [status(thm)], [f_27])).
% 13.61/5.92  tff(c_58, plain, (k3_xboole_0('#skF_5', '#skF_6')=k1_tarski('#skF_7')), inference(cnfTransformation, [status(thm)], [f_92])).
% 13.61/5.92  tff(c_113, plain, (k3_xboole_0('#skF_6', '#skF_5')=k1_tarski('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_98, c_58])).
% 13.61/5.92  tff(c_60, plain, (r1_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_92])).
% 13.61/5.92  tff(c_150, plain, (![A_67, B_68]: (k2_xboole_0(A_67, B_68)=B_68 | ~r1_tarski(A_67, B_68))), inference(cnfTransformation, [status(thm)], [f_53])).
% 13.61/5.92  tff(c_162, plain, (k2_xboole_0('#skF_4', '#skF_5')='#skF_5'), inference(resolution, [status(thm)], [c_60, c_150])).
% 13.61/5.92  tff(c_30, plain, (![A_19, B_20]: (k3_xboole_0(A_19, k2_xboole_0(A_19, B_20))=A_19)), inference(cnfTransformation, [status(thm)], [f_57])).
% 13.61/5.92  tff(c_166, plain, (k3_xboole_0('#skF_4', '#skF_5')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_162, c_30])).
% 13.61/5.92  tff(c_754, plain, (![A_104, B_105, C_106]: (k3_xboole_0(k3_xboole_0(A_104, B_105), C_106)=k3_xboole_0(A_104, k3_xboole_0(B_105, C_106)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 13.61/5.92  tff(c_818, plain, (![C_106]: (k3_xboole_0('#skF_4', k3_xboole_0('#skF_5', C_106))=k3_xboole_0('#skF_4', C_106))), inference(superposition, [status(thm), theory('equality')], [c_166, c_754])).
% 13.61/5.92  tff(c_36, plain, (![A_24, B_25]: (k4_xboole_0(A_24, k4_xboole_0(A_24, B_25))=k3_xboole_0(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_63])).
% 13.61/5.92  tff(c_28, plain, (![A_16, B_17, C_18]: (k3_xboole_0(k3_xboole_0(A_16, B_17), C_18)=k3_xboole_0(A_16, k3_xboole_0(B_17, C_18)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 13.61/5.92  tff(c_32, plain, (![A_21, B_22]: (r1_tarski(k4_xboole_0(A_21, B_22), A_21))), inference(cnfTransformation, [status(thm)], [f_59])).
% 13.61/5.92  tff(c_204, plain, (![A_73, B_74]: (k2_xboole_0(k4_xboole_0(A_73, B_74), A_73)=A_73)), inference(resolution, [status(thm)], [c_32, c_150])).
% 13.61/5.92  tff(c_6799, plain, (![A_286, B_287]: (k3_xboole_0(k4_xboole_0(A_286, B_287), A_286)=k4_xboole_0(A_286, B_287))), inference(superposition, [status(thm), theory('equality')], [c_204, c_30])).
% 13.61/5.92  tff(c_6953, plain, (![A_24, B_25]: (k4_xboole_0(A_24, k4_xboole_0(A_24, B_25))=k3_xboole_0(k3_xboole_0(A_24, B_25), A_24))), inference(superposition, [status(thm), theory('equality')], [c_36, c_6799])).
% 13.61/5.92  tff(c_6997, plain, (![A_24, B_25]: (k3_xboole_0(A_24, k3_xboole_0(B_25, A_24))=k3_xboole_0(A_24, B_25))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_28, c_6953])).
% 13.61/5.92  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 13.61/5.92  tff(c_11329, plain, (![A_354, A_352, B_353]: (k3_xboole_0(A_354, k3_xboole_0(A_352, B_353))=k3_xboole_0(A_352, k3_xboole_0(B_353, A_354)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_754])).
% 13.61/5.92  tff(c_13075, plain, (![A_363]: (k3_xboole_0('#skF_4', k3_xboole_0('#skF_5', A_363))=k3_xboole_0(A_363, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_166, c_11329])).
% 13.61/5.92  tff(c_13240, plain, (![B_25]: (k3_xboole_0(k3_xboole_0(B_25, '#skF_5'), '#skF_4')=k3_xboole_0('#skF_4', k3_xboole_0('#skF_5', B_25)))), inference(superposition, [status(thm), theory('equality')], [c_6997, c_13075])).
% 13.61/5.92  tff(c_35041, plain, (![B_537]: (k3_xboole_0(k3_xboole_0(B_537, '#skF_5'), '#skF_4')=k3_xboole_0('#skF_4', B_537))), inference(demodulation, [status(thm), theory('equality')], [c_818, c_13240])).
% 13.61/5.92  tff(c_35274, plain, (k3_xboole_0(k1_tarski('#skF_7'), '#skF_4')=k3_xboole_0('#skF_4', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_113, c_35041])).
% 13.61/5.92  tff(c_38, plain, (![A_26]: (k2_tarski(A_26, A_26)=k1_tarski(A_26))), inference(cnfTransformation, [status(thm)], [f_65])).
% 13.61/5.92  tff(c_1925, plain, (![A_154, C_155, B_156]: (k3_xboole_0(k2_tarski(A_154, C_155), B_156)=k2_tarski(A_154, C_155) | ~r2_hidden(C_155, B_156) | ~r2_hidden(A_154, B_156))), inference(cnfTransformation, [status(thm)], [f_83])).
% 13.61/5.92  tff(c_2039, plain, (![A_26, B_156]: (k3_xboole_0(k1_tarski(A_26), B_156)=k2_tarski(A_26, A_26) | ~r2_hidden(A_26, B_156) | ~r2_hidden(A_26, B_156))), inference(superposition, [status(thm), theory('equality')], [c_38, c_1925])).
% 13.61/5.92  tff(c_2051, plain, (![A_26, B_156]: (k3_xboole_0(k1_tarski(A_26), B_156)=k1_tarski(A_26) | ~r2_hidden(A_26, B_156) | ~r2_hidden(A_26, B_156))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_2039])).
% 13.61/5.92  tff(c_35382, plain, (k3_xboole_0('#skF_4', '#skF_6')=k1_tarski('#skF_7') | ~r2_hidden('#skF_7', '#skF_4') | ~r2_hidden('#skF_7', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_35274, c_2051])).
% 13.61/5.92  tff(c_35529, plain, (k3_xboole_0('#skF_4', '#skF_6')=k1_tarski('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_56, c_35382])).
% 13.61/5.92  tff(c_35531, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_35529])).
% 13.61/5.92  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.61/5.92  
% 13.61/5.92  Inference rules
% 13.61/5.92  ----------------------
% 13.61/5.92  #Ref     : 0
% 13.61/5.92  #Sup     : 8729
% 13.61/5.92  #Fact    : 0
% 13.61/5.92  #Define  : 0
% 13.61/5.92  #Split   : 1
% 13.61/5.92  #Chain   : 0
% 13.61/5.92  #Close   : 0
% 13.61/5.92  
% 13.61/5.92  Ordering : KBO
% 13.61/5.92  
% 13.61/5.92  Simplification rules
% 13.61/5.92  ----------------------
% 13.61/5.92  #Subsume      : 532
% 13.61/5.92  #Demod        : 9325
% 13.61/5.92  #Tautology    : 4965
% 13.61/5.92  #SimpNegUnit  : 13
% 13.61/5.92  #BackRed      : 54
% 13.61/5.92  
% 13.61/5.92  #Partial instantiations: 0
% 13.61/5.92  #Strategies tried      : 1
% 13.61/5.92  
% 13.61/5.92  Timing (in seconds)
% 13.61/5.92  ----------------------
% 13.76/5.92  Preprocessing        : 0.33
% 13.76/5.92  Parsing              : 0.17
% 13.76/5.92  CNF conversion       : 0.02
% 13.76/5.92  Main loop            : 4.82
% 13.76/5.92  Inferencing          : 0.78
% 13.76/5.92  Reduction            : 2.93
% 13.76/5.92  Demodulation         : 2.63
% 13.76/5.92  BG Simplification    : 0.10
% 13.76/5.92  Subsumption          : 0.79
% 13.76/5.92  Abstraction          : 0.15
% 13.76/5.92  MUC search           : 0.00
% 13.76/5.92  Cooper               : 0.00
% 13.76/5.92  Total                : 5.18
% 13.76/5.92  Index Insertion      : 0.00
% 13.76/5.92  Index Deletion       : 0.00
% 13.76/5.92  Index Matching       : 0.00
% 13.76/5.92  BG Taut test         : 0.00
%------------------------------------------------------------------------------
