%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:55 EST 2020

% Result     : Theorem 6.61s
% Output     : CNFRefutation 6.75s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 109 expanded)
%              Number of leaves         :   26 (  48 expanded)
%              Depth                    :   13
%              Number of atoms          :   56 ( 123 expanded)
%              Number of equality atoms :   42 (  91 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_66,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(A,B)
          & k3_xboole_0(B,C) = k1_tarski(D)
          & r2_hidden(D,A) )
       => k3_xboole_0(A,C) = k1_tarski(D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] : k3_xboole_0(A,k2_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] : k3_xboole_0(k3_xboole_0(A,B),C) = k3_xboole_0(A,k3_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k2_xboole_0(k1_tarski(A),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l22_zfmisc_1)).

tff(c_32,plain,(
    k3_xboole_0('#skF_1','#skF_3') != k1_tarski('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_34,plain,(
    r2_hidden('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_63,plain,(
    ! [B_29,A_30] : k3_xboole_0(B_29,A_30) = k3_xboole_0(A_30,B_29) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_36,plain,(
    k3_xboole_0('#skF_2','#skF_3') = k1_tarski('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_78,plain,(
    k3_xboole_0('#skF_3','#skF_2') = k1_tarski('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_63,c_36])).

tff(c_18,plain,(
    ! [A_12,B_13] : k3_xboole_0(A_12,k2_xboole_0(A_12,B_13)) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_10,plain,(
    ! [B_6] : r1_tarski(B_6,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_134,plain,(
    ! [A_37,B_38] :
      ( k4_xboole_0(A_37,B_38) = k1_xboole_0
      | ~ r1_tarski(A_37,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_145,plain,(
    ! [B_6] : k4_xboole_0(B_6,B_6) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_134])).

tff(c_188,plain,(
    ! [A_44,B_45] : k4_xboole_0(A_44,k3_xboole_0(A_44,B_45)) = k4_xboole_0(A_44,B_45) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_197,plain,(
    ! [A_12,B_13] : k4_xboole_0(A_12,k2_xboole_0(A_12,B_13)) = k4_xboole_0(A_12,A_12) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_188])).

tff(c_215,plain,(
    ! [A_12,B_13] : k4_xboole_0(A_12,k2_xboole_0(A_12,B_13)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_145,c_197])).

tff(c_227,plain,(
    ! [A_48,B_49] : k4_xboole_0(A_48,k4_xboole_0(A_48,B_49)) = k3_xboole_0(A_48,B_49) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_242,plain,(
    ! [A_12,B_13] : k3_xboole_0(A_12,k2_xboole_0(A_12,B_13)) = k4_xboole_0(A_12,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_215,c_227])).

tff(c_256,plain,(
    ! [A_12] : k4_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_242])).

tff(c_38,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_146,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_38,c_134])).

tff(c_248,plain,(
    k4_xboole_0('#skF_1',k1_xboole_0) = k3_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_146,c_227])).

tff(c_460,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_256,c_248])).

tff(c_733,plain,(
    ! [A_63,B_64,C_65] : k3_xboole_0(k3_xboole_0(A_63,B_64),C_65) = k3_xboole_0(A_63,k3_xboole_0(B_64,C_65)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_786,plain,(
    ! [C_65] : k3_xboole_0('#skF_1',k3_xboole_0('#skF_2',C_65)) = k3_xboole_0('#skF_1',C_65) ),
    inference(superposition,[status(thm),theory(equality)],[c_460,c_733])).

tff(c_22,plain,(
    ! [A_16,B_17] : k4_xboole_0(A_16,k4_xboole_0(A_16,B_17)) = k3_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_485,plain,(
    ! [B_57,A_58] : k4_xboole_0(B_57,k3_xboole_0(A_58,B_57)) = k4_xboole_0(B_57,A_58) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_188])).

tff(c_495,plain,(
    ! [B_57,A_58] : k4_xboole_0(B_57,k4_xboole_0(B_57,A_58)) = k3_xboole_0(B_57,k3_xboole_0(A_58,B_57)) ),
    inference(superposition,[status(thm),theory(equality)],[c_485,c_22])).

tff(c_546,plain,(
    ! [B_57,A_58] : k3_xboole_0(B_57,k3_xboole_0(A_58,B_57)) = k3_xboole_0(B_57,A_58) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_495])).

tff(c_2982,plain,(
    ! [C_97,A_98,B_99] : k3_xboole_0(C_97,k3_xboole_0(A_98,B_99)) = k3_xboole_0(A_98,k3_xboole_0(B_99,C_97)) ),
    inference(superposition,[status(thm),theory(equality)],[c_733,c_2])).

tff(c_7007,plain,(
    ! [C_133] : k3_xboole_0('#skF_1',k3_xboole_0('#skF_2',C_133)) = k3_xboole_0(C_133,'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_460,c_2982])).

tff(c_7137,plain,(
    ! [A_58] : k3_xboole_0(k3_xboole_0(A_58,'#skF_2'),'#skF_1') = k3_xboole_0('#skF_1',k3_xboole_0('#skF_2',A_58)) ),
    inference(superposition,[status(thm),theory(equality)],[c_546,c_7007])).

tff(c_8545,plain,(
    ! [A_144] : k3_xboole_0(k3_xboole_0(A_144,'#skF_2'),'#skF_1') = k3_xboole_0('#skF_1',A_144) ),
    inference(demodulation,[status(thm),theory(equality)],[c_786,c_7137])).

tff(c_8670,plain,(
    k3_xboole_0(k1_tarski('#skF_4'),'#skF_1') = k3_xboole_0('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_8545])).

tff(c_158,plain,(
    ! [A_40,B_41] :
      ( k2_xboole_0(k1_tarski(A_40),B_41) = B_41
      | ~ r2_hidden(A_40,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_164,plain,(
    ! [A_40,B_41] :
      ( k3_xboole_0(k1_tarski(A_40),B_41) = k1_tarski(A_40)
      | ~ r2_hidden(A_40,B_41) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_158,c_18])).

tff(c_8764,plain,
    ( k3_xboole_0('#skF_1','#skF_3') = k1_tarski('#skF_4')
    | ~ r2_hidden('#skF_4','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_8670,c_164])).

tff(c_8814,plain,(
    k3_xboole_0('#skF_1','#skF_3') = k1_tarski('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_8764])).

tff(c_8816,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_8814])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 16:26:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.61/2.42  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.61/2.43  
% 6.61/2.43  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.61/2.43  %$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 6.61/2.43  
% 6.61/2.43  %Foreground sorts:
% 6.61/2.43  
% 6.61/2.43  
% 6.61/2.43  %Background operators:
% 6.61/2.43  
% 6.61/2.43  
% 6.61/2.43  %Foreground operators:
% 6.61/2.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.61/2.43  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.61/2.43  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.61/2.43  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.61/2.43  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.61/2.43  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.61/2.43  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.61/2.43  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.61/2.43  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.61/2.43  tff('#skF_2', type, '#skF_2': $i).
% 6.61/2.43  tff('#skF_3', type, '#skF_3': $i).
% 6.61/2.43  tff('#skF_1', type, '#skF_1': $i).
% 6.61/2.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.61/2.43  tff('#skF_4', type, '#skF_4': $i).
% 6.61/2.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.61/2.43  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.61/2.43  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.61/2.43  
% 6.75/2.45  tff(f_66, negated_conjecture, ~(![A, B, C, D]: (((r1_tarski(A, B) & (k3_xboole_0(B, C) = k1_tarski(D))) & r2_hidden(D, A)) => (k3_xboole_0(A, C) = k1_tarski(D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_zfmisc_1)).
% 6.75/2.45  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 6.75/2.45  tff(f_43, axiom, (![A, B]: (k3_xboole_0(A, k2_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_xboole_1)).
% 6.75/2.45  tff(f_35, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 6.75/2.45  tff(f_39, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 6.75/2.45  tff(f_45, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 6.75/2.45  tff(f_47, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 6.75/2.45  tff(f_41, axiom, (![A, B, C]: (k3_xboole_0(k3_xboole_0(A, B), C) = k3_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_xboole_1)).
% 6.75/2.45  tff(f_57, axiom, (![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l22_zfmisc_1)).
% 6.75/2.45  tff(c_32, plain, (k3_xboole_0('#skF_1', '#skF_3')!=k1_tarski('#skF_4')), inference(cnfTransformation, [status(thm)], [f_66])).
% 6.75/2.45  tff(c_34, plain, (r2_hidden('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_66])).
% 6.75/2.45  tff(c_63, plain, (![B_29, A_30]: (k3_xboole_0(B_29, A_30)=k3_xboole_0(A_30, B_29))), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.75/2.45  tff(c_36, plain, (k3_xboole_0('#skF_2', '#skF_3')=k1_tarski('#skF_4')), inference(cnfTransformation, [status(thm)], [f_66])).
% 6.75/2.45  tff(c_78, plain, (k3_xboole_0('#skF_3', '#skF_2')=k1_tarski('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_63, c_36])).
% 6.75/2.45  tff(c_18, plain, (![A_12, B_13]: (k3_xboole_0(A_12, k2_xboole_0(A_12, B_13))=A_12)), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.75/2.45  tff(c_10, plain, (![B_6]: (r1_tarski(B_6, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.75/2.45  tff(c_134, plain, (![A_37, B_38]: (k4_xboole_0(A_37, B_38)=k1_xboole_0 | ~r1_tarski(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.75/2.45  tff(c_145, plain, (![B_6]: (k4_xboole_0(B_6, B_6)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_134])).
% 6.75/2.45  tff(c_188, plain, (![A_44, B_45]: (k4_xboole_0(A_44, k3_xboole_0(A_44, B_45))=k4_xboole_0(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.75/2.45  tff(c_197, plain, (![A_12, B_13]: (k4_xboole_0(A_12, k2_xboole_0(A_12, B_13))=k4_xboole_0(A_12, A_12))), inference(superposition, [status(thm), theory('equality')], [c_18, c_188])).
% 6.75/2.45  tff(c_215, plain, (![A_12, B_13]: (k4_xboole_0(A_12, k2_xboole_0(A_12, B_13))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_145, c_197])).
% 6.75/2.45  tff(c_227, plain, (![A_48, B_49]: (k4_xboole_0(A_48, k4_xboole_0(A_48, B_49))=k3_xboole_0(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.75/2.45  tff(c_242, plain, (![A_12, B_13]: (k3_xboole_0(A_12, k2_xboole_0(A_12, B_13))=k4_xboole_0(A_12, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_215, c_227])).
% 6.75/2.45  tff(c_256, plain, (![A_12]: (k4_xboole_0(A_12, k1_xboole_0)=A_12)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_242])).
% 6.75/2.45  tff(c_38, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_66])).
% 6.75/2.45  tff(c_146, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_38, c_134])).
% 6.75/2.45  tff(c_248, plain, (k4_xboole_0('#skF_1', k1_xboole_0)=k3_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_146, c_227])).
% 6.75/2.45  tff(c_460, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_256, c_248])).
% 6.75/2.45  tff(c_733, plain, (![A_63, B_64, C_65]: (k3_xboole_0(k3_xboole_0(A_63, B_64), C_65)=k3_xboole_0(A_63, k3_xboole_0(B_64, C_65)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.75/2.45  tff(c_786, plain, (![C_65]: (k3_xboole_0('#skF_1', k3_xboole_0('#skF_2', C_65))=k3_xboole_0('#skF_1', C_65))), inference(superposition, [status(thm), theory('equality')], [c_460, c_733])).
% 6.75/2.45  tff(c_22, plain, (![A_16, B_17]: (k4_xboole_0(A_16, k4_xboole_0(A_16, B_17))=k3_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.75/2.45  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.75/2.45  tff(c_485, plain, (![B_57, A_58]: (k4_xboole_0(B_57, k3_xboole_0(A_58, B_57))=k4_xboole_0(B_57, A_58))), inference(superposition, [status(thm), theory('equality')], [c_2, c_188])).
% 6.75/2.45  tff(c_495, plain, (![B_57, A_58]: (k4_xboole_0(B_57, k4_xboole_0(B_57, A_58))=k3_xboole_0(B_57, k3_xboole_0(A_58, B_57)))), inference(superposition, [status(thm), theory('equality')], [c_485, c_22])).
% 6.75/2.45  tff(c_546, plain, (![B_57, A_58]: (k3_xboole_0(B_57, k3_xboole_0(A_58, B_57))=k3_xboole_0(B_57, A_58))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_495])).
% 6.75/2.45  tff(c_2982, plain, (![C_97, A_98, B_99]: (k3_xboole_0(C_97, k3_xboole_0(A_98, B_99))=k3_xboole_0(A_98, k3_xboole_0(B_99, C_97)))), inference(superposition, [status(thm), theory('equality')], [c_733, c_2])).
% 6.75/2.45  tff(c_7007, plain, (![C_133]: (k3_xboole_0('#skF_1', k3_xboole_0('#skF_2', C_133))=k3_xboole_0(C_133, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_460, c_2982])).
% 6.75/2.45  tff(c_7137, plain, (![A_58]: (k3_xboole_0(k3_xboole_0(A_58, '#skF_2'), '#skF_1')=k3_xboole_0('#skF_1', k3_xboole_0('#skF_2', A_58)))), inference(superposition, [status(thm), theory('equality')], [c_546, c_7007])).
% 6.75/2.45  tff(c_8545, plain, (![A_144]: (k3_xboole_0(k3_xboole_0(A_144, '#skF_2'), '#skF_1')=k3_xboole_0('#skF_1', A_144))), inference(demodulation, [status(thm), theory('equality')], [c_786, c_7137])).
% 6.75/2.45  tff(c_8670, plain, (k3_xboole_0(k1_tarski('#skF_4'), '#skF_1')=k3_xboole_0('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_78, c_8545])).
% 6.75/2.45  tff(c_158, plain, (![A_40, B_41]: (k2_xboole_0(k1_tarski(A_40), B_41)=B_41 | ~r2_hidden(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.75/2.45  tff(c_164, plain, (![A_40, B_41]: (k3_xboole_0(k1_tarski(A_40), B_41)=k1_tarski(A_40) | ~r2_hidden(A_40, B_41))), inference(superposition, [status(thm), theory('equality')], [c_158, c_18])).
% 6.75/2.45  tff(c_8764, plain, (k3_xboole_0('#skF_1', '#skF_3')=k1_tarski('#skF_4') | ~r2_hidden('#skF_4', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_8670, c_164])).
% 6.75/2.45  tff(c_8814, plain, (k3_xboole_0('#skF_1', '#skF_3')=k1_tarski('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_8764])).
% 6.75/2.45  tff(c_8816, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_8814])).
% 6.75/2.45  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.75/2.45  
% 6.75/2.45  Inference rules
% 6.75/2.45  ----------------------
% 6.75/2.45  #Ref     : 0
% 6.75/2.45  #Sup     : 2148
% 6.75/2.45  #Fact    : 0
% 6.75/2.45  #Define  : 0
% 6.75/2.45  #Split   : 1
% 6.75/2.45  #Chain   : 0
% 6.75/2.45  #Close   : 0
% 6.75/2.45  
% 6.75/2.45  Ordering : KBO
% 6.75/2.45  
% 6.75/2.45  Simplification rules
% 6.75/2.45  ----------------------
% 6.75/2.45  #Subsume      : 70
% 6.75/2.45  #Demod        : 2501
% 6.75/2.45  #Tautology    : 1408
% 6.75/2.45  #SimpNegUnit  : 1
% 6.75/2.45  #BackRed      : 3
% 6.75/2.45  
% 6.75/2.45  #Partial instantiations: 0
% 6.75/2.45  #Strategies tried      : 1
% 6.75/2.45  
% 6.75/2.45  Timing (in seconds)
% 6.75/2.45  ----------------------
% 6.75/2.45  Preprocessing        : 0.30
% 6.75/2.45  Parsing              : 0.16
% 6.75/2.45  CNF conversion       : 0.02
% 6.75/2.45  Main loop            : 1.37
% 6.75/2.45  Inferencing          : 0.35
% 6.75/2.45  Reduction            : 0.75
% 6.75/2.45  Demodulation         : 0.65
% 6.75/2.45  BG Simplification    : 0.04
% 6.75/2.45  Subsumption          : 0.17
% 6.75/2.45  Abstraction          : 0.06
% 6.75/2.45  MUC search           : 0.00
% 6.75/2.45  Cooper               : 0.00
% 6.75/2.45  Total                : 1.71
% 6.75/2.45  Index Insertion      : 0.00
% 6.75/2.45  Index Deletion       : 0.00
% 6.75/2.45  Index Matching       : 0.00
% 6.75/2.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
