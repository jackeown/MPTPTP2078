%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:09 EST 2020

% Result     : Theorem 12.27s
% Output     : CNFRefutation 12.27s
% Verified   : 
% Statistics : Number of formulae       :   56 (  89 expanded)
%              Number of leaves         :   26 (  41 expanded)
%              Depth                    :    9
%              Number of atoms          :   42 (  75 expanded)
%              Number of equality atoms :   37 (  70 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

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

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_37,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_41,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] : r1_tarski(k1_tarski(A),k2_tarski(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_39,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_56,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(k1_tarski(A),k2_tarski(A,B)) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_zfmisc_1)).

tff(c_10,plain,(
    ! [A_9] : k5_xboole_0(A_9,k1_xboole_0) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_14,plain,(
    ! [A_13] : k5_xboole_0(A_13,A_13) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_26,plain,(
    ! [A_26,B_27] : r1_tarski(k1_tarski(A_26),k2_tarski(A_26,B_27)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_199,plain,(
    ! [A_39,B_40] :
      ( k3_xboole_0(A_39,B_40) = A_39
      | ~ r1_tarski(A_39,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_813,plain,(
    ! [A_70,B_71] : k3_xboole_0(k1_tarski(A_70),k2_tarski(A_70,B_71)) = k1_tarski(A_70) ),
    inference(resolution,[status(thm)],[c_26,c_199])).

tff(c_6,plain,(
    ! [A_5,B_6] : k5_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = k4_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_819,plain,(
    ! [A_70,B_71] : k5_xboole_0(k1_tarski(A_70),k1_tarski(A_70)) = k4_xboole_0(k1_tarski(A_70),k2_tarski(A_70,B_71)) ),
    inference(superposition,[status(thm),theory(equality)],[c_813,c_6])).

tff(c_928,plain,(
    ! [A_75,B_76] : k4_xboole_0(k1_tarski(A_75),k2_tarski(A_75,B_76)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_819])).

tff(c_16,plain,(
    ! [A_14,B_15] : k5_xboole_0(A_14,k4_xboole_0(B_15,A_14)) = k2_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_933,plain,(
    ! [A_75,B_76] : k2_xboole_0(k2_tarski(A_75,B_76),k1_tarski(A_75)) = k5_xboole_0(k2_tarski(A_75,B_76),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_928,c_16])).

tff(c_24149,plain,(
    ! [A_241,B_242] : k2_xboole_0(k2_tarski(A_241,B_242),k1_tarski(A_241)) = k2_tarski(A_241,B_242) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_933])).

tff(c_69,plain,(
    ! [B_34,A_35] : k5_xboole_0(B_34,A_35) = k5_xboole_0(A_35,B_34) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_85,plain,(
    ! [A_35] : k5_xboole_0(k1_xboole_0,A_35) = A_35 ),
    inference(superposition,[status(thm),theory(equality)],[c_69,c_10])).

tff(c_4,plain,(
    ! [B_4,A_3] : k5_xboole_0(B_4,A_3) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_334,plain,(
    ! [A_54,B_55,C_56] : k5_xboole_0(k5_xboole_0(A_54,B_55),C_56) = k5_xboole_0(A_54,k5_xboole_0(B_55,C_56)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_945,plain,(
    ! [A_79,A_77,B_78] : k5_xboole_0(A_79,k5_xboole_0(A_77,B_78)) = k5_xboole_0(A_77,k5_xboole_0(B_78,A_79)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_334])).

tff(c_1519,plain,(
    ! [A_87,A_88] : k5_xboole_0(k1_xboole_0,k5_xboole_0(A_87,A_88)) = k5_xboole_0(A_88,A_87) ),
    inference(superposition,[status(thm),theory(equality)],[c_85,c_945])).

tff(c_1624,plain,(
    ! [B_15,A_14] : k5_xboole_0(k4_xboole_0(B_15,A_14),A_14) = k5_xboole_0(k1_xboole_0,k2_xboole_0(A_14,B_15)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_1519])).

tff(c_1670,plain,(
    ! [B_15,A_14] : k5_xboole_0(k4_xboole_0(B_15,A_14),A_14) = k2_xboole_0(A_14,B_15) ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_1624])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_257,plain,(
    ! [A_47,B_48] : k5_xboole_0(A_47,k3_xboole_0(A_47,B_48)) = k4_xboole_0(A_47,B_48) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_276,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,k3_xboole_0(A_1,B_2)) = k4_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_257])).

tff(c_1595,plain,(
    ! [A_1,B_2] : k5_xboole_0(k3_xboole_0(A_1,B_2),B_2) = k5_xboole_0(k1_xboole_0,k4_xboole_0(B_2,A_1)) ),
    inference(superposition,[status(thm),theory(equality)],[c_276,c_1519])).

tff(c_1662,plain,(
    ! [A_1,B_2] : k5_xboole_0(k3_xboole_0(A_1,B_2),B_2) = k4_xboole_0(B_2,A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_1595])).

tff(c_4963,plain,(
    ! [A_135,B_136,C_137] : k5_xboole_0(A_135,k5_xboole_0(k3_xboole_0(A_135,B_136),C_137)) = k5_xboole_0(k4_xboole_0(A_135,B_136),C_137) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_334])).

tff(c_5070,plain,(
    ! [A_1,B_2] : k5_xboole_0(k4_xboole_0(A_1,B_2),B_2) = k5_xboole_0(A_1,k4_xboole_0(B_2,A_1)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1662,c_4963])).

tff(c_5185,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1670,c_16,c_5070])).

tff(c_24179,plain,(
    ! [A_241,B_242] : k2_xboole_0(k1_tarski(A_241),k2_tarski(A_241,B_242)) = k2_tarski(A_241,B_242) ),
    inference(superposition,[status(thm),theory(equality)],[c_24149,c_5185])).

tff(c_28,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),k2_tarski('#skF_1','#skF_2')) != k2_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_24220,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24179,c_28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:42:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 12.27/5.84  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.27/5.85  
% 12.27/5.85  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.27/5.85  %$ r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 12.27/5.85  
% 12.27/5.85  %Foreground sorts:
% 12.27/5.85  
% 12.27/5.85  
% 12.27/5.85  %Background operators:
% 12.27/5.85  
% 12.27/5.85  
% 12.27/5.85  %Foreground operators:
% 12.27/5.85  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 12.27/5.85  tff(k1_tarski, type, k1_tarski: $i > $i).
% 12.27/5.85  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 12.27/5.85  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 12.27/5.85  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 12.27/5.85  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 12.27/5.85  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 12.27/5.85  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 12.27/5.85  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 12.27/5.85  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 12.27/5.85  tff('#skF_2', type, '#skF_2': $i).
% 12.27/5.85  tff('#skF_1', type, '#skF_1': $i).
% 12.27/5.85  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 12.27/5.85  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 12.27/5.85  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 12.27/5.85  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 12.27/5.85  
% 12.27/5.86  tff(f_37, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 12.27/5.86  tff(f_41, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 12.27/5.86  tff(f_53, axiom, (![A, B]: r1_tarski(k1_tarski(A), k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_zfmisc_1)).
% 12.27/5.86  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 12.27/5.86  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 12.27/5.86  tff(f_43, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 12.27/5.86  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 12.27/5.86  tff(f_39, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 12.27/5.86  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 12.27/5.86  tff(f_56, negated_conjecture, ~(![A, B]: (k2_xboole_0(k1_tarski(A), k2_tarski(A, B)) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_zfmisc_1)).
% 12.27/5.86  tff(c_10, plain, (![A_9]: (k5_xboole_0(A_9, k1_xboole_0)=A_9)), inference(cnfTransformation, [status(thm)], [f_37])).
% 12.27/5.86  tff(c_14, plain, (![A_13]: (k5_xboole_0(A_13, A_13)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 12.27/5.86  tff(c_26, plain, (![A_26, B_27]: (r1_tarski(k1_tarski(A_26), k2_tarski(A_26, B_27)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 12.27/5.86  tff(c_199, plain, (![A_39, B_40]: (k3_xboole_0(A_39, B_40)=A_39 | ~r1_tarski(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_35])).
% 12.27/5.86  tff(c_813, plain, (![A_70, B_71]: (k3_xboole_0(k1_tarski(A_70), k2_tarski(A_70, B_71))=k1_tarski(A_70))), inference(resolution, [status(thm)], [c_26, c_199])).
% 12.27/5.86  tff(c_6, plain, (![A_5, B_6]: (k5_xboole_0(A_5, k3_xboole_0(A_5, B_6))=k4_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 12.27/5.86  tff(c_819, plain, (![A_70, B_71]: (k5_xboole_0(k1_tarski(A_70), k1_tarski(A_70))=k4_xboole_0(k1_tarski(A_70), k2_tarski(A_70, B_71)))), inference(superposition, [status(thm), theory('equality')], [c_813, c_6])).
% 12.27/5.86  tff(c_928, plain, (![A_75, B_76]: (k4_xboole_0(k1_tarski(A_75), k2_tarski(A_75, B_76))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_819])).
% 12.27/5.86  tff(c_16, plain, (![A_14, B_15]: (k5_xboole_0(A_14, k4_xboole_0(B_15, A_14))=k2_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_43])).
% 12.27/5.86  tff(c_933, plain, (![A_75, B_76]: (k2_xboole_0(k2_tarski(A_75, B_76), k1_tarski(A_75))=k5_xboole_0(k2_tarski(A_75, B_76), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_928, c_16])).
% 12.27/5.86  tff(c_24149, plain, (![A_241, B_242]: (k2_xboole_0(k2_tarski(A_241, B_242), k1_tarski(A_241))=k2_tarski(A_241, B_242))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_933])).
% 12.27/5.86  tff(c_69, plain, (![B_34, A_35]: (k5_xboole_0(B_34, A_35)=k5_xboole_0(A_35, B_34))), inference(cnfTransformation, [status(thm)], [f_29])).
% 12.27/5.86  tff(c_85, plain, (![A_35]: (k5_xboole_0(k1_xboole_0, A_35)=A_35)), inference(superposition, [status(thm), theory('equality')], [c_69, c_10])).
% 12.27/5.86  tff(c_4, plain, (![B_4, A_3]: (k5_xboole_0(B_4, A_3)=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 12.27/5.86  tff(c_334, plain, (![A_54, B_55, C_56]: (k5_xboole_0(k5_xboole_0(A_54, B_55), C_56)=k5_xboole_0(A_54, k5_xboole_0(B_55, C_56)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 12.27/5.86  tff(c_945, plain, (![A_79, A_77, B_78]: (k5_xboole_0(A_79, k5_xboole_0(A_77, B_78))=k5_xboole_0(A_77, k5_xboole_0(B_78, A_79)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_334])).
% 12.27/5.86  tff(c_1519, plain, (![A_87, A_88]: (k5_xboole_0(k1_xboole_0, k5_xboole_0(A_87, A_88))=k5_xboole_0(A_88, A_87))), inference(superposition, [status(thm), theory('equality')], [c_85, c_945])).
% 12.27/5.86  tff(c_1624, plain, (![B_15, A_14]: (k5_xboole_0(k4_xboole_0(B_15, A_14), A_14)=k5_xboole_0(k1_xboole_0, k2_xboole_0(A_14, B_15)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_1519])).
% 12.27/5.86  tff(c_1670, plain, (![B_15, A_14]: (k5_xboole_0(k4_xboole_0(B_15, A_14), A_14)=k2_xboole_0(A_14, B_15))), inference(demodulation, [status(thm), theory('equality')], [c_85, c_1624])).
% 12.27/5.86  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 12.27/5.86  tff(c_257, plain, (![A_47, B_48]: (k5_xboole_0(A_47, k3_xboole_0(A_47, B_48))=k4_xboole_0(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_31])).
% 12.27/5.86  tff(c_276, plain, (![B_2, A_1]: (k5_xboole_0(B_2, k3_xboole_0(A_1, B_2))=k4_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_257])).
% 12.27/5.86  tff(c_1595, plain, (![A_1, B_2]: (k5_xboole_0(k3_xboole_0(A_1, B_2), B_2)=k5_xboole_0(k1_xboole_0, k4_xboole_0(B_2, A_1)))), inference(superposition, [status(thm), theory('equality')], [c_276, c_1519])).
% 12.27/5.86  tff(c_1662, plain, (![A_1, B_2]: (k5_xboole_0(k3_xboole_0(A_1, B_2), B_2)=k4_xboole_0(B_2, A_1))), inference(demodulation, [status(thm), theory('equality')], [c_85, c_1595])).
% 12.27/5.86  tff(c_4963, plain, (![A_135, B_136, C_137]: (k5_xboole_0(A_135, k5_xboole_0(k3_xboole_0(A_135, B_136), C_137))=k5_xboole_0(k4_xboole_0(A_135, B_136), C_137))), inference(superposition, [status(thm), theory('equality')], [c_6, c_334])).
% 12.27/5.86  tff(c_5070, plain, (![A_1, B_2]: (k5_xboole_0(k4_xboole_0(A_1, B_2), B_2)=k5_xboole_0(A_1, k4_xboole_0(B_2, A_1)))), inference(superposition, [status(thm), theory('equality')], [c_1662, c_4963])).
% 12.27/5.86  tff(c_5185, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(demodulation, [status(thm), theory('equality')], [c_1670, c_16, c_5070])).
% 12.27/5.86  tff(c_24179, plain, (![A_241, B_242]: (k2_xboole_0(k1_tarski(A_241), k2_tarski(A_241, B_242))=k2_tarski(A_241, B_242))), inference(superposition, [status(thm), theory('equality')], [c_24149, c_5185])).
% 12.27/5.86  tff(c_28, plain, (k2_xboole_0(k1_tarski('#skF_1'), k2_tarski('#skF_1', '#skF_2'))!=k2_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_56])).
% 12.27/5.86  tff(c_24220, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24179, c_28])).
% 12.27/5.86  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.27/5.86  
% 12.27/5.86  Inference rules
% 12.27/5.86  ----------------------
% 12.27/5.86  #Ref     : 0
% 12.27/5.86  #Sup     : 6187
% 12.27/5.86  #Fact    : 0
% 12.27/5.86  #Define  : 0
% 12.27/5.86  #Split   : 0
% 12.27/5.86  #Chain   : 0
% 12.27/5.86  #Close   : 0
% 12.27/5.86  
% 12.27/5.86  Ordering : KBO
% 12.27/5.86  
% 12.27/5.86  Simplification rules
% 12.27/5.86  ----------------------
% 12.27/5.86  #Subsume      : 406
% 12.27/5.86  #Demod        : 6369
% 12.27/5.86  #Tautology    : 2409
% 12.27/5.86  #SimpNegUnit  : 0
% 12.27/5.86  #BackRed      : 2
% 12.27/5.86  
% 12.27/5.86  #Partial instantiations: 0
% 12.27/5.86  #Strategies tried      : 1
% 12.27/5.86  
% 12.27/5.86  Timing (in seconds)
% 12.27/5.86  ----------------------
% 12.27/5.87  Preprocessing        : 0.31
% 12.27/5.87  Parsing              : 0.17
% 12.27/5.87  CNF conversion       : 0.02
% 12.27/5.87  Main loop            : 4.77
% 12.27/5.87  Inferencing          : 0.72
% 12.27/5.87  Reduction            : 3.24
% 12.27/5.87  Demodulation         : 3.05
% 12.27/5.87  BG Simplification    : 0.12
% 12.27/5.87  Subsumption          : 0.52
% 12.27/5.87  Abstraction          : 0.19
% 12.27/5.87  MUC search           : 0.00
% 12.27/5.87  Cooper               : 0.00
% 12.27/5.87  Total                : 5.11
% 12.27/5.87  Index Insertion      : 0.00
% 12.27/5.87  Index Deletion       : 0.00
% 12.27/5.87  Index Matching       : 0.00
% 12.27/5.87  BG Taut test         : 0.00
%------------------------------------------------------------------------------
