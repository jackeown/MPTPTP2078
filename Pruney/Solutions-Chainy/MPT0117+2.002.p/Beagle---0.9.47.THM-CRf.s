%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:29 EST 2020

% Result     : Theorem 2.99s
% Output     : CNFRefutation 2.99s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 232 expanded)
%              Number of leaves         :   24 (  87 expanded)
%              Depth                    :   17
%              Number of atoms          :   67 ( 256 expanded)
%              Number of equality atoms :   52 ( 187 expanded)
%              Maximal formula depth    :    7 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(f_56,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r1_tarski(A,B)
          & r1_tarski(C,B) )
       => r1_tarski(k5_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t110_xboole_1)).

tff(f_43,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_39,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_47,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_49,axiom,(
    ! [A,B,C] : k4_xboole_0(k5_xboole_0(A,B),C) = k2_xboole_0(k4_xboole_0(A,k2_xboole_0(B,C)),k4_xboole_0(B,k2_xboole_0(A,C))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(c_24,plain,(
    ~ r1_tarski(k5_xboole_0('#skF_1','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_16,plain,(
    ! [A_14] : k5_xboole_0(A_14,k1_xboole_0) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_12,plain,(
    ! [A_11] : r1_tarski(k1_xboole_0,A_11) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_131,plain,(
    ! [A_33,B_34] :
      ( k3_xboole_0(A_33,B_34) = A_33
      | ~ r1_tarski(A_33,B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_152,plain,(
    ! [A_35] : k3_xboole_0(k1_xboole_0,A_35) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12,c_131])).

tff(c_170,plain,(
    ! [B_4] : k3_xboole_0(B_4,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_152])).

tff(c_219,plain,(
    ! [B_38] : k3_xboole_0(B_38,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_152])).

tff(c_8,plain,(
    ! [A_7,B_8] : k5_xboole_0(A_7,k3_xboole_0(A_7,B_8)) = k4_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_224,plain,(
    ! [B_38] : k5_xboole_0(B_38,k1_xboole_0) = k4_xboole_0(B_38,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_219,c_8])).

tff(c_256,plain,(
    ! [B_38] : k4_xboole_0(B_38,k1_xboole_0) = B_38 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_224])).

tff(c_514,plain,(
    ! [A_51,B_52] : k4_xboole_0(A_51,k4_xboole_0(A_51,B_52)) = k3_xboole_0(A_51,B_52) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_539,plain,(
    ! [B_38] : k4_xboole_0(B_38,B_38) = k3_xboole_0(B_38,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_256,c_514])).

tff(c_552,plain,(
    ! [B_38] : k4_xboole_0(B_38,B_38) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_170,c_539])).

tff(c_6,plain,(
    ! [A_5] : k3_xboole_0(A_5,A_5) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_191,plain,(
    ! [A_36,B_37] : k5_xboole_0(A_36,k3_xboole_0(A_36,B_37)) = k4_xboole_0(A_36,B_37) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_215,plain,(
    ! [A_5] : k5_xboole_0(A_5,A_5) = k4_xboole_0(A_5,A_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_191])).

tff(c_26,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_150,plain,(
    k3_xboole_0('#skF_3','#skF_2') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_26,c_131])).

tff(c_203,plain,(
    k5_xboole_0('#skF_3','#skF_3') = k4_xboole_0('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_150,c_191])).

tff(c_327,plain,(
    k4_xboole_0('#skF_3','#skF_2') = k4_xboole_0('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_215,c_203])).

tff(c_619,plain,(
    k4_xboole_0('#skF_3','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_552,c_327])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_149,plain,(
    ! [A_11] : k3_xboole_0(k1_xboole_0,A_11) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12,c_131])).

tff(c_206,plain,(
    ! [A_11] : k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,A_11) ),
    inference(superposition,[status(thm),theory(equality)],[c_149,c_191])).

tff(c_218,plain,(
    ! [A_11] : k4_xboole_0(k1_xboole_0,A_11) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_206])).

tff(c_347,plain,(
    ! [A_44,B_45] : k5_xboole_0(A_44,k4_xboole_0(B_45,A_44)) = k2_xboole_0(A_44,B_45) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_359,plain,(
    ! [A_11] : k5_xboole_0(A_11,k1_xboole_0) = k2_xboole_0(A_11,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_218,c_347])).

tff(c_363,plain,(
    ! [A_46] : k2_xboole_0(A_46,k1_xboole_0) = A_46 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_359])).

tff(c_392,plain,(
    ! [B_2] : k2_xboole_0(k1_xboole_0,B_2) = B_2 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_363])).

tff(c_28,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_151,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_28,c_131])).

tff(c_200,plain,(
    k5_xboole_0('#skF_1','#skF_1') = k4_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_151,c_191])).

tff(c_452,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k4_xboole_0('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_215,c_200])).

tff(c_555,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_552,c_452])).

tff(c_20,plain,(
    ! [A_17,B_18] : k5_xboole_0(A_17,k4_xboole_0(B_18,A_17)) = k2_xboole_0(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_626,plain,(
    k5_xboole_0('#skF_2',k1_xboole_0) = k2_xboole_0('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_619,c_20])).

tff(c_630,plain,(
    k2_xboole_0('#skF_3','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_16,c_626])).

tff(c_596,plain,(
    k5_xboole_0('#skF_2',k1_xboole_0) = k2_xboole_0('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_555,c_20])).

tff(c_600,plain,(
    k2_xboole_0('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_16,c_596])).

tff(c_768,plain,(
    ! [A_57,B_58,C_59] : k2_xboole_0(k4_xboole_0(A_57,k2_xboole_0(B_58,C_59)),k4_xboole_0(B_58,k2_xboole_0(A_57,C_59))) = k4_xboole_0(k5_xboole_0(A_57,B_58),C_59) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1255,plain,(
    ! [B_70] : k2_xboole_0(k4_xboole_0('#skF_1',k2_xboole_0(B_70,'#skF_2')),k4_xboole_0(B_70,'#skF_2')) = k4_xboole_0(k5_xboole_0('#skF_1',B_70),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_600,c_768])).

tff(c_1305,plain,(
    k2_xboole_0(k4_xboole_0('#skF_1','#skF_2'),k4_xboole_0('#skF_3','#skF_2')) = k4_xboole_0(k5_xboole_0('#skF_1','#skF_3'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_630,c_1255])).

tff(c_1349,plain,(
    k4_xboole_0(k5_xboole_0('#skF_1','#skF_3'),'#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_619,c_392,c_555,c_1305])).

tff(c_1366,plain,(
    k2_xboole_0('#skF_2',k5_xboole_0('#skF_1','#skF_3')) = k5_xboole_0('#skF_2',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1349,c_20])).

tff(c_1371,plain,(
    k2_xboole_0('#skF_2',k5_xboole_0('#skF_1','#skF_3')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_1366])).

tff(c_49,plain,(
    ! [B_27,A_28] : k2_xboole_0(B_27,A_28) = k2_xboole_0(A_28,B_27) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_18,plain,(
    ! [A_15,B_16] : r1_tarski(A_15,k2_xboole_0(A_15,B_16)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_64,plain,(
    ! [A_28,B_27] : r1_tarski(A_28,k2_xboole_0(B_27,A_28)) ),
    inference(superposition,[status(thm),theory(equality)],[c_49,c_18])).

tff(c_1415,plain,(
    r1_tarski(k5_xboole_0('#skF_1','#skF_3'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1371,c_64])).

tff(c_1426,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_1415])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:55:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.99/1.48  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.99/1.49  
% 2.99/1.49  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.99/1.49  %$ r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.99/1.49  
% 2.99/1.49  %Foreground sorts:
% 2.99/1.49  
% 2.99/1.49  
% 2.99/1.49  %Background operators:
% 2.99/1.49  
% 2.99/1.49  
% 2.99/1.49  %Foreground operators:
% 2.99/1.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.99/1.49  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.99/1.49  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.99/1.49  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.99/1.49  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.99/1.49  tff('#skF_2', type, '#skF_2': $i).
% 2.99/1.49  tff('#skF_3', type, '#skF_3': $i).
% 2.99/1.49  tff('#skF_1', type, '#skF_1': $i).
% 2.99/1.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.99/1.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.99/1.49  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.99/1.49  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.99/1.49  
% 2.99/1.50  tff(f_56, negated_conjecture, ~(![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k5_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t110_xboole_1)).
% 2.99/1.50  tff(f_43, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 2.99/1.50  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.99/1.50  tff(f_39, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.99/1.50  tff(f_37, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.99/1.50  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.99/1.50  tff(f_41, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.99/1.50  tff(f_31, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 2.99/1.50  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.99/1.50  tff(f_47, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 2.99/1.50  tff(f_49, axiom, (![A, B, C]: (k4_xboole_0(k5_xboole_0(A, B), C) = k2_xboole_0(k4_xboole_0(A, k2_xboole_0(B, C)), k4_xboole_0(B, k2_xboole_0(A, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t99_xboole_1)).
% 2.99/1.50  tff(f_45, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.99/1.50  tff(c_24, plain, (~r1_tarski(k5_xboole_0('#skF_1', '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.99/1.50  tff(c_16, plain, (![A_14]: (k5_xboole_0(A_14, k1_xboole_0)=A_14)), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.99/1.50  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(B_4, A_3)=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.99/1.50  tff(c_12, plain, (![A_11]: (r1_tarski(k1_xboole_0, A_11))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.99/1.50  tff(c_131, plain, (![A_33, B_34]: (k3_xboole_0(A_33, B_34)=A_33 | ~r1_tarski(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.99/1.50  tff(c_152, plain, (![A_35]: (k3_xboole_0(k1_xboole_0, A_35)=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_131])).
% 2.99/1.50  tff(c_170, plain, (![B_4]: (k3_xboole_0(B_4, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_4, c_152])).
% 2.99/1.50  tff(c_219, plain, (![B_38]: (k3_xboole_0(B_38, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_4, c_152])).
% 2.99/1.50  tff(c_8, plain, (![A_7, B_8]: (k5_xboole_0(A_7, k3_xboole_0(A_7, B_8))=k4_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.99/1.50  tff(c_224, plain, (![B_38]: (k5_xboole_0(B_38, k1_xboole_0)=k4_xboole_0(B_38, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_219, c_8])).
% 2.99/1.50  tff(c_256, plain, (![B_38]: (k4_xboole_0(B_38, k1_xboole_0)=B_38)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_224])).
% 2.99/1.50  tff(c_514, plain, (![A_51, B_52]: (k4_xboole_0(A_51, k4_xboole_0(A_51, B_52))=k3_xboole_0(A_51, B_52))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.99/1.50  tff(c_539, plain, (![B_38]: (k4_xboole_0(B_38, B_38)=k3_xboole_0(B_38, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_256, c_514])).
% 2.99/1.50  tff(c_552, plain, (![B_38]: (k4_xboole_0(B_38, B_38)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_170, c_539])).
% 2.99/1.50  tff(c_6, plain, (![A_5]: (k3_xboole_0(A_5, A_5)=A_5)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.99/1.50  tff(c_191, plain, (![A_36, B_37]: (k5_xboole_0(A_36, k3_xboole_0(A_36, B_37))=k4_xboole_0(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.99/1.51  tff(c_215, plain, (![A_5]: (k5_xboole_0(A_5, A_5)=k4_xboole_0(A_5, A_5))), inference(superposition, [status(thm), theory('equality')], [c_6, c_191])).
% 2.99/1.51  tff(c_26, plain, (r1_tarski('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.99/1.51  tff(c_150, plain, (k3_xboole_0('#skF_3', '#skF_2')='#skF_3'), inference(resolution, [status(thm)], [c_26, c_131])).
% 2.99/1.51  tff(c_203, plain, (k5_xboole_0('#skF_3', '#skF_3')=k4_xboole_0('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_150, c_191])).
% 2.99/1.51  tff(c_327, plain, (k4_xboole_0('#skF_3', '#skF_2')=k4_xboole_0('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_215, c_203])).
% 2.99/1.51  tff(c_619, plain, (k4_xboole_0('#skF_3', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_552, c_327])).
% 2.99/1.51  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.99/1.51  tff(c_149, plain, (![A_11]: (k3_xboole_0(k1_xboole_0, A_11)=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_131])).
% 2.99/1.51  tff(c_206, plain, (![A_11]: (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, A_11))), inference(superposition, [status(thm), theory('equality')], [c_149, c_191])).
% 2.99/1.51  tff(c_218, plain, (![A_11]: (k4_xboole_0(k1_xboole_0, A_11)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_206])).
% 2.99/1.51  tff(c_347, plain, (![A_44, B_45]: (k5_xboole_0(A_44, k4_xboole_0(B_45, A_44))=k2_xboole_0(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.99/1.51  tff(c_359, plain, (![A_11]: (k5_xboole_0(A_11, k1_xboole_0)=k2_xboole_0(A_11, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_218, c_347])).
% 2.99/1.51  tff(c_363, plain, (![A_46]: (k2_xboole_0(A_46, k1_xboole_0)=A_46)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_359])).
% 2.99/1.51  tff(c_392, plain, (![B_2]: (k2_xboole_0(k1_xboole_0, B_2)=B_2)), inference(superposition, [status(thm), theory('equality')], [c_2, c_363])).
% 2.99/1.51  tff(c_28, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.99/1.51  tff(c_151, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(resolution, [status(thm)], [c_28, c_131])).
% 2.99/1.51  tff(c_200, plain, (k5_xboole_0('#skF_1', '#skF_1')=k4_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_151, c_191])).
% 2.99/1.51  tff(c_452, plain, (k4_xboole_0('#skF_1', '#skF_2')=k4_xboole_0('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_215, c_200])).
% 2.99/1.51  tff(c_555, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_552, c_452])).
% 2.99/1.51  tff(c_20, plain, (![A_17, B_18]: (k5_xboole_0(A_17, k4_xboole_0(B_18, A_17))=k2_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.99/1.51  tff(c_626, plain, (k5_xboole_0('#skF_2', k1_xboole_0)=k2_xboole_0('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_619, c_20])).
% 2.99/1.51  tff(c_630, plain, (k2_xboole_0('#skF_3', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2, c_16, c_626])).
% 2.99/1.51  tff(c_596, plain, (k5_xboole_0('#skF_2', k1_xboole_0)=k2_xboole_0('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_555, c_20])).
% 2.99/1.51  tff(c_600, plain, (k2_xboole_0('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2, c_16, c_596])).
% 2.99/1.51  tff(c_768, plain, (![A_57, B_58, C_59]: (k2_xboole_0(k4_xboole_0(A_57, k2_xboole_0(B_58, C_59)), k4_xboole_0(B_58, k2_xboole_0(A_57, C_59)))=k4_xboole_0(k5_xboole_0(A_57, B_58), C_59))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.99/1.51  tff(c_1255, plain, (![B_70]: (k2_xboole_0(k4_xboole_0('#skF_1', k2_xboole_0(B_70, '#skF_2')), k4_xboole_0(B_70, '#skF_2'))=k4_xboole_0(k5_xboole_0('#skF_1', B_70), '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_600, c_768])).
% 2.99/1.51  tff(c_1305, plain, (k2_xboole_0(k4_xboole_0('#skF_1', '#skF_2'), k4_xboole_0('#skF_3', '#skF_2'))=k4_xboole_0(k5_xboole_0('#skF_1', '#skF_3'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_630, c_1255])).
% 2.99/1.51  tff(c_1349, plain, (k4_xboole_0(k5_xboole_0('#skF_1', '#skF_3'), '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_619, c_392, c_555, c_1305])).
% 2.99/1.51  tff(c_1366, plain, (k2_xboole_0('#skF_2', k5_xboole_0('#skF_1', '#skF_3'))=k5_xboole_0('#skF_2', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1349, c_20])).
% 2.99/1.51  tff(c_1371, plain, (k2_xboole_0('#skF_2', k5_xboole_0('#skF_1', '#skF_3'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_16, c_1366])).
% 2.99/1.51  tff(c_49, plain, (![B_27, A_28]: (k2_xboole_0(B_27, A_28)=k2_xboole_0(A_28, B_27))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.99/1.51  tff(c_18, plain, (![A_15, B_16]: (r1_tarski(A_15, k2_xboole_0(A_15, B_16)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.99/1.51  tff(c_64, plain, (![A_28, B_27]: (r1_tarski(A_28, k2_xboole_0(B_27, A_28)))), inference(superposition, [status(thm), theory('equality')], [c_49, c_18])).
% 2.99/1.51  tff(c_1415, plain, (r1_tarski(k5_xboole_0('#skF_1', '#skF_3'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1371, c_64])).
% 2.99/1.51  tff(c_1426, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_1415])).
% 2.99/1.51  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.99/1.51  
% 2.99/1.51  Inference rules
% 2.99/1.51  ----------------------
% 2.99/1.51  #Ref     : 0
% 2.99/1.51  #Sup     : 356
% 2.99/1.51  #Fact    : 0
% 2.99/1.51  #Define  : 0
% 2.99/1.51  #Split   : 0
% 2.99/1.51  #Chain   : 0
% 2.99/1.51  #Close   : 0
% 2.99/1.51  
% 2.99/1.51  Ordering : KBO
% 2.99/1.51  
% 2.99/1.51  Simplification rules
% 2.99/1.51  ----------------------
% 2.99/1.51  #Subsume      : 0
% 2.99/1.51  #Demod        : 266
% 2.99/1.51  #Tautology    : 249
% 2.99/1.51  #SimpNegUnit  : 1
% 2.99/1.51  #BackRed      : 3
% 2.99/1.51  
% 2.99/1.51  #Partial instantiations: 0
% 2.99/1.51  #Strategies tried      : 1
% 2.99/1.51  
% 2.99/1.51  Timing (in seconds)
% 2.99/1.51  ----------------------
% 2.99/1.51  Preprocessing        : 0.28
% 2.99/1.51  Parsing              : 0.16
% 2.99/1.51  CNF conversion       : 0.02
% 2.99/1.51  Main loop            : 0.44
% 2.99/1.51  Inferencing          : 0.16
% 2.99/1.51  Reduction            : 0.18
% 2.99/1.51  Demodulation         : 0.15
% 2.99/1.51  BG Simplification    : 0.02
% 2.99/1.51  Subsumption          : 0.06
% 2.99/1.51  Abstraction          : 0.02
% 2.99/1.51  MUC search           : 0.00
% 2.99/1.51  Cooper               : 0.00
% 2.99/1.51  Total                : 0.75
% 2.99/1.51  Index Insertion      : 0.00
% 2.99/1.51  Index Deletion       : 0.00
% 2.99/1.51  Index Matching       : 0.00
% 2.99/1.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
