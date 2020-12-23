%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:00 EST 2020

% Result     : Theorem 3.88s
% Output     : CNFRefutation 3.88s
% Verified   : 
% Statistics : Number of formulae       :   47 (  58 expanded)
%              Number of leaves         :   20 (  27 expanded)
%              Depth                    :   12
%              Number of atoms          :   41 (  52 expanded)
%              Number of equality atoms :   34 (  45 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(f_33,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_41,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_31,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k4_xboole_0(B,A))
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_xboole_1)).

tff(f_48,negated_conjecture,(
    ~ ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(c_8,plain,(
    ! [A_7,B_8] : k2_xboole_0(A_7,k3_xboole_0(A_7,B_8)) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_18,plain,(
    ! [A_16,B_17] : k4_xboole_0(A_16,k3_xboole_0(A_16,B_17)) = k4_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_14,plain,(
    ! [A_13] : k4_xboole_0(A_13,k1_xboole_0) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_6,plain,(
    ! [A_5,B_6] : r1_tarski(k3_xboole_0(A_5,B_6),A_5) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_161,plain,(
    ! [A_33,B_34] : k4_xboole_0(k2_xboole_0(A_33,B_34),B_34) = k4_xboole_0(A_33,B_34) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_186,plain,(
    ! [A_1,B_2] : k4_xboole_0(k2_xboole_0(A_1,B_2),A_1) = k4_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_161])).

tff(c_12,plain,(
    ! [A_11,B_12] : k2_xboole_0(A_11,k4_xboole_0(B_12,A_11)) = k2_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_771,plain,(
    ! [A_55,B_56] : k4_xboole_0(k2_xboole_0(A_55,B_56),A_55) = k4_xboole_0(B_56,A_55) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_161])).

tff(c_803,plain,(
    ! [B_12,A_11] : k4_xboole_0(k4_xboole_0(B_12,A_11),A_11) = k4_xboole_0(k2_xboole_0(A_11,B_12),A_11) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_771])).

tff(c_2125,plain,(
    ! [B_89,A_90] : k4_xboole_0(k4_xboole_0(B_89,A_90),A_90) = k4_xboole_0(B_89,A_90) ),
    inference(demodulation,[status(thm),theory(equality)],[c_186,c_803])).

tff(c_281,plain,(
    ! [A_37,B_38] : k4_xboole_0(A_37,k3_xboole_0(A_37,B_38)) = k4_xboole_0(A_37,B_38) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_10,plain,(
    ! [A_9,B_10] :
      ( k1_xboole_0 = A_9
      | ~ r1_tarski(A_9,k4_xboole_0(B_10,A_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_287,plain,(
    ! [A_37,B_38] :
      ( k3_xboole_0(A_37,B_38) = k1_xboole_0
      | ~ r1_tarski(k3_xboole_0(A_37,B_38),k4_xboole_0(A_37,B_38)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_281,c_10])).

tff(c_2153,plain,(
    ! [B_89,A_90] :
      ( k3_xboole_0(k4_xboole_0(B_89,A_90),A_90) = k1_xboole_0
      | ~ r1_tarski(k3_xboole_0(k4_xboole_0(B_89,A_90),A_90),k4_xboole_0(B_89,A_90)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2125,c_287])).

tff(c_2249,plain,(
    ! [A_91,B_92] : k3_xboole_0(A_91,k4_xboole_0(B_92,A_91)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_4,c_2153])).

tff(c_2275,plain,(
    ! [A_91,B_92] : k4_xboole_0(A_91,k4_xboole_0(B_92,A_91)) = k4_xboole_0(A_91,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_2249,c_18])).

tff(c_2343,plain,(
    ! [A_91,B_92] : k4_xboole_0(A_91,k4_xboole_0(B_92,A_91)) = A_91 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_2275])).

tff(c_302,plain,(
    ! [A_39,B_40] : k2_xboole_0(A_39,k4_xboole_0(B_40,A_39)) = k2_xboole_0(A_39,B_40) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_16,plain,(
    ! [A_14,B_15] : k4_xboole_0(k2_xboole_0(A_14,B_15),B_15) = k4_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_312,plain,(
    ! [A_39,B_40] : k4_xboole_0(k2_xboole_0(A_39,B_40),k4_xboole_0(B_40,A_39)) = k4_xboole_0(A_39,k4_xboole_0(B_40,A_39)) ),
    inference(superposition,[status(thm),theory(equality)],[c_302,c_16])).

tff(c_3081,plain,(
    ! [A_105,B_106] : k4_xboole_0(k2_xboole_0(A_105,B_106),k4_xboole_0(B_106,A_105)) = A_105 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2343,c_312])).

tff(c_3195,plain,(
    ! [A_16,B_17] : k4_xboole_0(k2_xboole_0(k3_xboole_0(A_16,B_17),A_16),k4_xboole_0(A_16,B_17)) = k3_xboole_0(A_16,B_17) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_3081])).

tff(c_3249,plain,(
    ! [A_16,B_17] : k4_xboole_0(A_16,k4_xboole_0(A_16,B_17)) = k3_xboole_0(A_16,B_17) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_2,c_3195])).

tff(c_20,plain,(
    k4_xboole_0('#skF_1',k4_xboole_0('#skF_1','#skF_2')) != k3_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_4472,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3249,c_20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:55:24 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.88/1.74  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.88/1.75  
% 3.88/1.75  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.88/1.75  %$ r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1
% 3.88/1.75  
% 3.88/1.75  %Foreground sorts:
% 3.88/1.75  
% 3.88/1.75  
% 3.88/1.75  %Background operators:
% 3.88/1.75  
% 3.88/1.75  
% 3.88/1.75  %Foreground operators:
% 3.88/1.75  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.88/1.75  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.88/1.75  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.88/1.75  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.88/1.75  tff('#skF_2', type, '#skF_2': $i).
% 3.88/1.75  tff('#skF_1', type, '#skF_1': $i).
% 3.88/1.75  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.88/1.75  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.88/1.75  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.88/1.75  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.88/1.75  
% 3.88/1.76  tff(f_33, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_xboole_1)).
% 3.88/1.76  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 3.88/1.76  tff(f_45, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 3.88/1.76  tff(f_41, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 3.88/1.76  tff(f_31, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 3.88/1.76  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.88/1.76  tff(f_43, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_xboole_1)).
% 3.88/1.76  tff(f_39, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 3.88/1.76  tff(f_37, axiom, (![A, B]: (r1_tarski(A, k4_xboole_0(B, A)) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_xboole_1)).
% 3.88/1.76  tff(f_48, negated_conjecture, ~(![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.88/1.76  tff(c_8, plain, (![A_7, B_8]: (k2_xboole_0(A_7, k3_xboole_0(A_7, B_8))=A_7)), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.88/1.76  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.88/1.76  tff(c_18, plain, (![A_16, B_17]: (k4_xboole_0(A_16, k3_xboole_0(A_16, B_17))=k4_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.88/1.76  tff(c_14, plain, (![A_13]: (k4_xboole_0(A_13, k1_xboole_0)=A_13)), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.88/1.76  tff(c_6, plain, (![A_5, B_6]: (r1_tarski(k3_xboole_0(A_5, B_6), A_5))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.88/1.76  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(B_4, A_3)=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.88/1.76  tff(c_161, plain, (![A_33, B_34]: (k4_xboole_0(k2_xboole_0(A_33, B_34), B_34)=k4_xboole_0(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.88/1.76  tff(c_186, plain, (![A_1, B_2]: (k4_xboole_0(k2_xboole_0(A_1, B_2), A_1)=k4_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_161])).
% 3.88/1.76  tff(c_12, plain, (![A_11, B_12]: (k2_xboole_0(A_11, k4_xboole_0(B_12, A_11))=k2_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.88/1.76  tff(c_771, plain, (![A_55, B_56]: (k4_xboole_0(k2_xboole_0(A_55, B_56), A_55)=k4_xboole_0(B_56, A_55))), inference(superposition, [status(thm), theory('equality')], [c_2, c_161])).
% 3.88/1.76  tff(c_803, plain, (![B_12, A_11]: (k4_xboole_0(k4_xboole_0(B_12, A_11), A_11)=k4_xboole_0(k2_xboole_0(A_11, B_12), A_11))), inference(superposition, [status(thm), theory('equality')], [c_12, c_771])).
% 3.88/1.76  tff(c_2125, plain, (![B_89, A_90]: (k4_xboole_0(k4_xboole_0(B_89, A_90), A_90)=k4_xboole_0(B_89, A_90))), inference(demodulation, [status(thm), theory('equality')], [c_186, c_803])).
% 3.88/1.76  tff(c_281, plain, (![A_37, B_38]: (k4_xboole_0(A_37, k3_xboole_0(A_37, B_38))=k4_xboole_0(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.88/1.76  tff(c_10, plain, (![A_9, B_10]: (k1_xboole_0=A_9 | ~r1_tarski(A_9, k4_xboole_0(B_10, A_9)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.88/1.76  tff(c_287, plain, (![A_37, B_38]: (k3_xboole_0(A_37, B_38)=k1_xboole_0 | ~r1_tarski(k3_xboole_0(A_37, B_38), k4_xboole_0(A_37, B_38)))), inference(superposition, [status(thm), theory('equality')], [c_281, c_10])).
% 3.88/1.76  tff(c_2153, plain, (![B_89, A_90]: (k3_xboole_0(k4_xboole_0(B_89, A_90), A_90)=k1_xboole_0 | ~r1_tarski(k3_xboole_0(k4_xboole_0(B_89, A_90), A_90), k4_xboole_0(B_89, A_90)))), inference(superposition, [status(thm), theory('equality')], [c_2125, c_287])).
% 3.88/1.76  tff(c_2249, plain, (![A_91, B_92]: (k3_xboole_0(A_91, k4_xboole_0(B_92, A_91))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_4, c_2153])).
% 3.88/1.76  tff(c_2275, plain, (![A_91, B_92]: (k4_xboole_0(A_91, k4_xboole_0(B_92, A_91))=k4_xboole_0(A_91, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_2249, c_18])).
% 3.88/1.76  tff(c_2343, plain, (![A_91, B_92]: (k4_xboole_0(A_91, k4_xboole_0(B_92, A_91))=A_91)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_2275])).
% 3.88/1.76  tff(c_302, plain, (![A_39, B_40]: (k2_xboole_0(A_39, k4_xboole_0(B_40, A_39))=k2_xboole_0(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.88/1.76  tff(c_16, plain, (![A_14, B_15]: (k4_xboole_0(k2_xboole_0(A_14, B_15), B_15)=k4_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.88/1.76  tff(c_312, plain, (![A_39, B_40]: (k4_xboole_0(k2_xboole_0(A_39, B_40), k4_xboole_0(B_40, A_39))=k4_xboole_0(A_39, k4_xboole_0(B_40, A_39)))), inference(superposition, [status(thm), theory('equality')], [c_302, c_16])).
% 3.88/1.76  tff(c_3081, plain, (![A_105, B_106]: (k4_xboole_0(k2_xboole_0(A_105, B_106), k4_xboole_0(B_106, A_105))=A_105)), inference(demodulation, [status(thm), theory('equality')], [c_2343, c_312])).
% 3.88/1.76  tff(c_3195, plain, (![A_16, B_17]: (k4_xboole_0(k2_xboole_0(k3_xboole_0(A_16, B_17), A_16), k4_xboole_0(A_16, B_17))=k3_xboole_0(A_16, B_17))), inference(superposition, [status(thm), theory('equality')], [c_18, c_3081])).
% 3.88/1.76  tff(c_3249, plain, (![A_16, B_17]: (k4_xboole_0(A_16, k4_xboole_0(A_16, B_17))=k3_xboole_0(A_16, B_17))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_2, c_3195])).
% 3.88/1.76  tff(c_20, plain, (k4_xboole_0('#skF_1', k4_xboole_0('#skF_1', '#skF_2'))!=k3_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.88/1.76  tff(c_4472, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3249, c_20])).
% 3.88/1.76  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.88/1.76  
% 3.88/1.76  Inference rules
% 3.88/1.76  ----------------------
% 3.88/1.76  #Ref     : 0
% 3.88/1.76  #Sup     : 1109
% 3.88/1.76  #Fact    : 0
% 3.88/1.76  #Define  : 0
% 3.88/1.76  #Split   : 0
% 3.88/1.76  #Chain   : 0
% 3.88/1.76  #Close   : 0
% 3.88/1.76  
% 3.88/1.76  Ordering : KBO
% 3.88/1.76  
% 3.88/1.76  Simplification rules
% 3.88/1.76  ----------------------
% 3.88/1.76  #Subsume      : 31
% 3.88/1.76  #Demod        : 1411
% 3.88/1.76  #Tautology    : 889
% 3.88/1.76  #SimpNegUnit  : 0
% 3.88/1.76  #BackRed      : 3
% 3.88/1.76  
% 3.88/1.76  #Partial instantiations: 0
% 3.88/1.76  #Strategies tried      : 1
% 3.88/1.76  
% 3.88/1.76  Timing (in seconds)
% 3.88/1.76  ----------------------
% 3.88/1.77  Preprocessing        : 0.24
% 3.88/1.77  Parsing              : 0.14
% 3.88/1.77  CNF conversion       : 0.02
% 3.88/1.77  Main loop            : 0.69
% 3.88/1.77  Inferencing          : 0.21
% 3.88/1.77  Reduction            : 0.34
% 3.88/1.77  Demodulation         : 0.30
% 3.88/1.77  BG Simplification    : 0.02
% 3.88/1.77  Subsumption          : 0.08
% 3.88/1.77  Abstraction          : 0.03
% 3.88/1.77  MUC search           : 0.00
% 3.88/1.77  Cooper               : 0.00
% 3.88/1.77  Total                : 0.96
% 3.88/1.77  Index Insertion      : 0.00
% 3.88/1.77  Index Deletion       : 0.00
% 3.88/1.77  Index Matching       : 0.00
% 3.88/1.77  BG Taut test         : 0.00
%------------------------------------------------------------------------------
