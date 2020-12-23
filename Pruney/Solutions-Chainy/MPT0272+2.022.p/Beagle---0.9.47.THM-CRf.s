%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:09 EST 2020

% Result     : Theorem 2.46s
% Output     : CNFRefutation 2.72s
% Verified   : 
% Statistics : Number of formulae       :   57 (  85 expanded)
%              Number of leaves         :   27 (  40 expanded)
%              Depth                    :   12
%              Number of atoms          :   57 (  86 expanded)
%              Number of equality atoms :   33 (  62 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(f_56,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_67,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),B) = k1_xboole_0
        | k4_xboole_0(k1_tarski(A),B) = k1_tarski(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_zfmisc_1)).

tff(f_35,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_39,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_45,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(c_161,plain,(
    ! [A_42,B_43] :
      ( r1_xboole_0(k1_tarski(A_42),B_43)
      | r2_hidden(A_42,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_14,plain,(
    ! [A_11,B_12] :
      ( k4_xboole_0(A_11,B_12) = A_11
      | ~ r1_xboole_0(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_385,plain,(
    ! [A_66,B_67] :
      ( k4_xboole_0(k1_tarski(A_66),B_67) = k1_tarski(A_66)
      | r2_hidden(A_66,B_67) ) ),
    inference(resolution,[status(thm)],[c_161,c_14])).

tff(c_34,plain,(
    k4_xboole_0(k1_tarski('#skF_1'),'#skF_2') != k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_428,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_385,c_34])).

tff(c_8,plain,(
    ! [A_7] : k3_xboole_0(A_7,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_12,plain,(
    ! [A_10] : k5_xboole_0(A_10,k1_xboole_0) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_190,plain,(
    ! [A_54,B_55] : k5_xboole_0(A_54,k3_xboole_0(A_54,B_55)) = k4_xboole_0(A_54,B_55) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_208,plain,(
    ! [A_7] : k5_xboole_0(A_7,k1_xboole_0) = k4_xboole_0(A_7,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_190])).

tff(c_213,plain,(
    ! [A_56] : k4_xboole_0(A_56,k1_xboole_0) = A_56 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_208])).

tff(c_10,plain,(
    ! [A_8,B_9] : k4_xboole_0(A_8,k4_xboole_0(A_8,B_9)) = k3_xboole_0(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_219,plain,(
    ! [A_56] : k4_xboole_0(A_56,A_56) = k3_xboole_0(A_56,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_213,c_10])).

tff(c_224,plain,(
    ! [A_56] : k4_xboole_0(A_56,A_56) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_219])).

tff(c_212,plain,(
    ! [A_7] : k4_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_208])).

tff(c_257,plain,(
    ! [A_58] : k4_xboole_0(A_58,A_58) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_219])).

tff(c_269,plain,(
    ! [A_58] : k4_xboole_0(A_58,k1_xboole_0) = k3_xboole_0(A_58,A_58) ),
    inference(superposition,[status(thm),theory(equality)],[c_257,c_10])).

tff(c_286,plain,(
    ! [A_59] : k3_xboole_0(A_59,A_59) = A_59 ),
    inference(demodulation,[status(thm),theory(equality)],[c_212,c_269])).

tff(c_4,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k3_xboole_0(A_3,B_4)) = k4_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_292,plain,(
    ! [A_59] : k5_xboole_0(A_59,A_59) = k4_xboole_0(A_59,A_59) ),
    inference(superposition,[status(thm),theory(equality)],[c_286,c_4])).

tff(c_313,plain,(
    ! [A_59] : k5_xboole_0(A_59,A_59) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_224,c_292])).

tff(c_18,plain,(
    ! [A_13] : k2_tarski(A_13,A_13) = k1_tarski(A_13) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_523,plain,(
    ! [A_73,B_74,C_75] :
      ( r1_tarski(k2_tarski(A_73,B_74),C_75)
      | ~ r2_hidden(B_74,C_75)
      | ~ r2_hidden(A_73,C_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_663,plain,(
    ! [A_84,C_85] :
      ( r1_tarski(k1_tarski(A_84),C_85)
      | ~ r2_hidden(A_84,C_85)
      | ~ r2_hidden(A_84,C_85) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_523])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( k3_xboole_0(A_5,B_6) = A_5
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_672,plain,(
    ! [A_86,C_87] :
      ( k3_xboole_0(k1_tarski(A_86),C_87) = k1_tarski(A_86)
      | ~ r2_hidden(A_86,C_87) ) ),
    inference(resolution,[status(thm)],[c_663,c_6])).

tff(c_695,plain,(
    ! [A_86,C_87] :
      ( k5_xboole_0(k1_tarski(A_86),k1_tarski(A_86)) = k4_xboole_0(k1_tarski(A_86),C_87)
      | ~ r2_hidden(A_86,C_87) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_672,c_4])).

tff(c_740,plain,(
    ! [A_89,C_90] :
      ( k4_xboole_0(k1_tarski(A_89),C_90) = k1_xboole_0
      | ~ r2_hidden(A_89,C_90) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_313,c_695])).

tff(c_36,plain,(
    k4_xboole_0(k1_tarski('#skF_1'),'#skF_2') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_775,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_740,c_36])).

tff(c_810,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_428,c_775])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:11:01 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.46/1.37  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.46/1.37  
% 2.46/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.72/1.38  %$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 2.72/1.38  
% 2.72/1.38  %Foreground sorts:
% 2.72/1.38  
% 2.72/1.38  
% 2.72/1.38  %Background operators:
% 2.72/1.38  
% 2.72/1.38  
% 2.72/1.38  %Foreground operators:
% 2.72/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.72/1.38  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.72/1.38  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.72/1.38  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.72/1.38  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.72/1.38  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.72/1.38  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.72/1.38  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.72/1.38  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.72/1.38  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.72/1.38  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.72/1.38  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.72/1.38  tff('#skF_2', type, '#skF_2': $i).
% 2.72/1.38  tff('#skF_1', type, '#skF_1': $i).
% 2.72/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.72/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.72/1.38  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.72/1.38  
% 2.72/1.40  tff(f_56, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 2.72/1.40  tff(f_43, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.72/1.40  tff(f_67, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_xboole_0) | (k4_xboole_0(k1_tarski(A), B) = k1_tarski(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_zfmisc_1)).
% 2.72/1.40  tff(f_35, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 2.72/1.40  tff(f_39, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 2.72/1.40  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.72/1.40  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.72/1.40  tff(f_45, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.72/1.40  tff(f_62, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 2.72/1.40  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.72/1.40  tff(c_161, plain, (![A_42, B_43]: (r1_xboole_0(k1_tarski(A_42), B_43) | r2_hidden(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.72/1.40  tff(c_14, plain, (![A_11, B_12]: (k4_xboole_0(A_11, B_12)=A_11 | ~r1_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.72/1.40  tff(c_385, plain, (![A_66, B_67]: (k4_xboole_0(k1_tarski(A_66), B_67)=k1_tarski(A_66) | r2_hidden(A_66, B_67))), inference(resolution, [status(thm)], [c_161, c_14])).
% 2.72/1.40  tff(c_34, plain, (k4_xboole_0(k1_tarski('#skF_1'), '#skF_2')!=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.72/1.40  tff(c_428, plain, (r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_385, c_34])).
% 2.72/1.40  tff(c_8, plain, (![A_7]: (k3_xboole_0(A_7, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.72/1.40  tff(c_12, plain, (![A_10]: (k5_xboole_0(A_10, k1_xboole_0)=A_10)), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.72/1.40  tff(c_190, plain, (![A_54, B_55]: (k5_xboole_0(A_54, k3_xboole_0(A_54, B_55))=k4_xboole_0(A_54, B_55))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.72/1.40  tff(c_208, plain, (![A_7]: (k5_xboole_0(A_7, k1_xboole_0)=k4_xboole_0(A_7, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_190])).
% 2.72/1.40  tff(c_213, plain, (![A_56]: (k4_xboole_0(A_56, k1_xboole_0)=A_56)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_208])).
% 2.72/1.40  tff(c_10, plain, (![A_8, B_9]: (k4_xboole_0(A_8, k4_xboole_0(A_8, B_9))=k3_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.72/1.40  tff(c_219, plain, (![A_56]: (k4_xboole_0(A_56, A_56)=k3_xboole_0(A_56, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_213, c_10])).
% 2.72/1.40  tff(c_224, plain, (![A_56]: (k4_xboole_0(A_56, A_56)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_219])).
% 2.72/1.40  tff(c_212, plain, (![A_7]: (k4_xboole_0(A_7, k1_xboole_0)=A_7)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_208])).
% 2.72/1.40  tff(c_257, plain, (![A_58]: (k4_xboole_0(A_58, A_58)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_219])).
% 2.72/1.40  tff(c_269, plain, (![A_58]: (k4_xboole_0(A_58, k1_xboole_0)=k3_xboole_0(A_58, A_58))), inference(superposition, [status(thm), theory('equality')], [c_257, c_10])).
% 2.72/1.40  tff(c_286, plain, (![A_59]: (k3_xboole_0(A_59, A_59)=A_59)), inference(demodulation, [status(thm), theory('equality')], [c_212, c_269])).
% 2.72/1.40  tff(c_4, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k3_xboole_0(A_3, B_4))=k4_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.72/1.40  tff(c_292, plain, (![A_59]: (k5_xboole_0(A_59, A_59)=k4_xboole_0(A_59, A_59))), inference(superposition, [status(thm), theory('equality')], [c_286, c_4])).
% 2.72/1.40  tff(c_313, plain, (![A_59]: (k5_xboole_0(A_59, A_59)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_224, c_292])).
% 2.72/1.40  tff(c_18, plain, (![A_13]: (k2_tarski(A_13, A_13)=k1_tarski(A_13))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.72/1.40  tff(c_523, plain, (![A_73, B_74, C_75]: (r1_tarski(k2_tarski(A_73, B_74), C_75) | ~r2_hidden(B_74, C_75) | ~r2_hidden(A_73, C_75))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.72/1.40  tff(c_663, plain, (![A_84, C_85]: (r1_tarski(k1_tarski(A_84), C_85) | ~r2_hidden(A_84, C_85) | ~r2_hidden(A_84, C_85))), inference(superposition, [status(thm), theory('equality')], [c_18, c_523])).
% 2.72/1.40  tff(c_6, plain, (![A_5, B_6]: (k3_xboole_0(A_5, B_6)=A_5 | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.72/1.40  tff(c_672, plain, (![A_86, C_87]: (k3_xboole_0(k1_tarski(A_86), C_87)=k1_tarski(A_86) | ~r2_hidden(A_86, C_87))), inference(resolution, [status(thm)], [c_663, c_6])).
% 2.72/1.40  tff(c_695, plain, (![A_86, C_87]: (k5_xboole_0(k1_tarski(A_86), k1_tarski(A_86))=k4_xboole_0(k1_tarski(A_86), C_87) | ~r2_hidden(A_86, C_87))), inference(superposition, [status(thm), theory('equality')], [c_672, c_4])).
% 2.72/1.40  tff(c_740, plain, (![A_89, C_90]: (k4_xboole_0(k1_tarski(A_89), C_90)=k1_xboole_0 | ~r2_hidden(A_89, C_90))), inference(demodulation, [status(thm), theory('equality')], [c_313, c_695])).
% 2.72/1.40  tff(c_36, plain, (k4_xboole_0(k1_tarski('#skF_1'), '#skF_2')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.72/1.40  tff(c_775, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_740, c_36])).
% 2.72/1.40  tff(c_810, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_428, c_775])).
% 2.72/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.72/1.40  
% 2.72/1.40  Inference rules
% 2.72/1.40  ----------------------
% 2.72/1.40  #Ref     : 0
% 2.72/1.40  #Sup     : 183
% 2.72/1.40  #Fact    : 0
% 2.72/1.40  #Define  : 0
% 2.72/1.40  #Split   : 0
% 2.72/1.40  #Chain   : 0
% 2.72/1.40  #Close   : 0
% 2.72/1.40  
% 2.72/1.40  Ordering : KBO
% 2.72/1.40  
% 2.72/1.40  Simplification rules
% 2.72/1.40  ----------------------
% 2.72/1.40  #Subsume      : 22
% 2.72/1.40  #Demod        : 54
% 2.72/1.40  #Tautology    : 112
% 2.72/1.40  #SimpNegUnit  : 0
% 2.72/1.40  #BackRed      : 0
% 2.72/1.40  
% 2.72/1.40  #Partial instantiations: 0
% 2.72/1.40  #Strategies tried      : 1
% 2.72/1.40  
% 2.72/1.40  Timing (in seconds)
% 2.72/1.40  ----------------------
% 2.72/1.40  Preprocessing        : 0.32
% 2.72/1.40  Parsing              : 0.17
% 2.72/1.40  CNF conversion       : 0.02
% 2.72/1.40  Main loop            : 0.31
% 2.72/1.40  Inferencing          : 0.12
% 2.72/1.40  Reduction            : 0.10
% 2.72/1.40  Demodulation         : 0.08
% 2.72/1.40  BG Simplification    : 0.02
% 2.72/1.40  Subsumption          : 0.05
% 2.72/1.40  Abstraction          : 0.02
% 2.72/1.40  MUC search           : 0.00
% 2.72/1.40  Cooper               : 0.00
% 2.72/1.40  Total                : 0.68
% 2.72/1.40  Index Insertion      : 0.00
% 2.72/1.40  Index Deletion       : 0.00
% 2.72/1.40  Index Matching       : 0.00
% 2.72/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
