%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:14 EST 2020

% Result     : Theorem 7.71s
% Output     : CNFRefutation 7.71s
% Verified   : 
% Statistics : Number of formulae       :   48 (  54 expanded)
%              Number of leaves         :   27 (  31 expanded)
%              Depth                    :    8
%              Number of atoms          :   34 (  41 expanded)
%              Number of equality atoms :   23 (  29 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_52,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_63,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_xboole_0(k1_tarski(A),B)
        | k3_xboole_0(k1_tarski(A),B) = k1_tarski(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_zfmisc_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k3_xboole_0(B,k1_tarski(A)) = k1_tarski(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l31_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_58,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(c_108,plain,(
    ! [A_49,B_50] :
      ( r1_xboole_0(k1_tarski(A_49),B_50)
      | r2_hidden(A_49,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_32,plain,(
    ~ r1_xboole_0(k1_tarski('#skF_1'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_112,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_108,c_32])).

tff(c_26,plain,(
    ! [B_41,A_40] :
      ( k3_xboole_0(B_41,k1_tarski(A_40)) = k1_tarski(A_40)
      | ~ r2_hidden(A_40,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_8,plain,(
    ! [B_9,A_8] : k2_tarski(B_9,A_8) = k2_tarski(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_113,plain,(
    ! [A_51,B_52] : k3_tarski(k2_tarski(A_51,B_52)) = k2_xboole_0(A_51,B_52) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_157,plain,(
    ! [A_56,B_57] : k3_tarski(k2_tarski(A_56,B_57)) = k2_xboole_0(B_57,A_56) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_113])).

tff(c_28,plain,(
    ! [A_42,B_43] : k3_tarski(k2_tarski(A_42,B_43)) = k2_xboole_0(A_42,B_43) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_163,plain,(
    ! [B_57,A_56] : k2_xboole_0(B_57,A_56) = k2_xboole_0(A_56,B_57) ),
    inference(superposition,[status(thm),theory(equality)],[c_157,c_28])).

tff(c_279,plain,(
    ! [A_67,B_68,C_69] : k5_xboole_0(k5_xboole_0(A_67,B_68),C_69) = k5_xboole_0(A_67,k5_xboole_0(B_68,C_69)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6,plain,(
    ! [A_6,B_7] : k5_xboole_0(k5_xboole_0(A_6,B_7),k2_xboole_0(A_6,B_7)) = k3_xboole_0(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_650,plain,(
    ! [A_81,B_82] : k5_xboole_0(A_81,k5_xboole_0(B_82,k2_xboole_0(A_81,B_82))) = k3_xboole_0(A_81,B_82) ),
    inference(superposition,[status(thm),theory(equality)],[c_279,c_6])).

tff(c_3602,plain,(
    ! [A_129,B_130] : k5_xboole_0(A_129,k5_xboole_0(B_130,k2_xboole_0(B_130,A_129))) = k3_xboole_0(A_129,B_130) ),
    inference(superposition,[status(thm),theory(equality)],[c_163,c_650])).

tff(c_2,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,A_1) = k5_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_731,plain,(
    ! [B_94,A_95,C_96] : k5_xboole_0(k5_xboole_0(B_94,A_95),C_96) = k5_xboole_0(A_95,k5_xboole_0(B_94,C_96)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_279])).

tff(c_836,plain,(
    ! [B_7,A_6] : k5_xboole_0(B_7,k5_xboole_0(A_6,k2_xboole_0(A_6,B_7))) = k3_xboole_0(A_6,B_7) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_731])).

tff(c_3650,plain,(
    ! [B_130,A_129] : k3_xboole_0(B_130,A_129) = k3_xboole_0(A_129,B_130) ),
    inference(superposition,[status(thm),theory(equality)],[c_3602,c_836])).

tff(c_30,plain,(
    k3_xboole_0(k1_tarski('#skF_1'),'#skF_2') != k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_4614,plain,(
    k3_xboole_0('#skF_2',k1_tarski('#skF_1')) != k1_tarski('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3650,c_30])).

tff(c_4664,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_4614])).

tff(c_4668,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_4664])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n018.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 21:07:42 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.71/2.63  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.71/2.64  
% 7.71/2.64  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.71/2.64  %$ r2_hidden > r1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_2 > #skF_1
% 7.71/2.64  
% 7.71/2.64  %Foreground sorts:
% 7.71/2.64  
% 7.71/2.64  
% 7.71/2.64  %Background operators:
% 7.71/2.64  
% 7.71/2.64  
% 7.71/2.64  %Foreground operators:
% 7.71/2.64  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.71/2.64  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.71/2.64  tff(k1_tarski, type, k1_tarski: $i > $i).
% 7.71/2.64  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 7.71/2.64  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 7.71/2.64  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 7.71/2.64  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.71/2.64  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 7.71/2.64  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 7.71/2.64  tff('#skF_2', type, '#skF_2': $i).
% 7.71/2.64  tff('#skF_1', type, '#skF_1': $i).
% 7.71/2.64  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 7.71/2.64  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 7.71/2.64  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.71/2.64  tff(k3_tarski, type, k3_tarski: $i > $i).
% 7.71/2.64  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.71/2.64  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.71/2.64  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 7.71/2.64  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 7.71/2.64  
% 7.71/2.65  tff(f_52, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 7.71/2.65  tff(f_63, negated_conjecture, ~(![A, B]: (r1_xboole_0(k1_tarski(A), B) | (k3_xboole_0(k1_tarski(A), B) = k1_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t58_zfmisc_1)).
% 7.71/2.65  tff(f_56, axiom, (![A, B]: (r2_hidden(A, B) => (k3_xboole_0(B, k1_tarski(A)) = k1_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l31_zfmisc_1)).
% 7.71/2.65  tff(f_33, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 7.71/2.65  tff(f_58, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 7.71/2.65  tff(f_29, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 7.71/2.65  tff(f_31, axiom, (![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_xboole_1)).
% 7.71/2.65  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 7.71/2.65  tff(c_108, plain, (![A_49, B_50]: (r1_xboole_0(k1_tarski(A_49), B_50) | r2_hidden(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_52])).
% 7.71/2.65  tff(c_32, plain, (~r1_xboole_0(k1_tarski('#skF_1'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_63])).
% 7.71/2.65  tff(c_112, plain, (r2_hidden('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_108, c_32])).
% 7.71/2.65  tff(c_26, plain, (![B_41, A_40]: (k3_xboole_0(B_41, k1_tarski(A_40))=k1_tarski(A_40) | ~r2_hidden(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_56])).
% 7.71/2.65  tff(c_8, plain, (![B_9, A_8]: (k2_tarski(B_9, A_8)=k2_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_33])).
% 7.71/2.65  tff(c_113, plain, (![A_51, B_52]: (k3_tarski(k2_tarski(A_51, B_52))=k2_xboole_0(A_51, B_52))), inference(cnfTransformation, [status(thm)], [f_58])).
% 7.71/2.65  tff(c_157, plain, (![A_56, B_57]: (k3_tarski(k2_tarski(A_56, B_57))=k2_xboole_0(B_57, A_56))), inference(superposition, [status(thm), theory('equality')], [c_8, c_113])).
% 7.71/2.65  tff(c_28, plain, (![A_42, B_43]: (k3_tarski(k2_tarski(A_42, B_43))=k2_xboole_0(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_58])).
% 7.71/2.65  tff(c_163, plain, (![B_57, A_56]: (k2_xboole_0(B_57, A_56)=k2_xboole_0(A_56, B_57))), inference(superposition, [status(thm), theory('equality')], [c_157, c_28])).
% 7.71/2.65  tff(c_279, plain, (![A_67, B_68, C_69]: (k5_xboole_0(k5_xboole_0(A_67, B_68), C_69)=k5_xboole_0(A_67, k5_xboole_0(B_68, C_69)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 7.71/2.65  tff(c_6, plain, (![A_6, B_7]: (k5_xboole_0(k5_xboole_0(A_6, B_7), k2_xboole_0(A_6, B_7))=k3_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.71/2.65  tff(c_650, plain, (![A_81, B_82]: (k5_xboole_0(A_81, k5_xboole_0(B_82, k2_xboole_0(A_81, B_82)))=k3_xboole_0(A_81, B_82))), inference(superposition, [status(thm), theory('equality')], [c_279, c_6])).
% 7.71/2.65  tff(c_3602, plain, (![A_129, B_130]: (k5_xboole_0(A_129, k5_xboole_0(B_130, k2_xboole_0(B_130, A_129)))=k3_xboole_0(A_129, B_130))), inference(superposition, [status(thm), theory('equality')], [c_163, c_650])).
% 7.71/2.65  tff(c_2, plain, (![B_2, A_1]: (k5_xboole_0(B_2, A_1)=k5_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 7.71/2.65  tff(c_731, plain, (![B_94, A_95, C_96]: (k5_xboole_0(k5_xboole_0(B_94, A_95), C_96)=k5_xboole_0(A_95, k5_xboole_0(B_94, C_96)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_279])).
% 7.71/2.65  tff(c_836, plain, (![B_7, A_6]: (k5_xboole_0(B_7, k5_xboole_0(A_6, k2_xboole_0(A_6, B_7)))=k3_xboole_0(A_6, B_7))), inference(superposition, [status(thm), theory('equality')], [c_6, c_731])).
% 7.71/2.65  tff(c_3650, plain, (![B_130, A_129]: (k3_xboole_0(B_130, A_129)=k3_xboole_0(A_129, B_130))), inference(superposition, [status(thm), theory('equality')], [c_3602, c_836])).
% 7.71/2.65  tff(c_30, plain, (k3_xboole_0(k1_tarski('#skF_1'), '#skF_2')!=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_63])).
% 7.71/2.65  tff(c_4614, plain, (k3_xboole_0('#skF_2', k1_tarski('#skF_1'))!=k1_tarski('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3650, c_30])).
% 7.71/2.65  tff(c_4664, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_26, c_4614])).
% 7.71/2.65  tff(c_4668, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_112, c_4664])).
% 7.71/2.65  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.71/2.65  
% 7.71/2.65  Inference rules
% 7.71/2.65  ----------------------
% 7.71/2.65  #Ref     : 0
% 7.71/2.65  #Sup     : 1239
% 7.71/2.65  #Fact    : 0
% 7.71/2.65  #Define  : 0
% 7.71/2.65  #Split   : 0
% 7.71/2.65  #Chain   : 0
% 7.71/2.65  #Close   : 0
% 7.71/2.65  
% 7.71/2.65  Ordering : KBO
% 7.71/2.65  
% 7.71/2.65  Simplification rules
% 7.71/2.65  ----------------------
% 7.71/2.65  #Subsume      : 82
% 7.71/2.65  #Demod        : 959
% 7.71/2.65  #Tautology    : 245
% 7.71/2.65  #SimpNegUnit  : 0
% 7.71/2.65  #BackRed      : 1
% 7.71/2.65  
% 7.71/2.65  #Partial instantiations: 0
% 7.71/2.65  #Strategies tried      : 1
% 7.71/2.65  
% 7.71/2.65  Timing (in seconds)
% 7.71/2.65  ----------------------
% 7.71/2.65  Preprocessing        : 0.31
% 7.71/2.65  Parsing              : 0.16
% 7.71/2.65  CNF conversion       : 0.02
% 7.71/2.65  Main loop            : 1.58
% 7.71/2.65  Inferencing          : 0.32
% 7.71/2.65  Reduction            : 1.02
% 7.71/2.65  Demodulation         : 0.96
% 7.71/2.65  BG Simplification    : 0.07
% 7.71/2.65  Subsumption          : 0.12
% 7.71/2.65  Abstraction          : 0.08
% 7.71/2.65  MUC search           : 0.00
% 7.71/2.65  Cooper               : 0.00
% 7.71/2.65  Total                : 1.91
% 7.71/2.65  Index Insertion      : 0.00
% 7.71/2.65  Index Deletion       : 0.00
% 7.71/2.65  Index Matching       : 0.00
% 7.71/2.65  BG Taut test         : 0.00
%------------------------------------------------------------------------------
