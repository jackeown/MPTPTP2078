%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:35 EST 2020

% Result     : Theorem 4.11s
% Output     : CNFRefutation 4.16s
% Verified   : 
% Statistics : Number of formulae       :   44 (  59 expanded)
%              Number of leaves         :   19 (  27 expanded)
%              Depth                    :    9
%              Number of atoms          :   38 (  57 expanded)
%              Number of equality atoms :   30 (  45 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff(f_50,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(C,B)
       => k4_xboole_0(A,C) = k2_xboole_0(k4_xboole_0(A,B),k3_xboole_0(A,k4_xboole_0(B,C))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => B = k2_xboole_0(A,k4_xboole_0(B,A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_45,axiom,(
    ! [A,B,C] : k4_xboole_0(A,k4_xboole_0(B,C)) = k2_xboole_0(k4_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(c_22,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_8,plain,(
    ! [A_7,B_8] : k2_xboole_0(A_7,k4_xboole_0(B_8,A_7)) = k2_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_14,plain,(
    ! [A_14,B_15] :
      ( k2_xboole_0(A_14,k4_xboole_0(B_15,A_14)) = B_15
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_94,plain,(
    ! [A_27,B_28] :
      ( k2_xboole_0(A_27,B_28) = B_28
      | ~ r1_tarski(A_27,B_28) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_14])).

tff(c_102,plain,(
    k2_xboole_0('#skF_3','#skF_2') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_22,c_94])).

tff(c_218,plain,(
    ! [A_41,B_42] : k4_xboole_0(k2_xboole_0(A_41,B_42),B_42) = k4_xboole_0(A_41,B_42) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_248,plain,(
    k4_xboole_0('#skF_2','#skF_2') = k4_xboole_0('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_102,c_218])).

tff(c_6,plain,(
    ! [A_5,B_6] : r1_tarski(k4_xboole_0(A_5,B_6),A_5) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_150,plain,(
    ! [A_35,B_36] : k2_xboole_0(k4_xboole_0(A_35,B_36),A_35) = A_35 ),
    inference(resolution,[status(thm)],[c_6,c_94])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_156,plain,(
    ! [A_35,B_36] : k2_xboole_0(A_35,k4_xboole_0(A_35,B_36)) = A_35 ),
    inference(superposition,[status(thm),theory(equality)],[c_150,c_2])).

tff(c_16,plain,(
    ! [A_16,B_17] : k4_xboole_0(A_16,k4_xboole_0(A_16,B_17)) = k3_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_366,plain,(
    ! [A_47,B_48] : k2_xboole_0(A_47,k4_xboole_0(B_48,A_47)) = k2_xboole_0(A_47,B_48) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_392,plain,(
    ! [A_16,B_17] : k2_xboole_0(k4_xboole_0(A_16,B_17),k3_xboole_0(A_16,B_17)) = k2_xboole_0(k4_xboole_0(A_16,B_17),A_16) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_366])).

tff(c_2079,plain,(
    ! [A_100,B_101] : k2_xboole_0(k4_xboole_0(A_100,B_101),k3_xboole_0(A_100,B_101)) = A_100 ),
    inference(demodulation,[status(thm),theory(equality)],[c_156,c_2,c_392])).

tff(c_18,plain,(
    ! [A_18,B_19,C_20] : k2_xboole_0(k4_xboole_0(A_18,B_19),k3_xboole_0(A_18,C_20)) = k4_xboole_0(A_18,k4_xboole_0(B_19,C_20)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2172,plain,(
    ! [A_102,B_103] : k4_xboole_0(A_102,k4_xboole_0(B_103,B_103)) = A_102 ),
    inference(superposition,[status(thm),theory(equality)],[c_2079,c_18])).

tff(c_2598,plain,(
    ! [A_109] : k4_xboole_0(A_109,k4_xboole_0('#skF_3','#skF_2')) = A_109 ),
    inference(superposition,[status(thm),theory(equality)],[c_248,c_2172])).

tff(c_2688,plain,(
    k3_xboole_0('#skF_3','#skF_2') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_2598,c_16])).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_20,plain,(
    k2_xboole_0(k4_xboole_0('#skF_1','#skF_2'),k3_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3'))) != k4_xboole_0('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_23,plain,(
    k4_xboole_0('#skF_1',k4_xboole_0('#skF_2',k4_xboole_0('#skF_2','#skF_3'))) != k4_xboole_0('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_20])).

tff(c_24,plain,(
    k4_xboole_0('#skF_1',k3_xboole_0('#skF_2','#skF_3')) != k4_xboole_0('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_23])).

tff(c_26,plain,(
    k4_xboole_0('#skF_1',k3_xboole_0('#skF_3','#skF_2')) != k4_xboole_0('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_24])).

tff(c_2739,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2688,c_26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:27:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.11/1.74  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.16/1.74  
% 4.16/1.74  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.16/1.75  %$ r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 4.16/1.75  
% 4.16/1.75  %Foreground sorts:
% 4.16/1.75  
% 4.16/1.75  
% 4.16/1.75  %Background operators:
% 4.16/1.75  
% 4.16/1.75  
% 4.16/1.75  %Foreground operators:
% 4.16/1.75  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.16/1.75  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.16/1.75  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.16/1.75  tff('#skF_2', type, '#skF_2': $i).
% 4.16/1.75  tff('#skF_3', type, '#skF_3': $i).
% 4.16/1.75  tff('#skF_1', type, '#skF_1': $i).
% 4.16/1.75  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.16/1.75  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.16/1.75  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.16/1.75  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.16/1.75  
% 4.16/1.76  tff(f_50, negated_conjecture, ~(![A, B, C]: (r1_tarski(C, B) => (k4_xboole_0(A, C) = k2_xboole_0(k4_xboole_0(A, B), k3_xboole_0(A, k4_xboole_0(B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t117_xboole_1)).
% 4.16/1.76  tff(f_33, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 4.16/1.76  tff(f_41, axiom, (![A, B]: (r1_tarski(A, B) => (B = k2_xboole_0(A, k4_xboole_0(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_xboole_1)).
% 4.16/1.76  tff(f_35, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_xboole_1)).
% 4.16/1.76  tff(f_31, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 4.16/1.76  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 4.16/1.76  tff(f_43, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 4.16/1.76  tff(f_45, axiom, (![A, B, C]: (k4_xboole_0(A, k4_xboole_0(B, C)) = k2_xboole_0(k4_xboole_0(A, B), k3_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_xboole_1)).
% 4.16/1.76  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 4.16/1.76  tff(c_22, plain, (r1_tarski('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.16/1.76  tff(c_8, plain, (![A_7, B_8]: (k2_xboole_0(A_7, k4_xboole_0(B_8, A_7))=k2_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.16/1.76  tff(c_14, plain, (![A_14, B_15]: (k2_xboole_0(A_14, k4_xboole_0(B_15, A_14))=B_15 | ~r1_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.16/1.76  tff(c_94, plain, (![A_27, B_28]: (k2_xboole_0(A_27, B_28)=B_28 | ~r1_tarski(A_27, B_28))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_14])).
% 4.16/1.76  tff(c_102, plain, (k2_xboole_0('#skF_3', '#skF_2')='#skF_2'), inference(resolution, [status(thm)], [c_22, c_94])).
% 4.16/1.76  tff(c_218, plain, (![A_41, B_42]: (k4_xboole_0(k2_xboole_0(A_41, B_42), B_42)=k4_xboole_0(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.16/1.76  tff(c_248, plain, (k4_xboole_0('#skF_2', '#skF_2')=k4_xboole_0('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_102, c_218])).
% 4.16/1.76  tff(c_6, plain, (![A_5, B_6]: (r1_tarski(k4_xboole_0(A_5, B_6), A_5))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.16/1.76  tff(c_150, plain, (![A_35, B_36]: (k2_xboole_0(k4_xboole_0(A_35, B_36), A_35)=A_35)), inference(resolution, [status(thm)], [c_6, c_94])).
% 4.16/1.76  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.16/1.76  tff(c_156, plain, (![A_35, B_36]: (k2_xboole_0(A_35, k4_xboole_0(A_35, B_36))=A_35)), inference(superposition, [status(thm), theory('equality')], [c_150, c_2])).
% 4.16/1.76  tff(c_16, plain, (![A_16, B_17]: (k4_xboole_0(A_16, k4_xboole_0(A_16, B_17))=k3_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.16/1.76  tff(c_366, plain, (![A_47, B_48]: (k2_xboole_0(A_47, k4_xboole_0(B_48, A_47))=k2_xboole_0(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.16/1.76  tff(c_392, plain, (![A_16, B_17]: (k2_xboole_0(k4_xboole_0(A_16, B_17), k3_xboole_0(A_16, B_17))=k2_xboole_0(k4_xboole_0(A_16, B_17), A_16))), inference(superposition, [status(thm), theory('equality')], [c_16, c_366])).
% 4.16/1.76  tff(c_2079, plain, (![A_100, B_101]: (k2_xboole_0(k4_xboole_0(A_100, B_101), k3_xboole_0(A_100, B_101))=A_100)), inference(demodulation, [status(thm), theory('equality')], [c_156, c_2, c_392])).
% 4.16/1.76  tff(c_18, plain, (![A_18, B_19, C_20]: (k2_xboole_0(k4_xboole_0(A_18, B_19), k3_xboole_0(A_18, C_20))=k4_xboole_0(A_18, k4_xboole_0(B_19, C_20)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.16/1.76  tff(c_2172, plain, (![A_102, B_103]: (k4_xboole_0(A_102, k4_xboole_0(B_103, B_103))=A_102)), inference(superposition, [status(thm), theory('equality')], [c_2079, c_18])).
% 4.16/1.76  tff(c_2598, plain, (![A_109]: (k4_xboole_0(A_109, k4_xboole_0('#skF_3', '#skF_2'))=A_109)), inference(superposition, [status(thm), theory('equality')], [c_248, c_2172])).
% 4.16/1.76  tff(c_2688, plain, (k3_xboole_0('#skF_3', '#skF_2')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_2598, c_16])).
% 4.16/1.76  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(B_4, A_3)=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.16/1.76  tff(c_20, plain, (k2_xboole_0(k4_xboole_0('#skF_1', '#skF_2'), k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3')))!=k4_xboole_0('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.16/1.76  tff(c_23, plain, (k4_xboole_0('#skF_1', k4_xboole_0('#skF_2', k4_xboole_0('#skF_2', '#skF_3')))!=k4_xboole_0('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_20])).
% 4.16/1.76  tff(c_24, plain, (k4_xboole_0('#skF_1', k3_xboole_0('#skF_2', '#skF_3'))!=k4_xboole_0('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_23])).
% 4.16/1.76  tff(c_26, plain, (k4_xboole_0('#skF_1', k3_xboole_0('#skF_3', '#skF_2'))!=k4_xboole_0('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_24])).
% 4.16/1.76  tff(c_2739, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2688, c_26])).
% 4.16/1.76  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.16/1.76  
% 4.16/1.76  Inference rules
% 4.16/1.76  ----------------------
% 4.16/1.76  #Ref     : 0
% 4.16/1.76  #Sup     : 686
% 4.16/1.76  #Fact    : 0
% 4.16/1.76  #Define  : 0
% 4.16/1.76  #Split   : 0
% 4.16/1.76  #Chain   : 0
% 4.16/1.76  #Close   : 0
% 4.16/1.76  
% 4.16/1.76  Ordering : KBO
% 4.16/1.76  
% 4.16/1.76  Simplification rules
% 4.16/1.76  ----------------------
% 4.16/1.76  #Subsume      : 2
% 4.16/1.76  #Demod        : 537
% 4.16/1.76  #Tautology    : 362
% 4.16/1.76  #SimpNegUnit  : 0
% 4.16/1.76  #BackRed      : 3
% 4.16/1.76  
% 4.16/1.76  #Partial instantiations: 0
% 4.16/1.76  #Strategies tried      : 1
% 4.16/1.76  
% 4.16/1.76  Timing (in seconds)
% 4.16/1.76  ----------------------
% 4.16/1.76  Preprocessing        : 0.28
% 4.16/1.76  Parsing              : 0.16
% 4.16/1.76  CNF conversion       : 0.02
% 4.16/1.76  Main loop            : 0.66
% 4.16/1.76  Inferencing          : 0.18
% 4.16/1.76  Reduction            : 0.31
% 4.16/1.76  Demodulation         : 0.26
% 4.16/1.76  BG Simplification    : 0.03
% 4.16/1.76  Subsumption          : 0.10
% 4.16/1.76  Abstraction          : 0.03
% 4.16/1.76  MUC search           : 0.00
% 4.16/1.76  Cooper               : 0.00
% 4.16/1.76  Total                : 0.96
% 4.16/1.76  Index Insertion      : 0.00
% 4.16/1.76  Index Deletion       : 0.00
% 4.16/1.76  Index Matching       : 0.00
% 4.16/1.76  BG Taut test         : 0.00
%------------------------------------------------------------------------------
