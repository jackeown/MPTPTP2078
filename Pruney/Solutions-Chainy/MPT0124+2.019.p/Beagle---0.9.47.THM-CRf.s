%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:37 EST 2020

% Result     : Theorem 3.88s
% Output     : CNFRefutation 3.88s
% Verified   : 
% Statistics : Number of formulae       :   50 (  67 expanded)
%              Number of leaves         :   22 (  31 expanded)
%              Depth                    :    9
%              Number of atoms          :   46 (  65 expanded)
%              Number of equality atoms :   36 (  52 expanded)
%              Maximal formula depth    :    6 (   3 average)
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

tff(f_54,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(C,B)
       => k4_xboole_0(A,C) = k2_xboole_0(k4_xboole_0(A,B),k3_xboole_0(A,k4_xboole_0(B,C))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] : k3_xboole_0(A,k2_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => B = k2_xboole_0(A,k4_xboole_0(B,A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_47,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_49,axiom,(
    ! [A,B,C] : k4_xboole_0(A,k4_xboole_0(B,C)) = k2_xboole_0(k4_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_xboole_1)).

tff(c_24,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_2,plain,(
    ! [A_1] : k2_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_45,plain,(
    ! [A_24,B_25] : k3_xboole_0(A_24,k2_xboole_0(A_24,B_25)) = A_24 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_54,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_45])).

tff(c_16,plain,(
    ! [A_14,B_15] : k4_xboole_0(A_14,k4_xboole_0(A_14,B_15)) = k3_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_326,plain,(
    ! [A_43,B_44] :
      ( k2_xboole_0(A_43,k4_xboole_0(B_44,A_43)) = B_44
      | ~ r1_tarski(A_43,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_12,plain,(
    ! [A_10,B_11] : k4_xboole_0(k2_xboole_0(A_10,B_11),B_11) = k4_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_335,plain,(
    ! [B_44,A_43] :
      ( k4_xboole_0(B_44,k4_xboole_0(B_44,A_43)) = k4_xboole_0(A_43,k4_xboole_0(B_44,A_43))
      | ~ r1_tarski(A_43,B_44) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_326,c_12])).

tff(c_2488,plain,(
    ! [A_91,B_92] :
      ( k4_xboole_0(A_91,k4_xboole_0(B_92,A_91)) = k3_xboole_0(B_92,A_91)
      | ~ r1_tarski(A_91,B_92) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_335])).

tff(c_421,plain,(
    ! [A_50,B_51,C_52] : k4_xboole_0(k3_xboole_0(A_50,B_51),C_52) = k3_xboole_0(A_50,k4_xboole_0(B_51,C_52)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_501,plain,(
    ! [A_53,C_54] : k3_xboole_0(A_53,k4_xboole_0(A_53,C_54)) = k4_xboole_0(A_53,C_54) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_421])).

tff(c_4,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k3_xboole_0(A_3,B_4)) = k4_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_510,plain,(
    ! [A_53,C_54] : k5_xboole_0(A_53,k4_xboole_0(A_53,C_54)) = k4_xboole_0(A_53,k4_xboole_0(A_53,C_54)) ),
    inference(superposition,[status(thm),theory(equality)],[c_501,c_4])).

tff(c_542,plain,(
    ! [A_53,C_54] : k5_xboole_0(A_53,k4_xboole_0(A_53,C_54)) = k3_xboole_0(A_53,C_54) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_510])).

tff(c_66,plain,(
    ! [A_27,B_28] :
      ( k2_xboole_0(A_27,B_28) = B_28
      | ~ r1_tarski(A_27,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_70,plain,(
    k2_xboole_0('#skF_3','#skF_2') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_24,c_66])).

tff(c_8,plain,(
    ! [A_7,B_8] : k3_xboole_0(A_7,k2_xboole_0(A_7,B_8)) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_74,plain,(
    k3_xboole_0('#skF_3','#skF_2') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_8])).

tff(c_553,plain,(
    ! [C_55] : k3_xboole_0('#skF_3',k4_xboole_0('#skF_2',C_55)) = k4_xboole_0('#skF_3',C_55) ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_421])).

tff(c_562,plain,(
    ! [C_55] : k5_xboole_0('#skF_3',k4_xboole_0('#skF_3',C_55)) = k4_xboole_0('#skF_3',k4_xboole_0('#skF_2',C_55)) ),
    inference(superposition,[status(thm),theory(equality)],[c_553,c_4])).

tff(c_639,plain,(
    ! [C_55] : k4_xboole_0('#skF_3',k4_xboole_0('#skF_2',C_55)) = k3_xboole_0('#skF_3',C_55) ),
    inference(demodulation,[status(thm),theory(equality)],[c_542,c_562])).

tff(c_2529,plain,
    ( k3_xboole_0('#skF_2','#skF_3') = k3_xboole_0('#skF_3','#skF_3')
    | ~ r1_tarski('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_2488,c_639])).

tff(c_2630,plain,(
    k3_xboole_0('#skF_2','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_54,c_2529])).

tff(c_20,plain,(
    ! [A_19,B_20,C_21] : k2_xboole_0(k4_xboole_0(A_19,B_20),k3_xboole_0(A_19,C_21)) = k4_xboole_0(A_19,k4_xboole_0(B_20,C_21)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_22,plain,(
    k2_xboole_0(k4_xboole_0('#skF_1','#skF_2'),k3_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3'))) != k4_xboole_0('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_25,plain,(
    k4_xboole_0('#skF_1',k4_xboole_0('#skF_2',k4_xboole_0('#skF_2','#skF_3'))) != k4_xboole_0('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_22])).

tff(c_26,plain,(
    k4_xboole_0('#skF_1',k3_xboole_0('#skF_2','#skF_3')) != k4_xboole_0('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_25])).

tff(c_2653,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2630,c_26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:22:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.88/1.66  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.88/1.66  
% 3.88/1.66  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.88/1.67  %$ r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.88/1.67  
% 3.88/1.67  %Foreground sorts:
% 3.88/1.67  
% 3.88/1.67  
% 3.88/1.67  %Background operators:
% 3.88/1.67  
% 3.88/1.67  
% 3.88/1.67  %Foreground operators:
% 3.88/1.67  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.88/1.67  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.88/1.67  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.88/1.67  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.88/1.67  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.88/1.67  tff('#skF_2', type, '#skF_2': $i).
% 3.88/1.67  tff('#skF_3', type, '#skF_3': $i).
% 3.88/1.67  tff('#skF_1', type, '#skF_1': $i).
% 3.88/1.67  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.88/1.67  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.88/1.67  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.88/1.67  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.88/1.67  
% 3.88/1.68  tff(f_54, negated_conjecture, ~(![A, B, C]: (r1_tarski(C, B) => (k4_xboole_0(A, C) = k2_xboole_0(k4_xboole_0(A, B), k3_xboole_0(A, k4_xboole_0(B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t117_xboole_1)).
% 3.88/1.68  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 3.88/1.68  tff(f_35, axiom, (![A, B]: (k3_xboole_0(A, k2_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_xboole_1)).
% 3.88/1.68  tff(f_45, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.88/1.68  tff(f_43, axiom, (![A, B]: (r1_tarski(A, B) => (B = k2_xboole_0(A, k4_xboole_0(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_xboole_1)).
% 3.88/1.68  tff(f_39, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_xboole_1)).
% 3.88/1.68  tff(f_47, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_xboole_1)).
% 3.88/1.68  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.88/1.68  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 3.88/1.68  tff(f_49, axiom, (![A, B, C]: (k4_xboole_0(A, k4_xboole_0(B, C)) = k2_xboole_0(k4_xboole_0(A, B), k3_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_xboole_1)).
% 3.88/1.68  tff(c_24, plain, (r1_tarski('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.88/1.68  tff(c_2, plain, (![A_1]: (k2_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.88/1.68  tff(c_45, plain, (![A_24, B_25]: (k3_xboole_0(A_24, k2_xboole_0(A_24, B_25))=A_24)), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.88/1.68  tff(c_54, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(superposition, [status(thm), theory('equality')], [c_2, c_45])).
% 3.88/1.68  tff(c_16, plain, (![A_14, B_15]: (k4_xboole_0(A_14, k4_xboole_0(A_14, B_15))=k3_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.88/1.68  tff(c_326, plain, (![A_43, B_44]: (k2_xboole_0(A_43, k4_xboole_0(B_44, A_43))=B_44 | ~r1_tarski(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.88/1.68  tff(c_12, plain, (![A_10, B_11]: (k4_xboole_0(k2_xboole_0(A_10, B_11), B_11)=k4_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.88/1.68  tff(c_335, plain, (![B_44, A_43]: (k4_xboole_0(B_44, k4_xboole_0(B_44, A_43))=k4_xboole_0(A_43, k4_xboole_0(B_44, A_43)) | ~r1_tarski(A_43, B_44))), inference(superposition, [status(thm), theory('equality')], [c_326, c_12])).
% 3.88/1.68  tff(c_2488, plain, (![A_91, B_92]: (k4_xboole_0(A_91, k4_xboole_0(B_92, A_91))=k3_xboole_0(B_92, A_91) | ~r1_tarski(A_91, B_92))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_335])).
% 3.88/1.68  tff(c_421, plain, (![A_50, B_51, C_52]: (k4_xboole_0(k3_xboole_0(A_50, B_51), C_52)=k3_xboole_0(A_50, k4_xboole_0(B_51, C_52)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.88/1.68  tff(c_501, plain, (![A_53, C_54]: (k3_xboole_0(A_53, k4_xboole_0(A_53, C_54))=k4_xboole_0(A_53, C_54))), inference(superposition, [status(thm), theory('equality')], [c_54, c_421])).
% 3.88/1.68  tff(c_4, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k3_xboole_0(A_3, B_4))=k4_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.88/1.68  tff(c_510, plain, (![A_53, C_54]: (k5_xboole_0(A_53, k4_xboole_0(A_53, C_54))=k4_xboole_0(A_53, k4_xboole_0(A_53, C_54)))), inference(superposition, [status(thm), theory('equality')], [c_501, c_4])).
% 3.88/1.68  tff(c_542, plain, (![A_53, C_54]: (k5_xboole_0(A_53, k4_xboole_0(A_53, C_54))=k3_xboole_0(A_53, C_54))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_510])).
% 3.88/1.68  tff(c_66, plain, (![A_27, B_28]: (k2_xboole_0(A_27, B_28)=B_28 | ~r1_tarski(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.88/1.68  tff(c_70, plain, (k2_xboole_0('#skF_3', '#skF_2')='#skF_2'), inference(resolution, [status(thm)], [c_24, c_66])).
% 3.88/1.68  tff(c_8, plain, (![A_7, B_8]: (k3_xboole_0(A_7, k2_xboole_0(A_7, B_8))=A_7)), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.88/1.68  tff(c_74, plain, (k3_xboole_0('#skF_3', '#skF_2')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_70, c_8])).
% 3.88/1.68  tff(c_553, plain, (![C_55]: (k3_xboole_0('#skF_3', k4_xboole_0('#skF_2', C_55))=k4_xboole_0('#skF_3', C_55))), inference(superposition, [status(thm), theory('equality')], [c_74, c_421])).
% 3.88/1.68  tff(c_562, plain, (![C_55]: (k5_xboole_0('#skF_3', k4_xboole_0('#skF_3', C_55))=k4_xboole_0('#skF_3', k4_xboole_0('#skF_2', C_55)))), inference(superposition, [status(thm), theory('equality')], [c_553, c_4])).
% 3.88/1.68  tff(c_639, plain, (![C_55]: (k4_xboole_0('#skF_3', k4_xboole_0('#skF_2', C_55))=k3_xboole_0('#skF_3', C_55))), inference(demodulation, [status(thm), theory('equality')], [c_542, c_562])).
% 3.88/1.68  tff(c_2529, plain, (k3_xboole_0('#skF_2', '#skF_3')=k3_xboole_0('#skF_3', '#skF_3') | ~r1_tarski('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_2488, c_639])).
% 3.88/1.68  tff(c_2630, plain, (k3_xboole_0('#skF_2', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_24, c_54, c_2529])).
% 3.88/1.68  tff(c_20, plain, (![A_19, B_20, C_21]: (k2_xboole_0(k4_xboole_0(A_19, B_20), k3_xboole_0(A_19, C_21))=k4_xboole_0(A_19, k4_xboole_0(B_20, C_21)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.88/1.68  tff(c_22, plain, (k2_xboole_0(k4_xboole_0('#skF_1', '#skF_2'), k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3')))!=k4_xboole_0('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.88/1.68  tff(c_25, plain, (k4_xboole_0('#skF_1', k4_xboole_0('#skF_2', k4_xboole_0('#skF_2', '#skF_3')))!=k4_xboole_0('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_22])).
% 3.88/1.68  tff(c_26, plain, (k4_xboole_0('#skF_1', k3_xboole_0('#skF_2', '#skF_3'))!=k4_xboole_0('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_25])).
% 3.88/1.68  tff(c_2653, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2630, c_26])).
% 3.88/1.68  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.88/1.68  
% 3.88/1.68  Inference rules
% 3.88/1.68  ----------------------
% 3.88/1.68  #Ref     : 0
% 3.88/1.68  #Sup     : 640
% 3.88/1.68  #Fact    : 0
% 3.88/1.68  #Define  : 0
% 3.88/1.68  #Split   : 2
% 3.88/1.68  #Chain   : 0
% 3.88/1.68  #Close   : 0
% 3.88/1.68  
% 3.88/1.68  Ordering : KBO
% 3.88/1.68  
% 3.88/1.68  Simplification rules
% 3.88/1.68  ----------------------
% 3.88/1.68  #Subsume      : 11
% 3.88/1.68  #Demod        : 650
% 3.88/1.68  #Tautology    : 390
% 3.88/1.68  #SimpNegUnit  : 0
% 3.88/1.68  #BackRed      : 5
% 3.88/1.68  
% 3.88/1.68  #Partial instantiations: 0
% 3.88/1.68  #Strategies tried      : 1
% 3.88/1.68  
% 3.88/1.68  Timing (in seconds)
% 3.88/1.68  ----------------------
% 3.94/1.68  Preprocessing        : 0.29
% 3.94/1.68  Parsing              : 0.16
% 3.94/1.68  CNF conversion       : 0.02
% 3.94/1.68  Main loop            : 0.62
% 3.94/1.68  Inferencing          : 0.21
% 3.94/1.68  Reduction            : 0.26
% 3.94/1.68  Demodulation         : 0.21
% 3.94/1.68  BG Simplification    : 0.03
% 3.94/1.68  Subsumption          : 0.09
% 3.94/1.68  Abstraction          : 0.03
% 3.94/1.68  MUC search           : 0.00
% 3.94/1.68  Cooper               : 0.00
% 3.94/1.68  Total                : 0.94
% 3.94/1.68  Index Insertion      : 0.00
% 3.94/1.68  Index Deletion       : 0.00
% 3.94/1.68  Index Matching       : 0.00
% 3.94/1.68  BG Taut test         : 0.00
%------------------------------------------------------------------------------
