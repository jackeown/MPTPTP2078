%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:57 EST 2020

% Result     : Theorem 3.85s
% Output     : CNFRefutation 3.85s
% Verified   : 
% Statistics : Number of formulae       :   52 (  75 expanded)
%              Number of leaves         :   20 (  33 expanded)
%              Depth                    :   10
%              Number of atoms          :   45 (  70 expanded)
%              Number of equality atoms :   37 (  59 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(f_33,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_37,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_50,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( ~ r1_xboole_0(A,k3_xboole_0(B,C))
          & r1_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_43,axiom,(
    ! [A,B,C] : k4_xboole_0(A,k4_xboole_0(B,C)) = k2_xboole_0(k4_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_xboole_1)).

tff(c_8,plain,(
    ! [A_5] : k3_xboole_0(A_5,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_12,plain,(
    ! [A_8] : k4_xboole_0(A_8,k1_xboole_0) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_90,plain,(
    ! [A_24,B_25] : k4_xboole_0(A_24,k4_xboole_0(A_24,B_25)) = k3_xboole_0(A_24,B_25) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_105,plain,(
    ! [A_8] : k4_xboole_0(A_8,A_8) = k3_xboole_0(A_8,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_90])).

tff(c_108,plain,(
    ! [A_8] : k4_xboole_0(A_8,A_8) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_105])).

tff(c_14,plain,(
    ! [A_9,B_10] : k4_xboole_0(A_9,k4_xboole_0(A_9,B_10)) = k3_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_149,plain,(
    ! [A_28,B_29] : k2_xboole_0(k3_xboole_0(A_28,B_29),k4_xboole_0(A_28,B_29)) = A_28 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_489,plain,(
    ! [A_42,B_43] : k2_xboole_0(k3_xboole_0(A_42,k4_xboole_0(A_42,B_43)),k3_xboole_0(A_42,B_43)) = A_42 ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_149])).

tff(c_532,plain,(
    ! [A_42,B_43] : k2_xboole_0(k3_xboole_0(A_42,B_43),k3_xboole_0(A_42,k4_xboole_0(A_42,B_43))) = A_42 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_489])).

tff(c_204,plain,(
    ! [A_31,B_32] : k2_xboole_0(A_31,k4_xboole_0(B_32,A_31)) = k2_xboole_0(A_31,B_32) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_224,plain,(
    ! [A_9,B_10] : k2_xboole_0(k4_xboole_0(A_9,B_10),k3_xboole_0(A_9,B_10)) = k2_xboole_0(k4_xboole_0(A_9,B_10),A_9) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_204])).

tff(c_2015,plain,(
    ! [A_64,B_65] : k2_xboole_0(k4_xboole_0(A_64,B_65),k3_xboole_0(A_64,B_65)) = k2_xboole_0(A_64,k4_xboole_0(A_64,B_65)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_224])).

tff(c_2091,plain,(
    ! [A_9,B_10] : k2_xboole_0(k3_xboole_0(A_9,B_10),k3_xboole_0(A_9,k4_xboole_0(A_9,B_10))) = k2_xboole_0(A_9,k4_xboole_0(A_9,k4_xboole_0(A_9,B_10))) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_2015])).

tff(c_2130,plain,(
    ! [A_9,B_10] : k2_xboole_0(A_9,k3_xboole_0(A_9,B_10)) = A_9 ),
    inference(demodulation,[status(thm),theory(equality)],[c_532,c_14,c_2091])).

tff(c_170,plain,(
    ! [A_8] : k2_xboole_0(k3_xboole_0(A_8,k1_xboole_0),A_8) = A_8 ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_149])).

tff(c_178,plain,(
    ! [A_8] : k2_xboole_0(k1_xboole_0,A_8) = A_8 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_170])).

tff(c_20,plain,(
    r1_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_72,plain,(
    ! [A_20,B_21] :
      ( k3_xboole_0(A_20,B_21) = k1_xboole_0
      | ~ r1_xboole_0(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_76,plain,(
    k3_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_20,c_72])).

tff(c_167,plain,(
    k2_xboole_0(k1_xboole_0,k4_xboole_0('#skF_1','#skF_2')) = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_149])).

tff(c_280,plain,(
    k4_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_178,c_167])).

tff(c_305,plain,(
    ! [A_34,B_35,C_36] : k2_xboole_0(k4_xboole_0(A_34,B_35),k3_xboole_0(A_34,C_36)) = k4_xboole_0(A_34,k4_xboole_0(B_35,C_36)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_320,plain,(
    ! [C_36] : k4_xboole_0('#skF_1',k4_xboole_0('#skF_2',C_36)) = k2_xboole_0('#skF_1',k3_xboole_0('#skF_1',C_36)) ),
    inference(superposition,[status(thm),theory(equality)],[c_280,c_305])).

tff(c_2536,plain,(
    ! [C_75] : k4_xboole_0('#skF_1',k4_xboole_0('#skF_2',C_75)) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2130,c_320])).

tff(c_2604,plain,(
    ! [B_76] : k4_xboole_0('#skF_1',k3_xboole_0('#skF_2',B_76)) = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_2536])).

tff(c_2630,plain,(
    ! [B_76] : k3_xboole_0('#skF_1',k3_xboole_0('#skF_2',B_76)) = k4_xboole_0('#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_2604,c_14])).

tff(c_2648,plain,(
    ! [B_76] : k3_xboole_0('#skF_1',k3_xboole_0('#skF_2',B_76)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_2630])).

tff(c_81,plain,(
    ! [A_22,B_23] :
      ( r1_xboole_0(A_22,B_23)
      | k3_xboole_0(A_22,B_23) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_22,plain,(
    ~ r1_xboole_0('#skF_1',k3_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_89,plain,(
    k3_xboole_0('#skF_1',k3_xboole_0('#skF_2','#skF_3')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_81,c_22])).

tff(c_2722,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2648,c_89])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 17:35:35 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.85/1.74  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.85/1.75  
% 3.85/1.75  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.85/1.75  %$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.85/1.75  
% 3.85/1.75  %Foreground sorts:
% 3.85/1.75  
% 3.85/1.75  
% 3.85/1.75  %Background operators:
% 3.85/1.75  
% 3.85/1.75  
% 3.85/1.75  %Foreground operators:
% 3.85/1.75  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.85/1.75  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.85/1.75  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.85/1.75  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.85/1.75  tff('#skF_2', type, '#skF_2': $i).
% 3.85/1.75  tff('#skF_3', type, '#skF_3': $i).
% 3.85/1.75  tff('#skF_1', type, '#skF_1': $i).
% 3.85/1.75  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.85/1.75  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.85/1.75  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.85/1.75  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.85/1.75  
% 3.85/1.76  tff(f_33, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 3.85/1.76  tff(f_37, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 3.85/1.76  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.85/1.76  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 3.85/1.76  tff(f_41, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_xboole_1)).
% 3.85/1.76  tff(f_35, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 3.85/1.76  tff(f_50, negated_conjecture, ~(![A, B, C]: ~(~r1_xboole_0(A, k3_xboole_0(B, C)) & r1_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_xboole_1)).
% 3.85/1.76  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 3.85/1.76  tff(f_43, axiom, (![A, B, C]: (k4_xboole_0(A, k4_xboole_0(B, C)) = k2_xboole_0(k4_xboole_0(A, B), k3_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_xboole_1)).
% 3.85/1.76  tff(c_8, plain, (![A_5]: (k3_xboole_0(A_5, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.85/1.76  tff(c_12, plain, (![A_8]: (k4_xboole_0(A_8, k1_xboole_0)=A_8)), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.85/1.76  tff(c_90, plain, (![A_24, B_25]: (k4_xboole_0(A_24, k4_xboole_0(A_24, B_25))=k3_xboole_0(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.85/1.76  tff(c_105, plain, (![A_8]: (k4_xboole_0(A_8, A_8)=k3_xboole_0(A_8, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_90])).
% 3.85/1.76  tff(c_108, plain, (![A_8]: (k4_xboole_0(A_8, A_8)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_105])).
% 3.85/1.76  tff(c_14, plain, (![A_9, B_10]: (k4_xboole_0(A_9, k4_xboole_0(A_9, B_10))=k3_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.85/1.76  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.85/1.76  tff(c_149, plain, (![A_28, B_29]: (k2_xboole_0(k3_xboole_0(A_28, B_29), k4_xboole_0(A_28, B_29))=A_28)), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.85/1.76  tff(c_489, plain, (![A_42, B_43]: (k2_xboole_0(k3_xboole_0(A_42, k4_xboole_0(A_42, B_43)), k3_xboole_0(A_42, B_43))=A_42)), inference(superposition, [status(thm), theory('equality')], [c_14, c_149])).
% 3.85/1.76  tff(c_532, plain, (![A_42, B_43]: (k2_xboole_0(k3_xboole_0(A_42, B_43), k3_xboole_0(A_42, k4_xboole_0(A_42, B_43)))=A_42)), inference(superposition, [status(thm), theory('equality')], [c_2, c_489])).
% 3.85/1.76  tff(c_204, plain, (![A_31, B_32]: (k2_xboole_0(A_31, k4_xboole_0(B_32, A_31))=k2_xboole_0(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.85/1.76  tff(c_224, plain, (![A_9, B_10]: (k2_xboole_0(k4_xboole_0(A_9, B_10), k3_xboole_0(A_9, B_10))=k2_xboole_0(k4_xboole_0(A_9, B_10), A_9))), inference(superposition, [status(thm), theory('equality')], [c_14, c_204])).
% 3.85/1.76  tff(c_2015, plain, (![A_64, B_65]: (k2_xboole_0(k4_xboole_0(A_64, B_65), k3_xboole_0(A_64, B_65))=k2_xboole_0(A_64, k4_xboole_0(A_64, B_65)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_224])).
% 3.85/1.76  tff(c_2091, plain, (![A_9, B_10]: (k2_xboole_0(k3_xboole_0(A_9, B_10), k3_xboole_0(A_9, k4_xboole_0(A_9, B_10)))=k2_xboole_0(A_9, k4_xboole_0(A_9, k4_xboole_0(A_9, B_10))))), inference(superposition, [status(thm), theory('equality')], [c_14, c_2015])).
% 3.85/1.76  tff(c_2130, plain, (![A_9, B_10]: (k2_xboole_0(A_9, k3_xboole_0(A_9, B_10))=A_9)), inference(demodulation, [status(thm), theory('equality')], [c_532, c_14, c_2091])).
% 3.85/1.76  tff(c_170, plain, (![A_8]: (k2_xboole_0(k3_xboole_0(A_8, k1_xboole_0), A_8)=A_8)), inference(superposition, [status(thm), theory('equality')], [c_12, c_149])).
% 3.85/1.76  tff(c_178, plain, (![A_8]: (k2_xboole_0(k1_xboole_0, A_8)=A_8)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_170])).
% 3.85/1.76  tff(c_20, plain, (r1_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.85/1.76  tff(c_72, plain, (![A_20, B_21]: (k3_xboole_0(A_20, B_21)=k1_xboole_0 | ~r1_xboole_0(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.85/1.76  tff(c_76, plain, (k3_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_20, c_72])).
% 3.85/1.76  tff(c_167, plain, (k2_xboole_0(k1_xboole_0, k4_xboole_0('#skF_1', '#skF_2'))='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_76, c_149])).
% 3.85/1.76  tff(c_280, plain, (k4_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_178, c_167])).
% 3.85/1.76  tff(c_305, plain, (![A_34, B_35, C_36]: (k2_xboole_0(k4_xboole_0(A_34, B_35), k3_xboole_0(A_34, C_36))=k4_xboole_0(A_34, k4_xboole_0(B_35, C_36)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.85/1.76  tff(c_320, plain, (![C_36]: (k4_xboole_0('#skF_1', k4_xboole_0('#skF_2', C_36))=k2_xboole_0('#skF_1', k3_xboole_0('#skF_1', C_36)))), inference(superposition, [status(thm), theory('equality')], [c_280, c_305])).
% 3.85/1.76  tff(c_2536, plain, (![C_75]: (k4_xboole_0('#skF_1', k4_xboole_0('#skF_2', C_75))='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2130, c_320])).
% 3.85/1.76  tff(c_2604, plain, (![B_76]: (k4_xboole_0('#skF_1', k3_xboole_0('#skF_2', B_76))='#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_14, c_2536])).
% 3.85/1.76  tff(c_2630, plain, (![B_76]: (k3_xboole_0('#skF_1', k3_xboole_0('#skF_2', B_76))=k4_xboole_0('#skF_1', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_2604, c_14])).
% 3.85/1.76  tff(c_2648, plain, (![B_76]: (k3_xboole_0('#skF_1', k3_xboole_0('#skF_2', B_76))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_108, c_2630])).
% 3.85/1.76  tff(c_81, plain, (![A_22, B_23]: (r1_xboole_0(A_22, B_23) | k3_xboole_0(A_22, B_23)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.85/1.76  tff(c_22, plain, (~r1_xboole_0('#skF_1', k3_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.85/1.76  tff(c_89, plain, (k3_xboole_0('#skF_1', k3_xboole_0('#skF_2', '#skF_3'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_81, c_22])).
% 3.85/1.76  tff(c_2722, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2648, c_89])).
% 3.85/1.76  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.85/1.76  
% 3.85/1.76  Inference rules
% 3.85/1.76  ----------------------
% 3.85/1.76  #Ref     : 0
% 3.85/1.76  #Sup     : 625
% 3.85/1.76  #Fact    : 0
% 3.85/1.76  #Define  : 0
% 3.85/1.76  #Split   : 0
% 3.85/1.76  #Chain   : 0
% 3.85/1.76  #Close   : 0
% 3.85/1.76  
% 3.85/1.76  Ordering : KBO
% 3.85/1.76  
% 3.85/1.76  Simplification rules
% 3.85/1.76  ----------------------
% 3.85/1.76  #Subsume      : 4
% 3.85/1.76  #Demod        : 972
% 3.85/1.76  #Tautology    : 469
% 3.85/1.76  #SimpNegUnit  : 0
% 3.85/1.76  #BackRed      : 17
% 3.85/1.76  
% 3.85/1.76  #Partial instantiations: 0
% 3.85/1.76  #Strategies tried      : 1
% 3.85/1.76  
% 3.85/1.76  Timing (in seconds)
% 3.85/1.76  ----------------------
% 3.85/1.77  Preprocessing        : 0.29
% 3.85/1.77  Parsing              : 0.16
% 3.85/1.77  CNF conversion       : 0.02
% 3.85/1.77  Main loop            : 0.64
% 3.85/1.77  Inferencing          : 0.21
% 3.85/1.77  Reduction            : 0.29
% 3.85/1.77  Demodulation         : 0.24
% 3.85/1.77  BG Simplification    : 0.02
% 3.85/1.77  Subsumption          : 0.08
% 3.85/1.77  Abstraction          : 0.03
% 3.85/1.77  MUC search           : 0.00
% 3.85/1.77  Cooper               : 0.00
% 3.85/1.77  Total                : 0.96
% 3.85/1.77  Index Insertion      : 0.00
% 3.85/1.77  Index Deletion       : 0.00
% 3.85/1.77  Index Matching       : 0.00
% 3.85/1.77  BG Taut test         : 0.00
%------------------------------------------------------------------------------
