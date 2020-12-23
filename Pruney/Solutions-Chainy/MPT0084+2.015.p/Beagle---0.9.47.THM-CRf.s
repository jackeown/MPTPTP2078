%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:06 EST 2020

% Result     : Theorem 3.44s
% Output     : CNFRefutation 3.44s
% Verified   : 
% Statistics : Number of formulae       :   60 (  91 expanded)
%              Number of leaves         :   23 (  41 expanded)
%              Depth                    :   10
%              Number of atoms          :   53 (  93 expanded)
%              Number of equality atoms :   40 (  67 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_68,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( ~ r1_xboole_0(A,B)
          & r1_tarski(A,C)
          & r1_xboole_0(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_xboole_1)).

tff(f_57,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_51,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_53,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_59,axiom,(
    ! [A,B,C] : k4_xboole_0(A,k4_xboole_0(B,C)) = k2_xboole_0(k4_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_130,plain,(
    ! [A_26,B_27] :
      ( r1_xboole_0(A_26,B_27)
      | k3_xboole_0(A_26,B_27) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_30,plain,(
    ~ r1_xboole_0('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_133,plain,(
    k3_xboole_0('#skF_2','#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_130,c_30])).

tff(c_135,plain,(
    k3_xboole_0('#skF_3','#skF_2') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_133])).

tff(c_22,plain,(
    ! [A_16,B_17] : k4_xboole_0(A_16,k4_xboole_0(A_16,B_17)) = k3_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_16,plain,(
    ! [A_12] : k3_xboole_0(A_12,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_18,plain,(
    ! [A_13] : k4_xboole_0(A_13,k1_xboole_0) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_183,plain,(
    ! [A_38,B_39] : k4_xboole_0(A_38,k4_xboole_0(A_38,B_39)) = k3_xboole_0(A_38,B_39) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_201,plain,(
    ! [A_13] : k4_xboole_0(A_13,A_13) = k3_xboole_0(A_13,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_183])).

tff(c_205,plain,(
    ! [A_13] : k4_xboole_0(A_13,A_13) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_201])).

tff(c_732,plain,(
    ! [A_66,B_67,C_68] : k2_xboole_0(k4_xboole_0(A_66,B_67),k3_xboole_0(A_66,C_68)) = k4_xboole_0(A_66,k4_xboole_0(B_67,C_68)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_771,plain,(
    ! [A_13,C_68] : k4_xboole_0(A_13,k4_xboole_0(A_13,C_68)) = k2_xboole_0(k1_xboole_0,k3_xboole_0(A_13,C_68)) ),
    inference(superposition,[status(thm),theory(equality)],[c_205,c_732])).

tff(c_802,plain,(
    ! [A_13,C_68] : k2_xboole_0(k1_xboole_0,k3_xboole_0(A_13,C_68)) = k3_xboole_0(A_13,C_68) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_771])).

tff(c_28,plain,(
    r1_tarski('#skF_2','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_137,plain,(
    ! [A_28,B_29] :
      ( k4_xboole_0(A_28,B_29) = k1_xboole_0
      | ~ r1_tarski(A_28,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_141,plain,(
    k4_xboole_0('#skF_2','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_28,c_137])).

tff(c_780,plain,(
    ! [C_68] : k4_xboole_0('#skF_2',k4_xboole_0('#skF_4',C_68)) = k2_xboole_0(k1_xboole_0,k3_xboole_0('#skF_2',C_68)) ),
    inference(superposition,[status(thm),theory(equality)],[c_141,c_732])).

tff(c_1531,plain,(
    ! [C_68] : k4_xboole_0('#skF_2',k4_xboole_0('#skF_4',C_68)) = k3_xboole_0('#skF_2',C_68) ),
    inference(demodulation,[status(thm),theory(equality)],[c_802,c_780])).

tff(c_20,plain,(
    ! [A_14,B_15] : k4_xboole_0(A_14,k3_xboole_0(A_14,B_15)) = k4_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_48,plain,(
    ! [B_23,A_24] : k3_xboole_0(B_23,A_24) = k3_xboole_0(A_24,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_64,plain,(
    ! [A_24] : k3_xboole_0(k1_xboole_0,A_24) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_16])).

tff(c_266,plain,(
    ! [A_42,B_43] : k4_xboole_0(A_42,k3_xboole_0(A_42,B_43)) = k4_xboole_0(A_42,B_43) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_287,plain,(
    ! [A_24] : k4_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,A_24) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_266])).

tff(c_303,plain,(
    ! [A_24] : k4_xboole_0(k1_xboole_0,A_24) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_287])).

tff(c_792,plain,(
    ! [A_13,C_68] : k4_xboole_0(A_13,k4_xboole_0(k1_xboole_0,C_68)) = k2_xboole_0(A_13,k3_xboole_0(A_13,C_68)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_732])).

tff(c_862,plain,(
    ! [A_70,C_71] : k2_xboole_0(A_70,k3_xboole_0(A_70,C_71)) = A_70 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_303,c_792])).

tff(c_892,plain,(
    ! [A_12] : k2_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_862])).

tff(c_26,plain,(
    r1_xboole_0('#skF_2',k3_xboole_0('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_31,plain,(
    r1_xboole_0('#skF_2',k3_xboole_0('#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_26])).

tff(c_151,plain,(
    ! [A_32,B_33] :
      ( k3_xboole_0(A_32,B_33) = k1_xboole_0
      | ~ r1_xboole_0(A_32,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_159,plain,(
    k3_xboole_0('#skF_2',k3_xboole_0('#skF_4','#skF_3')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_31,c_151])).

tff(c_777,plain,(
    ! [B_67] : k4_xboole_0('#skF_2',k4_xboole_0(B_67,k3_xboole_0('#skF_4','#skF_3'))) = k2_xboole_0(k4_xboole_0('#skF_2',B_67),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_159,c_732])).

tff(c_2443,plain,(
    ! [B_103] : k4_xboole_0('#skF_2',k4_xboole_0(B_103,k3_xboole_0('#skF_4','#skF_3'))) = k4_xboole_0('#skF_2',B_103) ),
    inference(demodulation,[status(thm),theory(equality)],[c_892,c_777])).

tff(c_2510,plain,(
    k4_xboole_0('#skF_2',k4_xboole_0('#skF_4','#skF_3')) = k4_xboole_0('#skF_2','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_2443])).

tff(c_2536,plain,(
    k3_xboole_0('#skF_3','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_1531,c_141,c_2510])).

tff(c_2538,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_135,c_2536])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:56:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.44/1.58  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.44/1.58  
% 3.44/1.58  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.44/1.58  %$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 3.44/1.58  
% 3.44/1.58  %Foreground sorts:
% 3.44/1.58  
% 3.44/1.58  
% 3.44/1.58  %Background operators:
% 3.44/1.58  
% 3.44/1.58  
% 3.44/1.58  %Foreground operators:
% 3.44/1.58  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.44/1.58  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.44/1.58  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.44/1.58  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.44/1.58  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.44/1.58  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.44/1.58  tff('#skF_2', type, '#skF_2': $i).
% 3.44/1.58  tff('#skF_3', type, '#skF_3': $i).
% 3.44/1.58  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.44/1.58  tff('#skF_4', type, '#skF_4': $i).
% 3.44/1.58  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.44/1.58  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.44/1.58  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.44/1.58  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.44/1.58  
% 3.44/1.60  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.44/1.60  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 3.44/1.60  tff(f_68, negated_conjecture, ~(![A, B, C]: ~((~r1_xboole_0(A, B) & r1_tarski(A, C)) & r1_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_xboole_1)).
% 3.44/1.60  tff(f_57, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.44/1.60  tff(f_51, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 3.44/1.60  tff(f_53, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 3.44/1.60  tff(f_59, axiom, (![A, B, C]: (k4_xboole_0(A, k4_xboole_0(B, C)) = k2_xboole_0(k4_xboole_0(A, B), k3_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_xboole_1)).
% 3.44/1.60  tff(f_49, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 3.44/1.60  tff(f_55, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 3.44/1.60  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.44/1.60  tff(c_130, plain, (![A_26, B_27]: (r1_xboole_0(A_26, B_27) | k3_xboole_0(A_26, B_27)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.44/1.60  tff(c_30, plain, (~r1_xboole_0('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.44/1.60  tff(c_133, plain, (k3_xboole_0('#skF_2', '#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_130, c_30])).
% 3.44/1.60  tff(c_135, plain, (k3_xboole_0('#skF_3', '#skF_2')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2, c_133])).
% 3.44/1.60  tff(c_22, plain, (![A_16, B_17]: (k4_xboole_0(A_16, k4_xboole_0(A_16, B_17))=k3_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.44/1.60  tff(c_16, plain, (![A_12]: (k3_xboole_0(A_12, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.44/1.60  tff(c_18, plain, (![A_13]: (k4_xboole_0(A_13, k1_xboole_0)=A_13)), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.44/1.60  tff(c_183, plain, (![A_38, B_39]: (k4_xboole_0(A_38, k4_xboole_0(A_38, B_39))=k3_xboole_0(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.44/1.60  tff(c_201, plain, (![A_13]: (k4_xboole_0(A_13, A_13)=k3_xboole_0(A_13, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_18, c_183])).
% 3.44/1.60  tff(c_205, plain, (![A_13]: (k4_xboole_0(A_13, A_13)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_201])).
% 3.44/1.60  tff(c_732, plain, (![A_66, B_67, C_68]: (k2_xboole_0(k4_xboole_0(A_66, B_67), k3_xboole_0(A_66, C_68))=k4_xboole_0(A_66, k4_xboole_0(B_67, C_68)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.44/1.60  tff(c_771, plain, (![A_13, C_68]: (k4_xboole_0(A_13, k4_xboole_0(A_13, C_68))=k2_xboole_0(k1_xboole_0, k3_xboole_0(A_13, C_68)))), inference(superposition, [status(thm), theory('equality')], [c_205, c_732])).
% 3.44/1.60  tff(c_802, plain, (![A_13, C_68]: (k2_xboole_0(k1_xboole_0, k3_xboole_0(A_13, C_68))=k3_xboole_0(A_13, C_68))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_771])).
% 3.44/1.60  tff(c_28, plain, (r1_tarski('#skF_2', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.44/1.60  tff(c_137, plain, (![A_28, B_29]: (k4_xboole_0(A_28, B_29)=k1_xboole_0 | ~r1_tarski(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.44/1.60  tff(c_141, plain, (k4_xboole_0('#skF_2', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_28, c_137])).
% 3.44/1.60  tff(c_780, plain, (![C_68]: (k4_xboole_0('#skF_2', k4_xboole_0('#skF_4', C_68))=k2_xboole_0(k1_xboole_0, k3_xboole_0('#skF_2', C_68)))), inference(superposition, [status(thm), theory('equality')], [c_141, c_732])).
% 3.44/1.60  tff(c_1531, plain, (![C_68]: (k4_xboole_0('#skF_2', k4_xboole_0('#skF_4', C_68))=k3_xboole_0('#skF_2', C_68))), inference(demodulation, [status(thm), theory('equality')], [c_802, c_780])).
% 3.44/1.60  tff(c_20, plain, (![A_14, B_15]: (k4_xboole_0(A_14, k3_xboole_0(A_14, B_15))=k4_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.44/1.60  tff(c_48, plain, (![B_23, A_24]: (k3_xboole_0(B_23, A_24)=k3_xboole_0(A_24, B_23))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.44/1.60  tff(c_64, plain, (![A_24]: (k3_xboole_0(k1_xboole_0, A_24)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_48, c_16])).
% 3.44/1.60  tff(c_266, plain, (![A_42, B_43]: (k4_xboole_0(A_42, k3_xboole_0(A_42, B_43))=k4_xboole_0(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.44/1.60  tff(c_287, plain, (![A_24]: (k4_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, A_24))), inference(superposition, [status(thm), theory('equality')], [c_64, c_266])).
% 3.44/1.60  tff(c_303, plain, (![A_24]: (k4_xboole_0(k1_xboole_0, A_24)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_287])).
% 3.44/1.60  tff(c_792, plain, (![A_13, C_68]: (k4_xboole_0(A_13, k4_xboole_0(k1_xboole_0, C_68))=k2_xboole_0(A_13, k3_xboole_0(A_13, C_68)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_732])).
% 3.44/1.60  tff(c_862, plain, (![A_70, C_71]: (k2_xboole_0(A_70, k3_xboole_0(A_70, C_71))=A_70)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_303, c_792])).
% 3.44/1.60  tff(c_892, plain, (![A_12]: (k2_xboole_0(A_12, k1_xboole_0)=A_12)), inference(superposition, [status(thm), theory('equality')], [c_16, c_862])).
% 3.44/1.60  tff(c_26, plain, (r1_xboole_0('#skF_2', k3_xboole_0('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.44/1.60  tff(c_31, plain, (r1_xboole_0('#skF_2', k3_xboole_0('#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_26])).
% 3.44/1.60  tff(c_151, plain, (![A_32, B_33]: (k3_xboole_0(A_32, B_33)=k1_xboole_0 | ~r1_xboole_0(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.44/1.60  tff(c_159, plain, (k3_xboole_0('#skF_2', k3_xboole_0('#skF_4', '#skF_3'))=k1_xboole_0), inference(resolution, [status(thm)], [c_31, c_151])).
% 3.44/1.60  tff(c_777, plain, (![B_67]: (k4_xboole_0('#skF_2', k4_xboole_0(B_67, k3_xboole_0('#skF_4', '#skF_3')))=k2_xboole_0(k4_xboole_0('#skF_2', B_67), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_159, c_732])).
% 3.44/1.60  tff(c_2443, plain, (![B_103]: (k4_xboole_0('#skF_2', k4_xboole_0(B_103, k3_xboole_0('#skF_4', '#skF_3')))=k4_xboole_0('#skF_2', B_103))), inference(demodulation, [status(thm), theory('equality')], [c_892, c_777])).
% 3.44/1.60  tff(c_2510, plain, (k4_xboole_0('#skF_2', k4_xboole_0('#skF_4', '#skF_3'))=k4_xboole_0('#skF_2', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_20, c_2443])).
% 3.44/1.60  tff(c_2536, plain, (k3_xboole_0('#skF_3', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2, c_1531, c_141, c_2510])).
% 3.44/1.60  tff(c_2538, plain, $false, inference(negUnitSimplification, [status(thm)], [c_135, c_2536])).
% 3.44/1.60  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.44/1.60  
% 3.44/1.60  Inference rules
% 3.44/1.60  ----------------------
% 3.44/1.60  #Ref     : 0
% 3.44/1.60  #Sup     : 619
% 3.44/1.60  #Fact    : 0
% 3.44/1.60  #Define  : 0
% 3.44/1.60  #Split   : 2
% 3.44/1.60  #Chain   : 0
% 3.44/1.60  #Close   : 0
% 3.44/1.60  
% 3.44/1.60  Ordering : KBO
% 3.44/1.60  
% 3.44/1.60  Simplification rules
% 3.44/1.60  ----------------------
% 3.44/1.60  #Subsume      : 33
% 3.44/1.60  #Demod        : 567
% 3.44/1.60  #Tautology    : 434
% 3.44/1.60  #SimpNegUnit  : 13
% 3.44/1.60  #BackRed      : 2
% 3.44/1.60  
% 3.44/1.60  #Partial instantiations: 0
% 3.44/1.60  #Strategies tried      : 1
% 3.44/1.60  
% 3.44/1.60  Timing (in seconds)
% 3.44/1.60  ----------------------
% 3.44/1.60  Preprocessing        : 0.27
% 3.44/1.60  Parsing              : 0.15
% 3.44/1.60  CNF conversion       : 0.02
% 3.44/1.60  Main loop            : 0.56
% 3.44/1.60  Inferencing          : 0.18
% 3.44/1.60  Reduction            : 0.25
% 3.44/1.60  Demodulation         : 0.20
% 3.44/1.60  BG Simplification    : 0.02
% 3.44/1.60  Subsumption          : 0.08
% 3.44/1.60  Abstraction          : 0.03
% 3.44/1.60  MUC search           : 0.00
% 3.44/1.60  Cooper               : 0.00
% 3.44/1.60  Total                : 0.86
% 3.44/1.60  Index Insertion      : 0.00
% 3.44/1.60  Index Deletion       : 0.00
% 3.44/1.60  Index Matching       : 0.00
% 3.44/1.60  BG Taut test         : 0.00
%------------------------------------------------------------------------------
