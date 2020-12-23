%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:02 EST 2020

% Result     : Theorem 8.67s
% Output     : CNFRefutation 8.85s
% Verified   : 
% Statistics : Number of formulae       :   55 (  83 expanded)
%              Number of leaves         :   18 (  35 expanded)
%              Depth                    :   10
%              Number of atoms          :   49 (  79 expanded)
%              Number of equality atoms :   40 (  67 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_35,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_33,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_46,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_xboole_0(A,B)
       => r1_xboole_0(k3_xboole_0(C,A),k3_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_41,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

tff(c_14,plain,(
    ! [A_9,B_10] : k4_xboole_0(A_9,k4_xboole_0(A_9,B_10)) = k3_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_10,plain,(
    ! [A_6] : k4_xboole_0(A_6,k1_xboole_0) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_38,plain,(
    ! [B_16,A_17] : k3_xboole_0(B_16,A_17) = k3_xboole_0(A_17,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_8,plain,(
    ! [A_5] : k3_xboole_0(A_5,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_54,plain,(
    ! [A_17] : k3_xboole_0(k1_xboole_0,A_17) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_8])).

tff(c_208,plain,(
    ! [A_27,B_28] : k4_xboole_0(A_27,k3_xboole_0(A_27,B_28)) = k4_xboole_0(A_27,B_28) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_226,plain,(
    ! [A_17] : k4_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,A_17) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_208])).

tff(c_241,plain,(
    ! [A_17] : k4_xboole_0(k1_xboole_0,A_17) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_226])).

tff(c_20,plain,(
    r1_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_126,plain,(
    ! [A_21,B_22] :
      ( k3_xboole_0(A_21,B_22) = k1_xboole_0
      | ~ r1_xboole_0(A_21,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_134,plain,(
    k3_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_20,c_126])).

tff(c_223,plain,(
    k4_xboole_0('#skF_1',k1_xboole_0) = k4_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_134,c_208])).

tff(c_240,plain,(
    k4_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_223])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_232,plain,(
    ! [B_2,A_1] : k4_xboole_0(B_2,k3_xboole_0(A_1,B_2)) = k4_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_208])).

tff(c_527,plain,(
    ! [A_38,B_39,C_40] : k4_xboole_0(k3_xboole_0(A_38,B_39),C_40) = k3_xboole_0(A_38,k4_xboole_0(B_39,C_40)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_139,plain,(
    ! [A_23,B_24] : k4_xboole_0(A_23,k4_xboole_0(A_23,B_24)) = k3_xboole_0(A_23,B_24) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_154,plain,(
    ! [A_6] : k4_xboole_0(A_6,A_6) = k3_xboole_0(A_6,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_139])).

tff(c_157,plain,(
    ! [A_6] : k4_xboole_0(A_6,A_6) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_154])).

tff(c_550,plain,(
    ! [A_38,B_39] : k3_xboole_0(A_38,k4_xboole_0(B_39,k3_xboole_0(A_38,B_39))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_527,c_157])).

tff(c_630,plain,(
    ! [A_41,B_42] : k3_xboole_0(A_41,k4_xboole_0(B_42,A_41)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_232,c_550])).

tff(c_676,plain,(
    k3_xboole_0('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_240,c_630])).

tff(c_16,plain,(
    ! [A_11,B_12,C_13] : k4_xboole_0(k3_xboole_0(A_11,B_12),C_13) = k3_xboole_0(A_11,k4_xboole_0(B_12,C_13)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_711,plain,(
    ! [C_13] : k3_xboole_0('#skF_2',k4_xboole_0('#skF_1',C_13)) = k4_xboole_0(k1_xboole_0,C_13) ),
    inference(superposition,[status(thm),theory(equality)],[c_676,c_16])).

tff(c_1090,plain,(
    ! [C_49] : k3_xboole_0('#skF_2',k4_xboole_0('#skF_1',C_49)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_241,c_711])).

tff(c_1147,plain,(
    ! [B_10] : k3_xboole_0('#skF_2',k3_xboole_0('#skF_1',B_10)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_1090])).

tff(c_553,plain,(
    ! [A_38,B_39,C_40] : k4_xboole_0(k3_xboole_0(A_38,B_39),k3_xboole_0(A_38,k4_xboole_0(B_39,C_40))) = k3_xboole_0(k3_xboole_0(A_38,B_39),C_40) ),
    inference(superposition,[status(thm),theory(equality)],[c_527,c_14])).

tff(c_12,plain,(
    ! [A_7,B_8] : k4_xboole_0(A_7,k3_xboole_0(A_7,B_8)) = k4_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_8452,plain,(
    ! [A_120,B_121,C_122] : k4_xboole_0(k3_xboole_0(A_120,B_121),k3_xboole_0(A_120,k4_xboole_0(B_121,C_122))) = k3_xboole_0(k3_xboole_0(A_120,B_121),C_122) ),
    inference(superposition,[status(thm),theory(equality)],[c_527,c_14])).

tff(c_8753,plain,(
    ! [A_120,A_7,B_8] : k4_xboole_0(k3_xboole_0(A_120,A_7),k3_xboole_0(A_120,k4_xboole_0(A_7,B_8))) = k3_xboole_0(k3_xboole_0(A_120,A_7),k3_xboole_0(A_7,B_8)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_8452])).

tff(c_8883,plain,(
    ! [A_120,A_7,B_8] : k3_xboole_0(k3_xboole_0(A_120,A_7),k3_xboole_0(A_7,B_8)) = k3_xboole_0(k3_xboole_0(A_120,A_7),B_8) ),
    inference(demodulation,[status(thm),theory(equality)],[c_553,c_8753])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( r1_xboole_0(A_3,B_4)
      | k3_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_18,plain,(
    ~ r1_xboole_0(k3_xboole_0('#skF_3','#skF_1'),k3_xboole_0('#skF_3','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_21,plain,(
    ~ r1_xboole_0(k3_xboole_0('#skF_1','#skF_3'),k3_xboole_0('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_18])).

tff(c_125,plain,(
    k3_xboole_0(k3_xboole_0('#skF_1','#skF_3'),k3_xboole_0('#skF_3','#skF_2')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_21])).

tff(c_20906,plain,(
    k3_xboole_0(k3_xboole_0('#skF_1','#skF_3'),'#skF_2') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8883,c_125])).

tff(c_20909,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1147,c_2,c_20906])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n011.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 16:55:57 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.67/3.39  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.67/3.39  
% 8.67/3.39  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.67/3.40  %$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 8.67/3.40  
% 8.67/3.40  %Foreground sorts:
% 8.67/3.40  
% 8.67/3.40  
% 8.67/3.40  %Background operators:
% 8.67/3.40  
% 8.67/3.40  
% 8.67/3.40  %Foreground operators:
% 8.67/3.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.67/3.40  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 8.67/3.40  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.67/3.40  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 8.67/3.40  tff('#skF_2', type, '#skF_2': $i).
% 8.67/3.40  tff('#skF_3', type, '#skF_3': $i).
% 8.67/3.40  tff('#skF_1', type, '#skF_1': $i).
% 8.67/3.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.67/3.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.67/3.40  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.67/3.40  
% 8.85/3.41  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 8.85/3.41  tff(f_35, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 8.85/3.41  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 8.85/3.41  tff(f_33, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 8.85/3.41  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 8.85/3.41  tff(f_46, negated_conjecture, ~(![A, B, C]: (r1_xboole_0(A, B) => r1_xboole_0(k3_xboole_0(C, A), k3_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t76_xboole_1)).
% 8.85/3.41  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 8.85/3.41  tff(f_41, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_xboole_1)).
% 8.85/3.41  tff(c_14, plain, (![A_9, B_10]: (k4_xboole_0(A_9, k4_xboole_0(A_9, B_10))=k3_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.85/3.41  tff(c_10, plain, (![A_6]: (k4_xboole_0(A_6, k1_xboole_0)=A_6)), inference(cnfTransformation, [status(thm)], [f_35])).
% 8.85/3.41  tff(c_38, plain, (![B_16, A_17]: (k3_xboole_0(B_16, A_17)=k3_xboole_0(A_17, B_16))), inference(cnfTransformation, [status(thm)], [f_27])).
% 8.85/3.41  tff(c_8, plain, (![A_5]: (k3_xboole_0(A_5, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 8.85/3.41  tff(c_54, plain, (![A_17]: (k3_xboole_0(k1_xboole_0, A_17)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_38, c_8])).
% 8.85/3.41  tff(c_208, plain, (![A_27, B_28]: (k4_xboole_0(A_27, k3_xboole_0(A_27, B_28))=k4_xboole_0(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_37])).
% 8.85/3.41  tff(c_226, plain, (![A_17]: (k4_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, A_17))), inference(superposition, [status(thm), theory('equality')], [c_54, c_208])).
% 8.85/3.41  tff(c_241, plain, (![A_17]: (k4_xboole_0(k1_xboole_0, A_17)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_226])).
% 8.85/3.41  tff(c_20, plain, (r1_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_46])).
% 8.85/3.41  tff(c_126, plain, (![A_21, B_22]: (k3_xboole_0(A_21, B_22)=k1_xboole_0 | ~r1_xboole_0(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.85/3.41  tff(c_134, plain, (k3_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_20, c_126])).
% 8.85/3.41  tff(c_223, plain, (k4_xboole_0('#skF_1', k1_xboole_0)=k4_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_134, c_208])).
% 8.85/3.41  tff(c_240, plain, (k4_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_10, c_223])).
% 8.85/3.41  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 8.85/3.41  tff(c_232, plain, (![B_2, A_1]: (k4_xboole_0(B_2, k3_xboole_0(A_1, B_2))=k4_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_208])).
% 8.85/3.41  tff(c_527, plain, (![A_38, B_39, C_40]: (k4_xboole_0(k3_xboole_0(A_38, B_39), C_40)=k3_xboole_0(A_38, k4_xboole_0(B_39, C_40)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.85/3.41  tff(c_139, plain, (![A_23, B_24]: (k4_xboole_0(A_23, k4_xboole_0(A_23, B_24))=k3_xboole_0(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.85/3.41  tff(c_154, plain, (![A_6]: (k4_xboole_0(A_6, A_6)=k3_xboole_0(A_6, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_139])).
% 8.85/3.41  tff(c_157, plain, (![A_6]: (k4_xboole_0(A_6, A_6)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_154])).
% 8.85/3.41  tff(c_550, plain, (![A_38, B_39]: (k3_xboole_0(A_38, k4_xboole_0(B_39, k3_xboole_0(A_38, B_39)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_527, c_157])).
% 8.85/3.41  tff(c_630, plain, (![A_41, B_42]: (k3_xboole_0(A_41, k4_xboole_0(B_42, A_41))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_232, c_550])).
% 8.85/3.41  tff(c_676, plain, (k3_xboole_0('#skF_2', '#skF_1')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_240, c_630])).
% 8.85/3.41  tff(c_16, plain, (![A_11, B_12, C_13]: (k4_xboole_0(k3_xboole_0(A_11, B_12), C_13)=k3_xboole_0(A_11, k4_xboole_0(B_12, C_13)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.85/3.41  tff(c_711, plain, (![C_13]: (k3_xboole_0('#skF_2', k4_xboole_0('#skF_1', C_13))=k4_xboole_0(k1_xboole_0, C_13))), inference(superposition, [status(thm), theory('equality')], [c_676, c_16])).
% 8.85/3.41  tff(c_1090, plain, (![C_49]: (k3_xboole_0('#skF_2', k4_xboole_0('#skF_1', C_49))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_241, c_711])).
% 8.85/3.41  tff(c_1147, plain, (![B_10]: (k3_xboole_0('#skF_2', k3_xboole_0('#skF_1', B_10))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_14, c_1090])).
% 8.85/3.41  tff(c_553, plain, (![A_38, B_39, C_40]: (k4_xboole_0(k3_xboole_0(A_38, B_39), k3_xboole_0(A_38, k4_xboole_0(B_39, C_40)))=k3_xboole_0(k3_xboole_0(A_38, B_39), C_40))), inference(superposition, [status(thm), theory('equality')], [c_527, c_14])).
% 8.85/3.41  tff(c_12, plain, (![A_7, B_8]: (k4_xboole_0(A_7, k3_xboole_0(A_7, B_8))=k4_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 8.85/3.41  tff(c_8452, plain, (![A_120, B_121, C_122]: (k4_xboole_0(k3_xboole_0(A_120, B_121), k3_xboole_0(A_120, k4_xboole_0(B_121, C_122)))=k3_xboole_0(k3_xboole_0(A_120, B_121), C_122))), inference(superposition, [status(thm), theory('equality')], [c_527, c_14])).
% 8.85/3.41  tff(c_8753, plain, (![A_120, A_7, B_8]: (k4_xboole_0(k3_xboole_0(A_120, A_7), k3_xboole_0(A_120, k4_xboole_0(A_7, B_8)))=k3_xboole_0(k3_xboole_0(A_120, A_7), k3_xboole_0(A_7, B_8)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_8452])).
% 8.85/3.41  tff(c_8883, plain, (![A_120, A_7, B_8]: (k3_xboole_0(k3_xboole_0(A_120, A_7), k3_xboole_0(A_7, B_8))=k3_xboole_0(k3_xboole_0(A_120, A_7), B_8))), inference(demodulation, [status(thm), theory('equality')], [c_553, c_8753])).
% 8.85/3.41  tff(c_6, plain, (![A_3, B_4]: (r1_xboole_0(A_3, B_4) | k3_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.85/3.41  tff(c_18, plain, (~r1_xboole_0(k3_xboole_0('#skF_3', '#skF_1'), k3_xboole_0('#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_46])).
% 8.85/3.41  tff(c_21, plain, (~r1_xboole_0(k3_xboole_0('#skF_1', '#skF_3'), k3_xboole_0('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_18])).
% 8.85/3.41  tff(c_125, plain, (k3_xboole_0(k3_xboole_0('#skF_1', '#skF_3'), k3_xboole_0('#skF_3', '#skF_2'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_6, c_21])).
% 8.85/3.41  tff(c_20906, plain, (k3_xboole_0(k3_xboole_0('#skF_1', '#skF_3'), '#skF_2')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_8883, c_125])).
% 8.85/3.41  tff(c_20909, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1147, c_2, c_20906])).
% 8.85/3.41  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.85/3.41  
% 8.85/3.41  Inference rules
% 8.85/3.41  ----------------------
% 8.85/3.41  #Ref     : 0
% 8.85/3.41  #Sup     : 5175
% 8.85/3.41  #Fact    : 0
% 8.85/3.41  #Define  : 0
% 8.85/3.41  #Split   : 0
% 8.85/3.41  #Chain   : 0
% 8.85/3.41  #Close   : 0
% 8.85/3.41  
% 8.85/3.41  Ordering : KBO
% 8.85/3.41  
% 8.85/3.41  Simplification rules
% 8.85/3.41  ----------------------
% 8.85/3.41  #Subsume      : 33
% 8.85/3.41  #Demod        : 6484
% 8.85/3.41  #Tautology    : 3924
% 8.85/3.41  #SimpNegUnit  : 0
% 8.85/3.41  #BackRed      : 1
% 8.85/3.41  
% 8.85/3.41  #Partial instantiations: 0
% 8.85/3.41  #Strategies tried      : 1
% 8.85/3.41  
% 8.85/3.41  Timing (in seconds)
% 8.85/3.41  ----------------------
% 8.85/3.41  Preprocessing        : 0.26
% 8.85/3.41  Parsing              : 0.14
% 8.85/3.41  CNF conversion       : 0.02
% 8.85/3.41  Main loop            : 2.40
% 8.85/3.41  Inferencing          : 0.50
% 8.85/3.41  Reduction            : 1.43
% 8.85/3.41  Demodulation         : 1.29
% 8.85/3.41  BG Simplification    : 0.05
% 8.85/3.41  Subsumption          : 0.31
% 8.85/3.41  Abstraction          : 0.10
% 8.85/3.41  MUC search           : 0.00
% 8.85/3.41  Cooper               : 0.00
% 8.85/3.41  Total                : 2.69
% 8.85/3.41  Index Insertion      : 0.00
% 8.85/3.41  Index Deletion       : 0.00
% 8.85/3.42  Index Matching       : 0.00
% 8.85/3.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
