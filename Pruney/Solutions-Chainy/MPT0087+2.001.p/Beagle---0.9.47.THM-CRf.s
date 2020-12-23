%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:17 EST 2020

% Result     : Theorem 3.64s
% Output     : CNFRefutation 3.64s
% Verified   : 
% Statistics : Number of formulae       :   50 (  92 expanded)
%              Number of leaves         :   21 (  39 expanded)
%              Depth                    :   12
%              Number of atoms          :   43 (  90 expanded)
%              Number of equality atoms :   29 (  66 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_45,axiom,(
    ! [A,B,C] : k4_xboole_0(A,k4_xboole_0(B,C)) = k2_xboole_0(k4_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_52,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_xboole_0(A,B)
       => r1_xboole_0(A,k4_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_47,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_498,plain,(
    ! [A_58,B_59,C_60] : k2_xboole_0(k4_xboole_0(A_58,B_59),k3_xboole_0(A_58,C_60)) = k4_xboole_0(A_58,k4_xboole_0(B_59,C_60)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1366,plain,(
    ! [A_73,C_74,B_75] : k2_xboole_0(k3_xboole_0(A_73,C_74),k4_xboole_0(A_73,B_75)) = k4_xboole_0(A_73,k4_xboole_0(B_75,C_74)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_498])).

tff(c_18,plain,(
    ! [A_13,B_14] : k2_xboole_0(k3_xboole_0(A_13,B_14),k4_xboole_0(A_13,B_14)) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1471,plain,(
    ! [A_76,B_77] : k4_xboole_0(A_76,k4_xboole_0(B_77,B_77)) = A_76 ),
    inference(superposition,[status(thm),theory(equality)],[c_1366,c_18])).

tff(c_12,plain,(
    ! [A_7,B_8] : r1_tarski(k4_xboole_0(A_7,B_8),A_7) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_91,plain,(
    ! [A_32,B_33] :
      ( k4_xboole_0(A_32,B_33) = k1_xboole_0
      | ~ r1_tarski(A_32,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_95,plain,(
    ! [A_7,B_8] : k4_xboole_0(k4_xboole_0(A_7,B_8),A_7) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12,c_91])).

tff(c_1537,plain,(
    ! [A_76] : k4_xboole_0(A_76,A_76) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1471,c_95])).

tff(c_1373,plain,(
    ! [A_73,B_75] : k4_xboole_0(A_73,k4_xboole_0(B_75,B_75)) = A_73 ),
    inference(superposition,[status(thm),theory(equality)],[c_1366,c_18])).

tff(c_1769,plain,(
    ! [A_73] : k4_xboole_0(A_73,k1_xboole_0) = A_73 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1537,c_1373])).

tff(c_16,plain,(
    ! [A_11,B_12] : k4_xboole_0(A_11,k4_xboole_0(A_11,B_12)) = k3_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1532,plain,(
    ! [B_77] : k3_xboole_0(B_77,B_77) = B_77 ),
    inference(superposition,[status(thm),theory(equality)],[c_1471,c_16])).

tff(c_1771,plain,(
    ! [A_82] : k4_xboole_0(A_82,A_82) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1471,c_95])).

tff(c_1801,plain,(
    ! [A_82] : k2_xboole_0(k3_xboole_0(A_82,A_82),k1_xboole_0) = A_82 ),
    inference(superposition,[status(thm),theory(equality)],[c_1771,c_18])).

tff(c_2023,plain,(
    ! [A_86] : k2_xboole_0(A_86,k1_xboole_0) = A_86 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1532,c_1801])).

tff(c_2043,plain,(
    ! [B_2] : k2_xboole_0(k1_xboole_0,B_2) = B_2 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_2023])).

tff(c_26,plain,(
    r1_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_62,plain,(
    ! [A_26,B_27] :
      ( k3_xboole_0(A_26,B_27) = k1_xboole_0
      | ~ r1_xboole_0(A_26,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_70,plain,(
    k3_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_26,c_62])).

tff(c_540,plain,(
    ! [B_59] : k4_xboole_0('#skF_1',k4_xboole_0(B_59,'#skF_2')) = k2_xboole_0(k4_xboole_0('#skF_1',B_59),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_498])).

tff(c_555,plain,(
    ! [B_59] : k4_xboole_0('#skF_1',k4_xboole_0(B_59,'#skF_2')) = k2_xboole_0(k1_xboole_0,k4_xboole_0('#skF_1',B_59)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_540])).

tff(c_2897,plain,(
    ! [B_107] : k4_xboole_0('#skF_1',k4_xboole_0(B_107,'#skF_2')) = k4_xboole_0('#skF_1',B_107) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2043,c_555])).

tff(c_2983,plain,(
    ! [B_8] : k4_xboole_0('#skF_1',k4_xboole_0('#skF_2',B_8)) = k4_xboole_0('#skF_1',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_95,c_2897])).

tff(c_3089,plain,(
    ! [B_110] : k4_xboole_0('#skF_1',k4_xboole_0('#skF_2',B_110)) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1769,c_2983])).

tff(c_22,plain,(
    ! [A_18,B_19] : r1_xboole_0(k4_xboole_0(A_18,B_19),B_19) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_3137,plain,(
    ! [B_110] : r1_xboole_0('#skF_1',k4_xboole_0('#skF_2',B_110)) ),
    inference(superposition,[status(thm),theory(equality)],[c_3089,c_22])).

tff(c_24,plain,(
    ~ r1_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_3187,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3137,c_24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:39:51 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.64/1.66  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.64/1.66  
% 3.64/1.66  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.64/1.66  %$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.64/1.66  
% 3.64/1.66  %Foreground sorts:
% 3.64/1.66  
% 3.64/1.66  
% 3.64/1.66  %Background operators:
% 3.64/1.66  
% 3.64/1.66  
% 3.64/1.66  %Foreground operators:
% 3.64/1.66  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.64/1.66  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.64/1.66  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.64/1.66  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.64/1.66  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.64/1.66  tff('#skF_2', type, '#skF_2': $i).
% 3.64/1.66  tff('#skF_3', type, '#skF_3': $i).
% 3.64/1.66  tff('#skF_1', type, '#skF_1': $i).
% 3.64/1.66  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.64/1.66  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.64/1.66  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.64/1.66  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.64/1.66  
% 3.64/1.67  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 3.64/1.67  tff(f_45, axiom, (![A, B, C]: (k4_xboole_0(A, k4_xboole_0(B, C)) = k2_xboole_0(k4_xboole_0(A, B), k3_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_xboole_1)).
% 3.64/1.67  tff(f_43, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_xboole_1)).
% 3.64/1.67  tff(f_37, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 3.64/1.67  tff(f_35, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 3.64/1.67  tff(f_41, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.64/1.67  tff(f_52, negated_conjecture, ~(![A, B, C]: (r1_xboole_0(A, B) => r1_xboole_0(A, k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t80_xboole_1)).
% 3.64/1.67  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 3.64/1.67  tff(f_47, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 3.64/1.67  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.64/1.67  tff(c_498, plain, (![A_58, B_59, C_60]: (k2_xboole_0(k4_xboole_0(A_58, B_59), k3_xboole_0(A_58, C_60))=k4_xboole_0(A_58, k4_xboole_0(B_59, C_60)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.64/1.67  tff(c_1366, plain, (![A_73, C_74, B_75]: (k2_xboole_0(k3_xboole_0(A_73, C_74), k4_xboole_0(A_73, B_75))=k4_xboole_0(A_73, k4_xboole_0(B_75, C_74)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_498])).
% 3.64/1.67  tff(c_18, plain, (![A_13, B_14]: (k2_xboole_0(k3_xboole_0(A_13, B_14), k4_xboole_0(A_13, B_14))=A_13)), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.64/1.67  tff(c_1471, plain, (![A_76, B_77]: (k4_xboole_0(A_76, k4_xboole_0(B_77, B_77))=A_76)), inference(superposition, [status(thm), theory('equality')], [c_1366, c_18])).
% 3.64/1.67  tff(c_12, plain, (![A_7, B_8]: (r1_tarski(k4_xboole_0(A_7, B_8), A_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.64/1.67  tff(c_91, plain, (![A_32, B_33]: (k4_xboole_0(A_32, B_33)=k1_xboole_0 | ~r1_tarski(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.64/1.67  tff(c_95, plain, (![A_7, B_8]: (k4_xboole_0(k4_xboole_0(A_7, B_8), A_7)=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_91])).
% 3.64/1.67  tff(c_1537, plain, (![A_76]: (k4_xboole_0(A_76, A_76)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1471, c_95])).
% 3.64/1.67  tff(c_1373, plain, (![A_73, B_75]: (k4_xboole_0(A_73, k4_xboole_0(B_75, B_75))=A_73)), inference(superposition, [status(thm), theory('equality')], [c_1366, c_18])).
% 3.64/1.67  tff(c_1769, plain, (![A_73]: (k4_xboole_0(A_73, k1_xboole_0)=A_73)), inference(demodulation, [status(thm), theory('equality')], [c_1537, c_1373])).
% 3.64/1.67  tff(c_16, plain, (![A_11, B_12]: (k4_xboole_0(A_11, k4_xboole_0(A_11, B_12))=k3_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.64/1.67  tff(c_1532, plain, (![B_77]: (k3_xboole_0(B_77, B_77)=B_77)), inference(superposition, [status(thm), theory('equality')], [c_1471, c_16])).
% 3.64/1.67  tff(c_1771, plain, (![A_82]: (k4_xboole_0(A_82, A_82)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1471, c_95])).
% 3.64/1.67  tff(c_1801, plain, (![A_82]: (k2_xboole_0(k3_xboole_0(A_82, A_82), k1_xboole_0)=A_82)), inference(superposition, [status(thm), theory('equality')], [c_1771, c_18])).
% 3.64/1.67  tff(c_2023, plain, (![A_86]: (k2_xboole_0(A_86, k1_xboole_0)=A_86)), inference(demodulation, [status(thm), theory('equality')], [c_1532, c_1801])).
% 3.64/1.67  tff(c_2043, plain, (![B_2]: (k2_xboole_0(k1_xboole_0, B_2)=B_2)), inference(superposition, [status(thm), theory('equality')], [c_2, c_2023])).
% 3.64/1.67  tff(c_26, plain, (r1_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.64/1.67  tff(c_62, plain, (![A_26, B_27]: (k3_xboole_0(A_26, B_27)=k1_xboole_0 | ~r1_xboole_0(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.64/1.67  tff(c_70, plain, (k3_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_26, c_62])).
% 3.64/1.67  tff(c_540, plain, (![B_59]: (k4_xboole_0('#skF_1', k4_xboole_0(B_59, '#skF_2'))=k2_xboole_0(k4_xboole_0('#skF_1', B_59), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_70, c_498])).
% 3.64/1.67  tff(c_555, plain, (![B_59]: (k4_xboole_0('#skF_1', k4_xboole_0(B_59, '#skF_2'))=k2_xboole_0(k1_xboole_0, k4_xboole_0('#skF_1', B_59)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_540])).
% 3.64/1.67  tff(c_2897, plain, (![B_107]: (k4_xboole_0('#skF_1', k4_xboole_0(B_107, '#skF_2'))=k4_xboole_0('#skF_1', B_107))), inference(demodulation, [status(thm), theory('equality')], [c_2043, c_555])).
% 3.64/1.67  tff(c_2983, plain, (![B_8]: (k4_xboole_0('#skF_1', k4_xboole_0('#skF_2', B_8))=k4_xboole_0('#skF_1', k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_95, c_2897])).
% 3.64/1.67  tff(c_3089, plain, (![B_110]: (k4_xboole_0('#skF_1', k4_xboole_0('#skF_2', B_110))='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1769, c_2983])).
% 3.64/1.67  tff(c_22, plain, (![A_18, B_19]: (r1_xboole_0(k4_xboole_0(A_18, B_19), B_19))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.64/1.67  tff(c_3137, plain, (![B_110]: (r1_xboole_0('#skF_1', k4_xboole_0('#skF_2', B_110)))), inference(superposition, [status(thm), theory('equality')], [c_3089, c_22])).
% 3.64/1.67  tff(c_24, plain, (~r1_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.64/1.67  tff(c_3187, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3137, c_24])).
% 3.64/1.67  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.64/1.67  
% 3.64/1.67  Inference rules
% 3.64/1.67  ----------------------
% 3.64/1.67  #Ref     : 0
% 3.64/1.67  #Sup     : 807
% 3.64/1.67  #Fact    : 0
% 3.64/1.67  #Define  : 0
% 3.64/1.67  #Split   : 0
% 3.64/1.67  #Chain   : 0
% 3.64/1.67  #Close   : 0
% 3.64/1.67  
% 3.64/1.67  Ordering : KBO
% 3.64/1.67  
% 3.64/1.67  Simplification rules
% 3.64/1.67  ----------------------
% 3.64/1.67  #Subsume      : 3
% 3.64/1.67  #Demod        : 845
% 3.64/1.67  #Tautology    : 604
% 3.64/1.67  #SimpNegUnit  : 0
% 3.64/1.67  #BackRed      : 22
% 3.64/1.67  
% 3.64/1.67  #Partial instantiations: 0
% 3.64/1.67  #Strategies tried      : 1
% 3.64/1.67  
% 3.64/1.67  Timing (in seconds)
% 3.64/1.67  ----------------------
% 3.64/1.68  Preprocessing        : 0.26
% 3.64/1.68  Parsing              : 0.14
% 3.64/1.68  CNF conversion       : 0.02
% 3.64/1.68  Main loop            : 0.63
% 3.64/1.68  Inferencing          : 0.20
% 3.64/1.68  Reduction            : 0.28
% 3.64/1.68  Demodulation         : 0.23
% 3.64/1.68  BG Simplification    : 0.03
% 3.64/1.68  Subsumption          : 0.08
% 3.64/1.68  Abstraction          : 0.03
% 3.64/1.68  MUC search           : 0.00
% 3.64/1.68  Cooper               : 0.00
% 3.64/1.68  Total                : 0.91
% 3.64/1.68  Index Insertion      : 0.00
% 3.64/1.68  Index Deletion       : 0.00
% 3.64/1.68  Index Matching       : 0.00
% 3.64/1.68  BG Taut test         : 0.00
%------------------------------------------------------------------------------
