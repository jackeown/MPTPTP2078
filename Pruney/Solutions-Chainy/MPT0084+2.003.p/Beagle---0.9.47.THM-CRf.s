%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:04 EST 2020

% Result     : Theorem 4.65s
% Output     : CNFRefutation 4.65s
% Verified   : 
% Statistics : Number of formulae       :   52 (  60 expanded)
%              Number of leaves         :   23 (  29 expanded)
%              Depth                    :    8
%              Number of atoms          :   47 (  62 expanded)
%              Number of equality atoms :   33 (  39 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    5 (   2 average)

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

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_60,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( ~ r1_xboole_0(A,B)
          & r1_tarski(A,C)
          & r1_xboole_0(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_xboole_1)).

tff(f_51,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_39,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_35,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] : r1_tarski(k3_xboole_0(A,B),k2_xboole_0(A,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_xboole_1)).

tff(f_45,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_37,axiom,(
    ! [A,B,C] : k3_xboole_0(k3_xboole_0(A,B),C) = k3_xboole_0(A,k3_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

tff(c_282,plain,(
    ! [A_46,B_47] :
      ( r1_xboole_0(A_46,B_47)
      | k3_xboole_0(A_46,B_47) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_32,plain,(
    ~ r1_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_290,plain,(
    k3_xboole_0('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_282,c_32])).

tff(c_26,plain,(
    ! [A_21,B_22,C_23] : k4_xboole_0(k3_xboole_0(A_21,B_22),C_23) = k3_xboole_0(A_21,k4_xboole_0(B_22,C_23)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_14,plain,(
    ! [A_10] : k2_xboole_0(A_10,k1_xboole_0) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_30,plain,(
    r1_tarski('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_167,plain,(
    ! [A_36,B_37] :
      ( k4_xboole_0(A_36,B_37) = k1_xboole_0
      | ~ r1_tarski(A_36,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_183,plain,(
    k4_xboole_0('#skF_1','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_30,c_167])).

tff(c_403,plain,(
    ! [A_57,B_58] : k2_xboole_0(A_57,k4_xboole_0(B_58,A_57)) = k2_xboole_0(A_57,B_58) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_434,plain,(
    k2_xboole_0('#skF_3',k1_xboole_0) = k2_xboole_0('#skF_3','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_183,c_403])).

tff(c_450,plain,(
    k2_xboole_0('#skF_1','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_14,c_434])).

tff(c_16,plain,(
    ! [A_11,B_12,C_13] : r1_tarski(k3_xboole_0(A_11,B_12),k2_xboole_0(A_11,C_13)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1739,plain,(
    ! [A_93,B_94,C_95] : k4_xboole_0(k3_xboole_0(A_93,B_94),k2_xboole_0(A_93,C_95)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_16,c_167])).

tff(c_1908,plain,(
    ! [B_97] : k4_xboole_0(k3_xboole_0('#skF_1',B_97),'#skF_3') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_450,c_1739])).

tff(c_1955,plain,(
    ! [B_22] : k3_xboole_0('#skF_1',k4_xboole_0(B_22,'#skF_3')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_1908])).

tff(c_20,plain,(
    ! [A_16] : k4_xboole_0(A_16,k1_xboole_0) = A_16 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_28,plain,(
    r1_xboole_0('#skF_1',k3_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_137,plain,(
    ! [A_29,B_30] :
      ( k3_xboole_0(A_29,B_30) = k1_xboole_0
      | ~ r1_xboole_0(A_29,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_141,plain,(
    k3_xboole_0('#skF_1',k3_xboole_0('#skF_2','#skF_3')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_28,c_137])).

tff(c_12,plain,(
    ! [A_7,B_8,C_9] : k3_xboole_0(k3_xboole_0(A_7,B_8),C_9) = k3_xboole_0(A_7,k3_xboole_0(B_8,C_9)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_647,plain,(
    ! [A_64,B_65,C_66] : k4_xboole_0(k3_xboole_0(A_64,B_65),C_66) = k3_xboole_0(A_64,k4_xboole_0(B_65,C_66)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_22,plain,(
    ! [A_17,B_18] : k4_xboole_0(A_17,k3_xboole_0(A_17,B_18)) = k4_xboole_0(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_664,plain,(
    ! [A_64,B_65,B_18] : k3_xboole_0(A_64,k4_xboole_0(B_65,k3_xboole_0(k3_xboole_0(A_64,B_65),B_18))) = k4_xboole_0(k3_xboole_0(A_64,B_65),B_18) ),
    inference(superposition,[status(thm),theory(equality)],[c_647,c_22])).

tff(c_705,plain,(
    ! [A_64,B_65,B_18] : k3_xboole_0(A_64,k4_xboole_0(B_65,k3_xboole_0(k3_xboole_0(A_64,B_65),B_18))) = k3_xboole_0(A_64,k4_xboole_0(B_65,B_18)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_664])).

tff(c_6159,plain,(
    ! [A_150,B_151,B_152] : k3_xboole_0(A_150,k4_xboole_0(B_151,k3_xboole_0(A_150,k3_xboole_0(B_151,B_152)))) = k3_xboole_0(A_150,k4_xboole_0(B_151,B_152)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_705])).

tff(c_6390,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0('#skF_2',k1_xboole_0)) = k3_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_141,c_6159])).

tff(c_6454,plain,(
    k3_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1955,c_20,c_6390])).

tff(c_6456,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_290,c_6454])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:06:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.65/1.94  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.65/1.94  
% 4.65/1.94  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.65/1.95  %$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 4.65/1.95  
% 4.65/1.95  %Foreground sorts:
% 4.65/1.95  
% 4.65/1.95  
% 4.65/1.95  %Background operators:
% 4.65/1.95  
% 4.65/1.95  
% 4.65/1.95  %Foreground operators:
% 4.65/1.95  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.65/1.95  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.65/1.95  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.65/1.95  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.65/1.95  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.65/1.95  tff('#skF_2', type, '#skF_2': $i).
% 4.65/1.95  tff('#skF_3', type, '#skF_3': $i).
% 4.65/1.95  tff('#skF_1', type, '#skF_1': $i).
% 4.65/1.95  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.65/1.95  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.65/1.95  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.65/1.95  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.65/1.95  
% 4.65/1.96  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 4.65/1.96  tff(f_60, negated_conjecture, ~(![A, B, C]: ~((~r1_xboole_0(A, B) & r1_tarski(A, C)) & r1_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_xboole_1)).
% 4.65/1.96  tff(f_51, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_xboole_1)).
% 4.65/1.96  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 4.65/1.96  tff(f_39, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 4.65/1.96  tff(f_35, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 4.65/1.96  tff(f_43, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 4.65/1.96  tff(f_41, axiom, (![A, B, C]: r1_tarski(k3_xboole_0(A, B), k2_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_xboole_1)).
% 4.65/1.96  tff(f_45, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 4.65/1.96  tff(f_37, axiom, (![A, B, C]: (k3_xboole_0(k3_xboole_0(A, B), C) = k3_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_xboole_1)).
% 4.65/1.96  tff(f_47, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 4.65/1.96  tff(c_282, plain, (![A_46, B_47]: (r1_xboole_0(A_46, B_47) | k3_xboole_0(A_46, B_47)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.65/1.96  tff(c_32, plain, (~r1_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.65/1.96  tff(c_290, plain, (k3_xboole_0('#skF_1', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_282, c_32])).
% 4.65/1.96  tff(c_26, plain, (![A_21, B_22, C_23]: (k4_xboole_0(k3_xboole_0(A_21, B_22), C_23)=k3_xboole_0(A_21, k4_xboole_0(B_22, C_23)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.65/1.96  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.65/1.96  tff(c_14, plain, (![A_10]: (k2_xboole_0(A_10, k1_xboole_0)=A_10)), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.65/1.96  tff(c_30, plain, (r1_tarski('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.65/1.96  tff(c_167, plain, (![A_36, B_37]: (k4_xboole_0(A_36, B_37)=k1_xboole_0 | ~r1_tarski(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.65/1.96  tff(c_183, plain, (k4_xboole_0('#skF_1', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_30, c_167])).
% 4.65/1.96  tff(c_403, plain, (![A_57, B_58]: (k2_xboole_0(A_57, k4_xboole_0(B_58, A_57))=k2_xboole_0(A_57, B_58))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.65/1.96  tff(c_434, plain, (k2_xboole_0('#skF_3', k1_xboole_0)=k2_xboole_0('#skF_3', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_183, c_403])).
% 4.65/1.96  tff(c_450, plain, (k2_xboole_0('#skF_1', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2, c_14, c_434])).
% 4.65/1.96  tff(c_16, plain, (![A_11, B_12, C_13]: (r1_tarski(k3_xboole_0(A_11, B_12), k2_xboole_0(A_11, C_13)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.65/1.96  tff(c_1739, plain, (![A_93, B_94, C_95]: (k4_xboole_0(k3_xboole_0(A_93, B_94), k2_xboole_0(A_93, C_95))=k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_167])).
% 4.65/1.96  tff(c_1908, plain, (![B_97]: (k4_xboole_0(k3_xboole_0('#skF_1', B_97), '#skF_3')=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_450, c_1739])).
% 4.65/1.96  tff(c_1955, plain, (![B_22]: (k3_xboole_0('#skF_1', k4_xboole_0(B_22, '#skF_3'))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_26, c_1908])).
% 4.65/1.96  tff(c_20, plain, (![A_16]: (k4_xboole_0(A_16, k1_xboole_0)=A_16)), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.65/1.96  tff(c_28, plain, (r1_xboole_0('#skF_1', k3_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.65/1.96  tff(c_137, plain, (![A_29, B_30]: (k3_xboole_0(A_29, B_30)=k1_xboole_0 | ~r1_xboole_0(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.65/1.96  tff(c_141, plain, (k3_xboole_0('#skF_1', k3_xboole_0('#skF_2', '#skF_3'))=k1_xboole_0), inference(resolution, [status(thm)], [c_28, c_137])).
% 4.65/1.96  tff(c_12, plain, (![A_7, B_8, C_9]: (k3_xboole_0(k3_xboole_0(A_7, B_8), C_9)=k3_xboole_0(A_7, k3_xboole_0(B_8, C_9)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.65/1.96  tff(c_647, plain, (![A_64, B_65, C_66]: (k4_xboole_0(k3_xboole_0(A_64, B_65), C_66)=k3_xboole_0(A_64, k4_xboole_0(B_65, C_66)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.65/1.96  tff(c_22, plain, (![A_17, B_18]: (k4_xboole_0(A_17, k3_xboole_0(A_17, B_18))=k4_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.65/1.96  tff(c_664, plain, (![A_64, B_65, B_18]: (k3_xboole_0(A_64, k4_xboole_0(B_65, k3_xboole_0(k3_xboole_0(A_64, B_65), B_18)))=k4_xboole_0(k3_xboole_0(A_64, B_65), B_18))), inference(superposition, [status(thm), theory('equality')], [c_647, c_22])).
% 4.65/1.96  tff(c_705, plain, (![A_64, B_65, B_18]: (k3_xboole_0(A_64, k4_xboole_0(B_65, k3_xboole_0(k3_xboole_0(A_64, B_65), B_18)))=k3_xboole_0(A_64, k4_xboole_0(B_65, B_18)))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_664])).
% 4.65/1.96  tff(c_6159, plain, (![A_150, B_151, B_152]: (k3_xboole_0(A_150, k4_xboole_0(B_151, k3_xboole_0(A_150, k3_xboole_0(B_151, B_152))))=k3_xboole_0(A_150, k4_xboole_0(B_151, B_152)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_705])).
% 4.65/1.96  tff(c_6390, plain, (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', k1_xboole_0))=k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_141, c_6159])).
% 4.65/1.96  tff(c_6454, plain, (k3_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1955, c_20, c_6390])).
% 4.65/1.96  tff(c_6456, plain, $false, inference(negUnitSimplification, [status(thm)], [c_290, c_6454])).
% 4.65/1.96  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.65/1.96  
% 4.65/1.96  Inference rules
% 4.65/1.96  ----------------------
% 4.65/1.96  #Ref     : 0
% 4.65/1.96  #Sup     : 1610
% 4.65/1.96  #Fact    : 0
% 4.65/1.96  #Define  : 0
% 4.65/1.96  #Split   : 0
% 4.65/1.96  #Chain   : 0
% 4.65/1.96  #Close   : 0
% 4.65/1.96  
% 4.65/1.96  Ordering : KBO
% 4.65/1.96  
% 4.65/1.96  Simplification rules
% 4.65/1.96  ----------------------
% 4.65/1.96  #Subsume      : 0
% 4.65/1.96  #Demod        : 1535
% 4.65/1.96  #Tautology    : 1243
% 4.65/1.96  #SimpNegUnit  : 1
% 4.65/1.96  #BackRed      : 2
% 4.65/1.96  
% 4.65/1.96  #Partial instantiations: 0
% 4.65/1.96  #Strategies tried      : 1
% 4.65/1.96  
% 4.65/1.96  Timing (in seconds)
% 4.65/1.96  ----------------------
% 4.65/1.96  Preprocessing        : 0.30
% 4.65/1.96  Parsing              : 0.16
% 4.65/1.96  CNF conversion       : 0.02
% 4.65/1.96  Main loop            : 0.84
% 4.65/1.96  Inferencing          : 0.26
% 4.65/1.96  Reduction            : 0.38
% 4.65/1.96  Demodulation         : 0.31
% 4.65/1.96  BG Simplification    : 0.03
% 4.65/1.96  Subsumption          : 0.12
% 4.65/1.96  Abstraction          : 0.04
% 4.65/1.96  MUC search           : 0.00
% 4.65/1.96  Cooper               : 0.00
% 4.65/1.96  Total                : 1.17
% 4.65/1.96  Index Insertion      : 0.00
% 4.65/1.96  Index Deletion       : 0.00
% 4.65/1.96  Index Matching       : 0.00
% 4.65/1.96  BG Taut test         : 0.00
%------------------------------------------------------------------------------
