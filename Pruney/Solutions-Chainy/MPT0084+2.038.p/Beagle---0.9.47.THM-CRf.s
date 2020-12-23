%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:09 EST 2020

% Result     : Theorem 3.85s
% Output     : CNFRefutation 4.18s
% Verified   : 
% Statistics : Number of formulae       :   53 (  66 expanded)
%              Number of leaves         :   20 (  30 expanded)
%              Depth                    :    9
%              Number of atoms          :   55 (  77 expanded)
%              Number of equality atoms :   34 (  44 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_58,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( ~ r1_xboole_0(A,B)
          & r1_tarski(A,C)
          & r1_xboole_0(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_41,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_39,axiom,(
    ! [A,B,C] : k3_xboole_0(k3_xboole_0(A,B),C) = k3_xboole_0(A,k3_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_43,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_37,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(c_54,plain,(
    ! [A_25,B_26] :
      ( r1_xboole_0(A_25,B_26)
      | k3_xboole_0(A_25,B_26) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_28,plain,(
    ~ r1_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_61,plain,(
    k3_xboole_0('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_54,c_28])).

tff(c_20,plain,(
    ! [A_14,B_15] : k4_xboole_0(A_14,k4_xboole_0(A_14,B_15)) = k3_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_18,plain,(
    ! [A_12,B_13] : k4_xboole_0(A_12,k3_xboole_0(A_12,B_13)) = k4_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_137,plain,(
    ! [A_35,B_36] : k4_xboole_0(A_35,k4_xboole_0(A_35,B_36)) = k3_xboole_0(A_35,B_36) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_158,plain,(
    ! [A_12,B_13] : k4_xboole_0(A_12,k4_xboole_0(A_12,B_13)) = k3_xboole_0(A_12,k3_xboole_0(A_12,B_13)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_137])).

tff(c_171,plain,(
    ! [A_12,B_13] : k3_xboole_0(A_12,k3_xboole_0(A_12,B_13)) = k3_xboole_0(A_12,B_13) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_158])).

tff(c_14,plain,(
    ! [A_10] : k3_xboole_0(A_10,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_12,plain,(
    ! [A_7,B_8,C_9] : k3_xboole_0(k3_xboole_0(A_7,B_8),C_9) = k3_xboole_0(A_7,k3_xboole_0(B_8,C_9)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_227,plain,(
    ! [A_39,B_40,C_41] : k3_xboole_0(k3_xboole_0(A_39,B_40),C_41) = k3_xboole_0(A_39,k3_xboole_0(B_40,C_41)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_24,plain,(
    r1_xboole_0('#skF_1',k3_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_45,plain,(
    ! [B_21,A_22] :
      ( r1_xboole_0(B_21,A_22)
      | ~ r1_xboole_0(A_22,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_48,plain,(
    r1_xboole_0(k3_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_45])).

tff(c_75,plain,(
    ! [A_29,B_30] :
      ( k3_xboole_0(A_29,B_30) = k1_xboole_0
      | ~ r1_xboole_0(A_29,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_86,plain,(
    k3_xboole_0(k3_xboole_0('#skF_2','#skF_3'),'#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_48,c_75])).

tff(c_243,plain,(
    k3_xboole_0('#skF_2',k3_xboole_0('#skF_3','#skF_1')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_227,c_86])).

tff(c_6,plain,(
    ! [B_4,A_3] :
      ( r1_xboole_0(B_4,A_3)
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_121,plain,(
    ! [B_33,A_34] :
      ( r1_xboole_0(B_33,A_34)
      | k3_xboole_0(A_34,B_33) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_54,c_6])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_1762,plain,(
    ! [B_64,A_65] :
      ( k3_xboole_0(B_64,A_65) = k1_xboole_0
      | k3_xboole_0(A_65,B_64) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_121,c_2])).

tff(c_1830,plain,(
    k3_xboole_0(k3_xboole_0('#skF_3','#skF_1'),'#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_243,c_1762])).

tff(c_2336,plain,(
    k3_xboole_0('#skF_3',k3_xboole_0('#skF_1','#skF_2')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_1830])).

tff(c_16,plain,(
    ! [A_11] : k4_xboole_0(A_11,k1_xboole_0) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_26,plain,(
    r1_tarski('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_62,plain,(
    ! [A_27,B_28] :
      ( k4_xboole_0(A_27,B_28) = k1_xboole_0
      | ~ r1_tarski(A_27,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_70,plain,(
    k4_xboole_0('#skF_1','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_26,c_62])).

tff(c_161,plain,(
    k4_xboole_0('#skF_1',k1_xboole_0) = k3_xboole_0('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_137])).

tff(c_172,plain,(
    k3_xboole_0('#skF_1','#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_161])).

tff(c_2752,plain,(
    ! [C_75] : k3_xboole_0('#skF_1',k3_xboole_0('#skF_3',C_75)) = k3_xboole_0('#skF_1',C_75) ),
    inference(superposition,[status(thm),theory(equality)],[c_172,c_227])).

tff(c_2795,plain,(
    k3_xboole_0('#skF_1',k3_xboole_0('#skF_1','#skF_2')) = k3_xboole_0('#skF_1',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_2336,c_2752])).

tff(c_2840,plain,(
    k3_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_171,c_14,c_2795])).

tff(c_2842,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_61,c_2840])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:21:55 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.85/1.70  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.18/1.71  
% 4.18/1.71  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.18/1.71  %$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 4.18/1.71  
% 4.18/1.71  %Foreground sorts:
% 4.18/1.71  
% 4.18/1.71  
% 4.18/1.71  %Background operators:
% 4.18/1.71  
% 4.18/1.71  
% 4.18/1.71  %Foreground operators:
% 4.18/1.71  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.18/1.71  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.18/1.71  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.18/1.71  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.18/1.71  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.18/1.71  tff('#skF_2', type, '#skF_2': $i).
% 4.18/1.71  tff('#skF_3', type, '#skF_3': $i).
% 4.18/1.71  tff('#skF_1', type, '#skF_1': $i).
% 4.18/1.71  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.18/1.71  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.18/1.71  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.18/1.71  
% 4.18/1.72  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 4.18/1.72  tff(f_58, negated_conjecture, ~(![A, B, C]: ~((~r1_xboole_0(A, B) & r1_tarski(A, C)) & r1_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_xboole_1)).
% 4.18/1.72  tff(f_47, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 4.18/1.72  tff(f_45, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 4.18/1.72  tff(f_41, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 4.18/1.72  tff(f_39, axiom, (![A, B, C]: (k3_xboole_0(k3_xboole_0(A, B), C) = k3_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_xboole_1)).
% 4.18/1.72  tff(f_33, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 4.18/1.72  tff(f_43, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 4.18/1.72  tff(f_37, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 4.18/1.72  tff(c_54, plain, (![A_25, B_26]: (r1_xboole_0(A_25, B_26) | k3_xboole_0(A_25, B_26)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.18/1.72  tff(c_28, plain, (~r1_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.18/1.72  tff(c_61, plain, (k3_xboole_0('#skF_1', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_54, c_28])).
% 4.18/1.72  tff(c_20, plain, (![A_14, B_15]: (k4_xboole_0(A_14, k4_xboole_0(A_14, B_15))=k3_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.18/1.72  tff(c_18, plain, (![A_12, B_13]: (k4_xboole_0(A_12, k3_xboole_0(A_12, B_13))=k4_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.18/1.72  tff(c_137, plain, (![A_35, B_36]: (k4_xboole_0(A_35, k4_xboole_0(A_35, B_36))=k3_xboole_0(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.18/1.72  tff(c_158, plain, (![A_12, B_13]: (k4_xboole_0(A_12, k4_xboole_0(A_12, B_13))=k3_xboole_0(A_12, k3_xboole_0(A_12, B_13)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_137])).
% 4.18/1.72  tff(c_171, plain, (![A_12, B_13]: (k3_xboole_0(A_12, k3_xboole_0(A_12, B_13))=k3_xboole_0(A_12, B_13))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_158])).
% 4.18/1.72  tff(c_14, plain, (![A_10]: (k3_xboole_0(A_10, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.18/1.72  tff(c_12, plain, (![A_7, B_8, C_9]: (k3_xboole_0(k3_xboole_0(A_7, B_8), C_9)=k3_xboole_0(A_7, k3_xboole_0(B_8, C_9)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.18/1.72  tff(c_227, plain, (![A_39, B_40, C_41]: (k3_xboole_0(k3_xboole_0(A_39, B_40), C_41)=k3_xboole_0(A_39, k3_xboole_0(B_40, C_41)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.18/1.72  tff(c_24, plain, (r1_xboole_0('#skF_1', k3_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.18/1.72  tff(c_45, plain, (![B_21, A_22]: (r1_xboole_0(B_21, A_22) | ~r1_xboole_0(A_22, B_21))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.18/1.72  tff(c_48, plain, (r1_xboole_0(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_24, c_45])).
% 4.18/1.72  tff(c_75, plain, (![A_29, B_30]: (k3_xboole_0(A_29, B_30)=k1_xboole_0 | ~r1_xboole_0(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.18/1.72  tff(c_86, plain, (k3_xboole_0(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_48, c_75])).
% 4.18/1.72  tff(c_243, plain, (k3_xboole_0('#skF_2', k3_xboole_0('#skF_3', '#skF_1'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_227, c_86])).
% 4.18/1.72  tff(c_6, plain, (![B_4, A_3]: (r1_xboole_0(B_4, A_3) | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.18/1.72  tff(c_121, plain, (![B_33, A_34]: (r1_xboole_0(B_33, A_34) | k3_xboole_0(A_34, B_33)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_54, c_6])).
% 4.18/1.72  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.18/1.72  tff(c_1762, plain, (![B_64, A_65]: (k3_xboole_0(B_64, A_65)=k1_xboole_0 | k3_xboole_0(A_65, B_64)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_121, c_2])).
% 4.18/1.72  tff(c_1830, plain, (k3_xboole_0(k3_xboole_0('#skF_3', '#skF_1'), '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_243, c_1762])).
% 4.18/1.72  tff(c_2336, plain, (k3_xboole_0('#skF_3', k3_xboole_0('#skF_1', '#skF_2'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_12, c_1830])).
% 4.18/1.72  tff(c_16, plain, (![A_11]: (k4_xboole_0(A_11, k1_xboole_0)=A_11)), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.18/1.72  tff(c_26, plain, (r1_tarski('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.18/1.72  tff(c_62, plain, (![A_27, B_28]: (k4_xboole_0(A_27, B_28)=k1_xboole_0 | ~r1_tarski(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.18/1.72  tff(c_70, plain, (k4_xboole_0('#skF_1', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_26, c_62])).
% 4.18/1.72  tff(c_161, plain, (k4_xboole_0('#skF_1', k1_xboole_0)=k3_xboole_0('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_70, c_137])).
% 4.18/1.72  tff(c_172, plain, (k3_xboole_0('#skF_1', '#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_16, c_161])).
% 4.18/1.72  tff(c_2752, plain, (![C_75]: (k3_xboole_0('#skF_1', k3_xboole_0('#skF_3', C_75))=k3_xboole_0('#skF_1', C_75))), inference(superposition, [status(thm), theory('equality')], [c_172, c_227])).
% 4.18/1.72  tff(c_2795, plain, (k3_xboole_0('#skF_1', k3_xboole_0('#skF_1', '#skF_2'))=k3_xboole_0('#skF_1', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2336, c_2752])).
% 4.18/1.72  tff(c_2840, plain, (k3_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_171, c_14, c_2795])).
% 4.18/1.72  tff(c_2842, plain, $false, inference(negUnitSimplification, [status(thm)], [c_61, c_2840])).
% 4.18/1.72  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.18/1.72  
% 4.18/1.72  Inference rules
% 4.18/1.72  ----------------------
% 4.18/1.72  #Ref     : 0
% 4.18/1.72  #Sup     : 710
% 4.18/1.72  #Fact    : 0
% 4.18/1.72  #Define  : 0
% 4.18/1.72  #Split   : 1
% 4.18/1.72  #Chain   : 0
% 4.18/1.72  #Close   : 0
% 4.18/1.72  
% 4.18/1.72  Ordering : KBO
% 4.18/1.72  
% 4.18/1.72  Simplification rules
% 4.18/1.72  ----------------------
% 4.18/1.72  #Subsume      : 3
% 4.18/1.72  #Demod        : 969
% 4.18/1.72  #Tautology    : 466
% 4.18/1.72  #SimpNegUnit  : 1
% 4.18/1.72  #BackRed      : 5
% 4.18/1.72  
% 4.18/1.72  #Partial instantiations: 0
% 4.18/1.72  #Strategies tried      : 1
% 4.18/1.72  
% 4.18/1.72  Timing (in seconds)
% 4.18/1.72  ----------------------
% 4.18/1.72  Preprocessing        : 0.28
% 4.18/1.72  Parsing              : 0.15
% 4.18/1.72  CNF conversion       : 0.02
% 4.18/1.72  Main loop            : 0.67
% 4.18/1.72  Inferencing          : 0.21
% 4.18/1.72  Reduction            : 0.31
% 4.18/1.72  Demodulation         : 0.26
% 4.18/1.72  BG Simplification    : 0.02
% 4.18/1.72  Subsumption          : 0.09
% 4.18/1.72  Abstraction          : 0.04
% 4.18/1.72  MUC search           : 0.00
% 4.18/1.72  Cooper               : 0.00
% 4.18/1.72  Total                : 0.98
% 4.18/1.72  Index Insertion      : 0.00
% 4.18/1.72  Index Deletion       : 0.00
% 4.18/1.72  Index Matching       : 0.00
% 4.18/1.72  BG Taut test         : 0.00
%------------------------------------------------------------------------------
