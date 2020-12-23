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
% DateTime   : Thu Dec  3 09:44:20 EST 2020

% Result     : Theorem 12.75s
% Output     : CNFRefutation 12.75s
% Verified   : 
% Statistics : Number of formulae       :   59 (  90 expanded)
%              Number of leaves         :   21 (  38 expanded)
%              Depth                    :   11
%              Number of atoms          :   58 (  98 expanded)
%              Number of equality atoms :   41 (  68 expanded)
%              Maximal formula depth    :    6 (   3 average)
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

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_52,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_xboole_0(A,k4_xboole_0(B,C))
       => r1_xboole_0(B,k4_xboole_0(A,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_xboole_1)).

tff(f_43,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_37,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_41,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_47,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

tff(c_99,plain,(
    ! [A_27,B_28] :
      ( r1_xboole_0(A_27,B_28)
      | k3_xboole_0(A_27,B_28) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    ! [B_6,A_5] :
      ( r1_xboole_0(B_6,A_5)
      | ~ r1_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_111,plain,(
    ! [B_29,A_30] :
      ( r1_xboole_0(B_29,A_30)
      | k3_xboole_0(A_30,B_29) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_99,c_8])).

tff(c_22,plain,(
    ~ r1_xboole_0('#skF_2',k4_xboole_0('#skF_1','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_122,plain,(
    k3_xboole_0(k4_xboole_0('#skF_1','#skF_3'),'#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_111,c_22])).

tff(c_358,plain,(
    ! [A_44,B_45,C_46] : k4_xboole_0(k4_xboole_0(A_44,B_45),C_46) = k4_xboole_0(A_44,k2_xboole_0(B_45,C_46)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_18,plain,(
    ! [A_14,B_15] : k4_xboole_0(A_14,k4_xboole_0(A_14,B_15)) = k3_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_374,plain,(
    ! [A_44,B_45,C_46] : k4_xboole_0(k4_xboole_0(A_44,B_45),k4_xboole_0(A_44,k2_xboole_0(B_45,C_46))) = k3_xboole_0(k4_xboole_0(A_44,B_45),C_46) ),
    inference(superposition,[status(thm),theory(equality)],[c_358,c_18])).

tff(c_12,plain,(
    ! [A_8,B_9] : k2_xboole_0(A_8,k4_xboole_0(B_9,A_8)) = k2_xboole_0(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_10111,plain,(
    ! [A_167,B_168,C_169] : k4_xboole_0(k4_xboole_0(A_167,B_168),k4_xboole_0(A_167,k2_xboole_0(B_168,C_169))) = k3_xboole_0(k4_xboole_0(A_167,B_168),C_169) ),
    inference(superposition,[status(thm),theory(equality)],[c_358,c_18])).

tff(c_10424,plain,(
    ! [A_167,A_8,B_9] : k4_xboole_0(k4_xboole_0(A_167,A_8),k4_xboole_0(A_167,k2_xboole_0(A_8,B_9))) = k3_xboole_0(k4_xboole_0(A_167,A_8),k4_xboole_0(B_9,A_8)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_10111])).

tff(c_19624,plain,(
    ! [A_228,A_229,B_230] : k3_xboole_0(k4_xboole_0(A_228,A_229),k4_xboole_0(B_230,A_229)) = k3_xboole_0(k4_xboole_0(A_228,A_229),B_230) ),
    inference(demodulation,[status(thm),theory(equality)],[c_374,c_10424])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_10,plain,(
    ! [A_7] : k3_xboole_0(A_7,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_14,plain,(
    ! [A_10] : k4_xboole_0(A_10,k1_xboole_0) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_123,plain,(
    ! [A_31,B_32] : k4_xboole_0(A_31,k4_xboole_0(A_31,B_32)) = k3_xboole_0(A_31,B_32) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_138,plain,(
    ! [A_10] : k4_xboole_0(A_10,A_10) = k3_xboole_0(A_10,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_123])).

tff(c_141,plain,(
    ! [A_10] : k4_xboole_0(A_10,A_10) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_138])).

tff(c_368,plain,(
    ! [A_44,B_45] : k4_xboole_0(A_44,k2_xboole_0(B_45,k4_xboole_0(A_44,B_45))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_358,c_141])).

tff(c_423,plain,(
    ! [A_47,B_48] : k4_xboole_0(A_47,k2_xboole_0(B_48,A_47)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_368])).

tff(c_477,plain,(
    ! [A_1,B_2] : k4_xboole_0(A_1,k2_xboole_0(A_1,B_2)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_423])).

tff(c_231,plain,(
    ! [A_38,B_39,C_40] : k4_xboole_0(k3_xboole_0(A_38,B_39),C_40) = k3_xboole_0(A_38,k4_xboole_0(B_39,C_40)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_275,plain,(
    ! [A_7,C_40] : k3_xboole_0(A_7,k4_xboole_0(k1_xboole_0,C_40)) = k4_xboole_0(k1_xboole_0,C_40) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_231])).

tff(c_650,plain,(
    ! [A_52,C_53] : k4_xboole_0(A_52,k2_xboole_0(k1_xboole_0,C_53)) = k4_xboole_0(A_52,C_53) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_358])).

tff(c_672,plain,(
    ! [C_53,A_7] : k4_xboole_0(k1_xboole_0,k2_xboole_0(k1_xboole_0,C_53)) = k3_xboole_0(A_7,k4_xboole_0(k1_xboole_0,C_53)) ),
    inference(superposition,[status(thm),theory(equality)],[c_650,c_275])).

tff(c_729,plain,(
    ! [C_53] : k4_xboole_0(k1_xboole_0,C_53) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_477,c_275,c_672])).

tff(c_24,plain,(
    r1_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_41,plain,(
    ! [B_21,A_22] :
      ( r1_xboole_0(B_21,A_22)
      | ~ r1_xboole_0(A_22,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_44,plain,(
    r1_xboole_0(k4_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_41])).

tff(c_82,plain,(
    ! [A_25,B_26] :
      ( k3_xboole_0(A_25,B_26) = k1_xboole_0
      | ~ r1_xboole_0(A_25,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_89,plain,(
    k3_xboole_0(k4_xboole_0('#skF_2','#skF_3'),'#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_44,c_82])).

tff(c_269,plain,(
    ! [C_40] : k3_xboole_0(k4_xboole_0('#skF_2','#skF_3'),k4_xboole_0('#skF_1',C_40)) = k4_xboole_0(k1_xboole_0,C_40) ),
    inference(superposition,[status(thm),theory(equality)],[c_89,c_231])).

tff(c_845,plain,(
    ! [C_40] : k3_xboole_0(k4_xboole_0('#skF_2','#skF_3'),k4_xboole_0('#skF_1',C_40)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_729,c_269])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( k3_xboole_0(A_3,B_4) = k1_xboole_0
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1527,plain,(
    ! [B_70,A_71] :
      ( k3_xboole_0(B_70,A_71) = k1_xboole_0
      | k3_xboole_0(A_71,B_70) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_111,c_4])).

tff(c_1550,plain,(
    ! [C_40] : k3_xboole_0(k4_xboole_0('#skF_1',C_40),k4_xboole_0('#skF_2','#skF_3')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_845,c_1527])).

tff(c_19631,plain,(
    k3_xboole_0(k4_xboole_0('#skF_1','#skF_3'),'#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_19624,c_1550])).

tff(c_20060,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_122,c_19631])).
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
% 0.14/0.34  % DateTime   : Tue Dec  1 19:37:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 12.75/6.00  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.75/6.00  
% 12.75/6.00  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.75/6.01  %$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 12.75/6.01  
% 12.75/6.01  %Foreground sorts:
% 12.75/6.01  
% 12.75/6.01  
% 12.75/6.01  %Background operators:
% 12.75/6.01  
% 12.75/6.01  
% 12.75/6.01  %Foreground operators:
% 12.75/6.01  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 12.75/6.01  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 12.75/6.01  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 12.75/6.01  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 12.75/6.01  tff('#skF_2', type, '#skF_2': $i).
% 12.75/6.01  tff('#skF_3', type, '#skF_3': $i).
% 12.75/6.01  tff('#skF_1', type, '#skF_1': $i).
% 12.75/6.01  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 12.75/6.01  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 12.75/6.01  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 12.75/6.01  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 12.75/6.01  
% 12.75/6.03  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 12.75/6.03  tff(f_35, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 12.75/6.03  tff(f_52, negated_conjecture, ~(![A, B, C]: (r1_xboole_0(A, k4_xboole_0(B, C)) => r1_xboole_0(B, k4_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_xboole_1)).
% 12.75/6.03  tff(f_43, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 12.75/6.03  tff(f_45, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 12.75/6.03  tff(f_39, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 12.75/6.03  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 12.75/6.03  tff(f_37, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 12.75/6.03  tff(f_41, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 12.75/6.03  tff(f_47, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_xboole_1)).
% 12.75/6.03  tff(c_99, plain, (![A_27, B_28]: (r1_xboole_0(A_27, B_28) | k3_xboole_0(A_27, B_28)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 12.75/6.03  tff(c_8, plain, (![B_6, A_5]: (r1_xboole_0(B_6, A_5) | ~r1_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 12.75/6.03  tff(c_111, plain, (![B_29, A_30]: (r1_xboole_0(B_29, A_30) | k3_xboole_0(A_30, B_29)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_99, c_8])).
% 12.75/6.03  tff(c_22, plain, (~r1_xboole_0('#skF_2', k4_xboole_0('#skF_1', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_52])).
% 12.75/6.03  tff(c_122, plain, (k3_xboole_0(k4_xboole_0('#skF_1', '#skF_3'), '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_111, c_22])).
% 12.75/6.03  tff(c_358, plain, (![A_44, B_45, C_46]: (k4_xboole_0(k4_xboole_0(A_44, B_45), C_46)=k4_xboole_0(A_44, k2_xboole_0(B_45, C_46)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 12.75/6.03  tff(c_18, plain, (![A_14, B_15]: (k4_xboole_0(A_14, k4_xboole_0(A_14, B_15))=k3_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_45])).
% 12.75/6.03  tff(c_374, plain, (![A_44, B_45, C_46]: (k4_xboole_0(k4_xboole_0(A_44, B_45), k4_xboole_0(A_44, k2_xboole_0(B_45, C_46)))=k3_xboole_0(k4_xboole_0(A_44, B_45), C_46))), inference(superposition, [status(thm), theory('equality')], [c_358, c_18])).
% 12.75/6.03  tff(c_12, plain, (![A_8, B_9]: (k2_xboole_0(A_8, k4_xboole_0(B_9, A_8))=k2_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_39])).
% 12.75/6.03  tff(c_10111, plain, (![A_167, B_168, C_169]: (k4_xboole_0(k4_xboole_0(A_167, B_168), k4_xboole_0(A_167, k2_xboole_0(B_168, C_169)))=k3_xboole_0(k4_xboole_0(A_167, B_168), C_169))), inference(superposition, [status(thm), theory('equality')], [c_358, c_18])).
% 12.75/6.03  tff(c_10424, plain, (![A_167, A_8, B_9]: (k4_xboole_0(k4_xboole_0(A_167, A_8), k4_xboole_0(A_167, k2_xboole_0(A_8, B_9)))=k3_xboole_0(k4_xboole_0(A_167, A_8), k4_xboole_0(B_9, A_8)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_10111])).
% 12.75/6.03  tff(c_19624, plain, (![A_228, A_229, B_230]: (k3_xboole_0(k4_xboole_0(A_228, A_229), k4_xboole_0(B_230, A_229))=k3_xboole_0(k4_xboole_0(A_228, A_229), B_230))), inference(demodulation, [status(thm), theory('equality')], [c_374, c_10424])).
% 12.75/6.03  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 12.75/6.03  tff(c_10, plain, (![A_7]: (k3_xboole_0(A_7, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 12.75/6.03  tff(c_14, plain, (![A_10]: (k4_xboole_0(A_10, k1_xboole_0)=A_10)), inference(cnfTransformation, [status(thm)], [f_41])).
% 12.75/6.03  tff(c_123, plain, (![A_31, B_32]: (k4_xboole_0(A_31, k4_xboole_0(A_31, B_32))=k3_xboole_0(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_45])).
% 12.75/6.03  tff(c_138, plain, (![A_10]: (k4_xboole_0(A_10, A_10)=k3_xboole_0(A_10, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_14, c_123])).
% 12.75/6.03  tff(c_141, plain, (![A_10]: (k4_xboole_0(A_10, A_10)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_138])).
% 12.75/6.03  tff(c_368, plain, (![A_44, B_45]: (k4_xboole_0(A_44, k2_xboole_0(B_45, k4_xboole_0(A_44, B_45)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_358, c_141])).
% 12.75/6.03  tff(c_423, plain, (![A_47, B_48]: (k4_xboole_0(A_47, k2_xboole_0(B_48, A_47))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_368])).
% 12.75/6.03  tff(c_477, plain, (![A_1, B_2]: (k4_xboole_0(A_1, k2_xboole_0(A_1, B_2))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_423])).
% 12.75/6.03  tff(c_231, plain, (![A_38, B_39, C_40]: (k4_xboole_0(k3_xboole_0(A_38, B_39), C_40)=k3_xboole_0(A_38, k4_xboole_0(B_39, C_40)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 12.75/6.03  tff(c_275, plain, (![A_7, C_40]: (k3_xboole_0(A_7, k4_xboole_0(k1_xboole_0, C_40))=k4_xboole_0(k1_xboole_0, C_40))), inference(superposition, [status(thm), theory('equality')], [c_10, c_231])).
% 12.75/6.03  tff(c_650, plain, (![A_52, C_53]: (k4_xboole_0(A_52, k2_xboole_0(k1_xboole_0, C_53))=k4_xboole_0(A_52, C_53))), inference(superposition, [status(thm), theory('equality')], [c_14, c_358])).
% 12.75/6.03  tff(c_672, plain, (![C_53, A_7]: (k4_xboole_0(k1_xboole_0, k2_xboole_0(k1_xboole_0, C_53))=k3_xboole_0(A_7, k4_xboole_0(k1_xboole_0, C_53)))), inference(superposition, [status(thm), theory('equality')], [c_650, c_275])).
% 12.75/6.03  tff(c_729, plain, (![C_53]: (k4_xboole_0(k1_xboole_0, C_53)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_477, c_275, c_672])).
% 12.75/6.03  tff(c_24, plain, (r1_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_52])).
% 12.75/6.03  tff(c_41, plain, (![B_21, A_22]: (r1_xboole_0(B_21, A_22) | ~r1_xboole_0(A_22, B_21))), inference(cnfTransformation, [status(thm)], [f_35])).
% 12.75/6.03  tff(c_44, plain, (r1_xboole_0(k4_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_24, c_41])).
% 12.75/6.03  tff(c_82, plain, (![A_25, B_26]: (k3_xboole_0(A_25, B_26)=k1_xboole_0 | ~r1_xboole_0(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_31])).
% 12.75/6.03  tff(c_89, plain, (k3_xboole_0(k4_xboole_0('#skF_2', '#skF_3'), '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_44, c_82])).
% 12.75/6.03  tff(c_269, plain, (![C_40]: (k3_xboole_0(k4_xboole_0('#skF_2', '#skF_3'), k4_xboole_0('#skF_1', C_40))=k4_xboole_0(k1_xboole_0, C_40))), inference(superposition, [status(thm), theory('equality')], [c_89, c_231])).
% 12.75/6.03  tff(c_845, plain, (![C_40]: (k3_xboole_0(k4_xboole_0('#skF_2', '#skF_3'), k4_xboole_0('#skF_1', C_40))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_729, c_269])).
% 12.75/6.03  tff(c_4, plain, (![A_3, B_4]: (k3_xboole_0(A_3, B_4)=k1_xboole_0 | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 12.75/6.03  tff(c_1527, plain, (![B_70, A_71]: (k3_xboole_0(B_70, A_71)=k1_xboole_0 | k3_xboole_0(A_71, B_70)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_111, c_4])).
% 12.75/6.03  tff(c_1550, plain, (![C_40]: (k3_xboole_0(k4_xboole_0('#skF_1', C_40), k4_xboole_0('#skF_2', '#skF_3'))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_845, c_1527])).
% 12.75/6.03  tff(c_19631, plain, (k3_xboole_0(k4_xboole_0('#skF_1', '#skF_3'), '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_19624, c_1550])).
% 12.75/6.03  tff(c_20060, plain, $false, inference(negUnitSimplification, [status(thm)], [c_122, c_19631])).
% 12.75/6.03  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.75/6.03  
% 12.75/6.03  Inference rules
% 12.75/6.03  ----------------------
% 12.75/6.03  #Ref     : 0
% 12.75/6.03  #Sup     : 4959
% 12.75/6.03  #Fact    : 0
% 12.75/6.03  #Define  : 0
% 12.75/6.03  #Split   : 2
% 12.75/6.03  #Chain   : 0
% 12.75/6.03  #Close   : 0
% 12.75/6.03  
% 12.75/6.03  Ordering : KBO
% 12.75/6.03  
% 12.75/6.03  Simplification rules
% 12.75/6.03  ----------------------
% 12.75/6.03  #Subsume      : 59
% 12.75/6.03  #Demod        : 6246
% 12.75/6.03  #Tautology    : 3184
% 12.75/6.03  #SimpNegUnit  : 1
% 12.75/6.03  #BackRed      : 5
% 12.75/6.03  
% 12.75/6.03  #Partial instantiations: 0
% 12.75/6.03  #Strategies tried      : 1
% 12.75/6.03  
% 12.75/6.03  Timing (in seconds)
% 12.75/6.03  ----------------------
% 12.87/6.03  Preprocessing        : 0.45
% 12.87/6.03  Parsing              : 0.24
% 12.87/6.03  CNF conversion       : 0.03
% 12.87/6.03  Main loop            : 4.63
% 12.87/6.03  Inferencing          : 0.95
% 12.87/6.03  Reduction            : 2.76
% 12.87/6.03  Demodulation         : 2.47
% 12.87/6.03  BG Simplification    : 0.11
% 12.87/6.03  Subsumption          : 0.62
% 12.87/6.03  Abstraction          : 0.21
% 12.87/6.03  MUC search           : 0.00
% 12.87/6.03  Cooper               : 0.00
% 12.87/6.03  Total                : 5.13
% 12.87/6.04  Index Insertion      : 0.00
% 12.87/6.04  Index Deletion       : 0.00
% 12.87/6.04  Index Matching       : 0.00
% 12.87/6.04  BG Taut test         : 0.00
%------------------------------------------------------------------------------
