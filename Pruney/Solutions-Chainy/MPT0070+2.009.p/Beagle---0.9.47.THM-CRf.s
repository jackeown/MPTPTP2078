%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:19 EST 2020

% Result     : Theorem 2.99s
% Output     : CNFRefutation 3.15s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 147 expanded)
%              Number of leaves         :   24 (  58 expanded)
%              Depth                    :   17
%              Number of atoms          :   71 ( 163 expanded)
%              Number of equality atoms :   49 ( 110 expanded)
%              Maximal formula depth    :    7 (   3 average)
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

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_60,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r1_tarski(A,B)
          & r1_xboole_0(B,C) )
       => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_43,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_47,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_53,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_49,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

tff(c_261,plain,(
    ! [A_39,B_40] :
      ( r1_xboole_0(A_39,B_40)
      | k3_xboole_0(A_39,B_40) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_26,plain,(
    ~ r1_xboole_0('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_272,plain,(
    k3_xboole_0('#skF_1','#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_261,c_26])).

tff(c_333,plain,(
    ! [A_44,B_45] : k4_xboole_0(A_44,k4_xboole_0(A_44,B_45)) = k3_xboole_0(A_44,B_45) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_16,plain,(
    ! [A_12,B_13] : r1_tarski(k4_xboole_0(A_12,B_13),A_12) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_215,plain,(
    ! [A_36,B_37] :
      ( k2_xboole_0(A_36,B_37) = B_37
      | ~ r1_tarski(A_36,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_273,plain,(
    ! [A_41,B_42] : k2_xboole_0(k4_xboole_0(A_41,B_42),A_41) = A_41 ),
    inference(resolution,[status(thm)],[c_16,c_215])).

tff(c_14,plain,(
    ! [A_11] : k2_xboole_0(A_11,k1_xboole_0) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_286,plain,(
    ! [B_42] : k4_xboole_0(k1_xboole_0,B_42) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_273,c_14])).

tff(c_370,plain,(
    ! [B_46] : k3_xboole_0(k1_xboole_0,B_46) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_333,c_286])).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_378,plain,(
    ! [B_46] : k3_xboole_0(B_46,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_370,c_4])).

tff(c_18,plain,(
    ! [A_14] : k4_xboole_0(A_14,k1_xboole_0) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_365,plain,(
    ! [A_14] : k4_xboole_0(A_14,A_14) = k3_xboole_0(A_14,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_333])).

tff(c_750,plain,(
    ! [A_14] : k4_xboole_0(A_14,A_14) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_378,c_365])).

tff(c_28,plain,(
    r1_xboole_0('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_134,plain,(
    ! [B_31,A_32] :
      ( r1_xboole_0(B_31,A_32)
      | ~ r1_xboole_0(A_32,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_137,plain,(
    r1_xboole_0('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_134])).

tff(c_182,plain,(
    ! [A_34,B_35] :
      ( k3_xboole_0(A_34,B_35) = k1_xboole_0
      | ~ r1_xboole_0(A_34,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_189,plain,(
    k3_xboole_0('#skF_3','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_137,c_182])).

tff(c_426,plain,(
    ! [A_48,B_49] : k2_xboole_0(k3_xboole_0(A_48,B_49),k4_xboole_0(A_48,B_49)) = A_48 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_447,plain,(
    k2_xboole_0(k1_xboole_0,k4_xboole_0('#skF_3','#skF_2')) = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_189,c_426])).

tff(c_87,plain,(
    ! [B_29,A_30] : k2_xboole_0(B_29,A_30) = k2_xboole_0(A_30,B_29) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_125,plain,(
    ! [A_11] : k2_xboole_0(k1_xboole_0,A_11) = A_11 ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_87])).

tff(c_645,plain,(
    k4_xboole_0('#skF_3','#skF_2') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_447,c_125])).

tff(c_30,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_227,plain,(
    k2_xboole_0('#skF_1','#skF_2') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_30,c_215])).

tff(c_753,plain,(
    ! [A_58] : k4_xboole_0(A_58,A_58) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_378,c_365])).

tff(c_20,plain,(
    ! [A_15,B_16,C_17] : k4_xboole_0(k4_xboole_0(A_15,B_16),C_17) = k4_xboole_0(A_15,k2_xboole_0(B_16,C_17)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_758,plain,(
    ! [A_58,C_17] : k4_xboole_0(A_58,k2_xboole_0(A_58,C_17)) = k4_xboole_0(k1_xboole_0,C_17) ),
    inference(superposition,[status(thm),theory(equality)],[c_753,c_20])).

tff(c_1500,plain,(
    ! [A_78,C_79] : k4_xboole_0(A_78,k2_xboole_0(A_78,C_79)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_286,c_758])).

tff(c_1580,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_227,c_1500])).

tff(c_453,plain,(
    ! [B_4,A_3] : k2_xboole_0(k3_xboole_0(B_4,A_3),k4_xboole_0(A_3,B_4)) = A_3 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_426])).

tff(c_1616,plain,(
    k2_xboole_0(k3_xboole_0('#skF_2','#skF_1'),k1_xboole_0) = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_1580,c_453])).

tff(c_1637,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_4,c_1616])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_600,plain,(
    ! [A_53,B_54] : r1_tarski(k3_xboole_0(A_53,B_54),A_53) ),
    inference(superposition,[status(thm),theory(equality)],[c_333,c_16])).

tff(c_713,plain,(
    ! [B_56,A_57] : r1_tarski(k3_xboole_0(B_56,A_57),A_57) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_600])).

tff(c_12,plain,(
    ! [A_9,B_10] :
      ( k2_xboole_0(A_9,B_10) = B_10
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1076,plain,(
    ! [B_69,A_70] : k2_xboole_0(k3_xboole_0(B_69,A_70),A_70) = A_70 ),
    inference(resolution,[status(thm)],[c_713,c_12])).

tff(c_1119,plain,(
    ! [B_2,B_69] : k2_xboole_0(B_2,k3_xboole_0(B_69,B_2)) = B_2 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1076])).

tff(c_1647,plain,(
    k2_xboole_0('#skF_2','#skF_1') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_1637,c_1119])).

tff(c_657,plain,(
    ! [C_17] : k4_xboole_0('#skF_3',k2_xboole_0('#skF_2',C_17)) = k4_xboole_0('#skF_3',C_17) ),
    inference(superposition,[status(thm),theory(equality)],[c_645,c_20])).

tff(c_1686,plain,(
    k4_xboole_0('#skF_3','#skF_2') = k4_xboole_0('#skF_3','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1647,c_657])).

tff(c_1702,plain,(
    k4_xboole_0('#skF_3','#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_645,c_1686])).

tff(c_22,plain,(
    ! [A_18,B_19] : k4_xboole_0(A_18,k4_xboole_0(A_18,B_19)) = k3_xboole_0(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1725,plain,(
    k4_xboole_0('#skF_3','#skF_3') = k3_xboole_0('#skF_3','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1702,c_22])).

tff(c_1738,plain,(
    k3_xboole_0('#skF_1','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_750,c_4,c_1725])).

tff(c_1740,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_272,c_1738])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n025.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:52:05 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.99/1.47  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.99/1.47  
% 2.99/1.47  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.99/1.48  %$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.99/1.48  
% 2.99/1.48  %Foreground sorts:
% 2.99/1.48  
% 2.99/1.48  
% 2.99/1.48  %Background operators:
% 2.99/1.48  
% 2.99/1.48  
% 2.99/1.48  %Foreground operators:
% 2.99/1.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.99/1.48  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.99/1.48  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.99/1.48  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.99/1.48  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.99/1.48  tff('#skF_2', type, '#skF_2': $i).
% 2.99/1.48  tff('#skF_3', type, '#skF_3': $i).
% 2.99/1.48  tff('#skF_1', type, '#skF_1': $i).
% 2.99/1.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.99/1.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.99/1.48  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.99/1.48  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.99/1.48  
% 3.15/1.49  tff(f_33, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 3.15/1.49  tff(f_60, negated_conjecture, ~(![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_xboole_1)).
% 3.15/1.49  tff(f_51, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.15/1.49  tff(f_45, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 3.15/1.49  tff(f_41, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 3.15/1.49  tff(f_43, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 3.15/1.49  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.15/1.49  tff(f_47, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 3.15/1.49  tff(f_37, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 3.15/1.49  tff(f_53, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_xboole_1)).
% 3.15/1.49  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 3.15/1.49  tff(f_49, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 3.15/1.49  tff(c_261, plain, (![A_39, B_40]: (r1_xboole_0(A_39, B_40) | k3_xboole_0(A_39, B_40)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.15/1.49  tff(c_26, plain, (~r1_xboole_0('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.15/1.49  tff(c_272, plain, (k3_xboole_0('#skF_1', '#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_261, c_26])).
% 3.15/1.49  tff(c_333, plain, (![A_44, B_45]: (k4_xboole_0(A_44, k4_xboole_0(A_44, B_45))=k3_xboole_0(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.15/1.49  tff(c_16, plain, (![A_12, B_13]: (r1_tarski(k4_xboole_0(A_12, B_13), A_12))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.15/1.49  tff(c_215, plain, (![A_36, B_37]: (k2_xboole_0(A_36, B_37)=B_37 | ~r1_tarski(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.15/1.49  tff(c_273, plain, (![A_41, B_42]: (k2_xboole_0(k4_xboole_0(A_41, B_42), A_41)=A_41)), inference(resolution, [status(thm)], [c_16, c_215])).
% 3.15/1.49  tff(c_14, plain, (![A_11]: (k2_xboole_0(A_11, k1_xboole_0)=A_11)), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.15/1.49  tff(c_286, plain, (![B_42]: (k4_xboole_0(k1_xboole_0, B_42)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_273, c_14])).
% 3.15/1.49  tff(c_370, plain, (![B_46]: (k3_xboole_0(k1_xboole_0, B_46)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_333, c_286])).
% 3.15/1.49  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(B_4, A_3)=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.15/1.49  tff(c_378, plain, (![B_46]: (k3_xboole_0(B_46, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_370, c_4])).
% 3.15/1.49  tff(c_18, plain, (![A_14]: (k4_xboole_0(A_14, k1_xboole_0)=A_14)), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.15/1.49  tff(c_365, plain, (![A_14]: (k4_xboole_0(A_14, A_14)=k3_xboole_0(A_14, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_18, c_333])).
% 3.15/1.49  tff(c_750, plain, (![A_14]: (k4_xboole_0(A_14, A_14)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_378, c_365])).
% 3.15/1.49  tff(c_28, plain, (r1_xboole_0('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.15/1.49  tff(c_134, plain, (![B_31, A_32]: (r1_xboole_0(B_31, A_32) | ~r1_xboole_0(A_32, B_31))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.15/1.49  tff(c_137, plain, (r1_xboole_0('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_28, c_134])).
% 3.15/1.49  tff(c_182, plain, (![A_34, B_35]: (k3_xboole_0(A_34, B_35)=k1_xboole_0 | ~r1_xboole_0(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.15/1.49  tff(c_189, plain, (k3_xboole_0('#skF_3', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_137, c_182])).
% 3.15/1.49  tff(c_426, plain, (![A_48, B_49]: (k2_xboole_0(k3_xboole_0(A_48, B_49), k4_xboole_0(A_48, B_49))=A_48)), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.15/1.49  tff(c_447, plain, (k2_xboole_0(k1_xboole_0, k4_xboole_0('#skF_3', '#skF_2'))='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_189, c_426])).
% 3.15/1.49  tff(c_87, plain, (![B_29, A_30]: (k2_xboole_0(B_29, A_30)=k2_xboole_0(A_30, B_29))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.15/1.49  tff(c_125, plain, (![A_11]: (k2_xboole_0(k1_xboole_0, A_11)=A_11)), inference(superposition, [status(thm), theory('equality')], [c_14, c_87])).
% 3.15/1.49  tff(c_645, plain, (k4_xboole_0('#skF_3', '#skF_2')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_447, c_125])).
% 3.15/1.49  tff(c_30, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.15/1.49  tff(c_227, plain, (k2_xboole_0('#skF_1', '#skF_2')='#skF_2'), inference(resolution, [status(thm)], [c_30, c_215])).
% 3.15/1.49  tff(c_753, plain, (![A_58]: (k4_xboole_0(A_58, A_58)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_378, c_365])).
% 3.15/1.49  tff(c_20, plain, (![A_15, B_16, C_17]: (k4_xboole_0(k4_xboole_0(A_15, B_16), C_17)=k4_xboole_0(A_15, k2_xboole_0(B_16, C_17)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.15/1.49  tff(c_758, plain, (![A_58, C_17]: (k4_xboole_0(A_58, k2_xboole_0(A_58, C_17))=k4_xboole_0(k1_xboole_0, C_17))), inference(superposition, [status(thm), theory('equality')], [c_753, c_20])).
% 3.15/1.49  tff(c_1500, plain, (![A_78, C_79]: (k4_xboole_0(A_78, k2_xboole_0(A_78, C_79))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_286, c_758])).
% 3.15/1.49  tff(c_1580, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_227, c_1500])).
% 3.15/1.49  tff(c_453, plain, (![B_4, A_3]: (k2_xboole_0(k3_xboole_0(B_4, A_3), k4_xboole_0(A_3, B_4))=A_3)), inference(superposition, [status(thm), theory('equality')], [c_4, c_426])).
% 3.15/1.49  tff(c_1616, plain, (k2_xboole_0(k3_xboole_0('#skF_2', '#skF_1'), k1_xboole_0)='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_1580, c_453])).
% 3.15/1.49  tff(c_1637, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_14, c_4, c_1616])).
% 3.15/1.49  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.15/1.49  tff(c_600, plain, (![A_53, B_54]: (r1_tarski(k3_xboole_0(A_53, B_54), A_53))), inference(superposition, [status(thm), theory('equality')], [c_333, c_16])).
% 3.15/1.49  tff(c_713, plain, (![B_56, A_57]: (r1_tarski(k3_xboole_0(B_56, A_57), A_57))), inference(superposition, [status(thm), theory('equality')], [c_4, c_600])).
% 3.15/1.49  tff(c_12, plain, (![A_9, B_10]: (k2_xboole_0(A_9, B_10)=B_10 | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.15/1.49  tff(c_1076, plain, (![B_69, A_70]: (k2_xboole_0(k3_xboole_0(B_69, A_70), A_70)=A_70)), inference(resolution, [status(thm)], [c_713, c_12])).
% 3.15/1.49  tff(c_1119, plain, (![B_2, B_69]: (k2_xboole_0(B_2, k3_xboole_0(B_69, B_2))=B_2)), inference(superposition, [status(thm), theory('equality')], [c_2, c_1076])).
% 3.15/1.49  tff(c_1647, plain, (k2_xboole_0('#skF_2', '#skF_1')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_1637, c_1119])).
% 3.15/1.49  tff(c_657, plain, (![C_17]: (k4_xboole_0('#skF_3', k2_xboole_0('#skF_2', C_17))=k4_xboole_0('#skF_3', C_17))), inference(superposition, [status(thm), theory('equality')], [c_645, c_20])).
% 3.15/1.49  tff(c_1686, plain, (k4_xboole_0('#skF_3', '#skF_2')=k4_xboole_0('#skF_3', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1647, c_657])).
% 3.15/1.49  tff(c_1702, plain, (k4_xboole_0('#skF_3', '#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_645, c_1686])).
% 3.15/1.49  tff(c_22, plain, (![A_18, B_19]: (k4_xboole_0(A_18, k4_xboole_0(A_18, B_19))=k3_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.15/1.49  tff(c_1725, plain, (k4_xboole_0('#skF_3', '#skF_3')=k3_xboole_0('#skF_3', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1702, c_22])).
% 3.15/1.49  tff(c_1738, plain, (k3_xboole_0('#skF_1', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_750, c_4, c_1725])).
% 3.15/1.49  tff(c_1740, plain, $false, inference(negUnitSimplification, [status(thm)], [c_272, c_1738])).
% 3.15/1.49  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.15/1.49  
% 3.15/1.49  Inference rules
% 3.15/1.49  ----------------------
% 3.15/1.49  #Ref     : 0
% 3.15/1.49  #Sup     : 428
% 3.15/1.49  #Fact    : 0
% 3.15/1.49  #Define  : 0
% 3.15/1.49  #Split   : 0
% 3.15/1.49  #Chain   : 0
% 3.15/1.49  #Close   : 0
% 3.15/1.49  
% 3.15/1.49  Ordering : KBO
% 3.15/1.49  
% 3.15/1.49  Simplification rules
% 3.15/1.49  ----------------------
% 3.15/1.49  #Subsume      : 2
% 3.15/1.49  #Demod        : 298
% 3.15/1.49  #Tautology    : 322
% 3.15/1.49  #SimpNegUnit  : 1
% 3.15/1.49  #BackRed      : 2
% 3.15/1.49  
% 3.15/1.49  #Partial instantiations: 0
% 3.15/1.49  #Strategies tried      : 1
% 3.15/1.49  
% 3.15/1.49  Timing (in seconds)
% 3.15/1.49  ----------------------
% 3.15/1.49  Preprocessing        : 0.27
% 3.15/1.49  Parsing              : 0.15
% 3.15/1.50  CNF conversion       : 0.02
% 3.15/1.50  Main loop            : 0.45
% 3.15/1.50  Inferencing          : 0.15
% 3.15/1.50  Reduction            : 0.19
% 3.15/1.50  Demodulation         : 0.15
% 3.15/1.50  BG Simplification    : 0.02
% 3.15/1.50  Subsumption          : 0.06
% 3.15/1.50  Abstraction          : 0.02
% 3.15/1.50  MUC search           : 0.00
% 3.15/1.50  Cooper               : 0.00
% 3.15/1.50  Total                : 0.76
% 3.15/1.50  Index Insertion      : 0.00
% 3.15/1.50  Index Deletion       : 0.00
% 3.15/1.50  Index Matching       : 0.00
% 3.15/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
