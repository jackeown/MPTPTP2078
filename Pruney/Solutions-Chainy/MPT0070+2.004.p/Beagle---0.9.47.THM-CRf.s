%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:18 EST 2020

% Result     : Theorem 2.71s
% Output     : CNFRefutation 3.06s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 106 expanded)
%              Number of leaves         :   23 (  44 expanded)
%              Depth                    :   13
%              Number of atoms          :   64 ( 118 expanded)
%              Number of equality atoms :   39 (  69 expanded)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_60,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r1_tarski(A,B)
          & r1_xboole_0(B,C) )
       => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_53,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_45,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_49,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_51,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

tff(c_244,plain,(
    ! [A_37,B_38] :
      ( r1_xboole_0(A_37,B_38)
      | k3_xboole_0(A_37,B_38) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_26,plain,(
    ~ r1_xboole_0('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_255,plain,(
    k3_xboole_0('#skF_1','#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_244,c_26])).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_334,plain,(
    ! [A_44,B_45] : k4_xboole_0(A_44,k4_xboole_0(A_44,B_45)) = k3_xboole_0(A_44,B_45) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_18,plain,(
    ! [A_14,B_15] : r1_tarski(k4_xboole_0(A_14,B_15),A_14) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_256,plain,(
    ! [A_39,B_40] :
      ( k2_xboole_0(A_39,B_40) = B_40
      | ~ r1_tarski(A_39,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_274,plain,(
    ! [A_41,B_42] : k2_xboole_0(k4_xboole_0(A_41,B_42),A_41) = A_41 ),
    inference(resolution,[status(thm)],[c_18,c_256])).

tff(c_16,plain,(
    ! [A_13] : k2_xboole_0(A_13,k1_xboole_0) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_287,plain,(
    ! [B_42] : k4_xboole_0(k1_xboole_0,B_42) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_274,c_16])).

tff(c_371,plain,(
    ! [B_46] : k3_xboole_0(k1_xboole_0,B_46) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_334,c_287])).

tff(c_385,plain,(
    ! [B_4] : k3_xboole_0(B_4,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_371])).

tff(c_20,plain,(
    ! [A_16] : k4_xboole_0(A_16,k1_xboole_0) = A_16 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_366,plain,(
    ! [A_16] : k4_xboole_0(A_16,A_16) = k3_xboole_0(A_16,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_334])).

tff(c_559,plain,(
    ! [A_16] : k4_xboole_0(A_16,A_16) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_385,c_366])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_283,plain,(
    ! [A_41,B_42] : k2_xboole_0(A_41,k4_xboole_0(A_41,B_42)) = A_41 ),
    inference(superposition,[status(thm),theory(equality)],[c_274,c_2])).

tff(c_28,plain,(
    r1_xboole_0('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_203,plain,(
    ! [B_33,A_34] :
      ( r1_xboole_0(B_33,A_34)
      | ~ r1_xboole_0(A_34,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_206,plain,(
    r1_xboole_0('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_203])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( k3_xboole_0(A_5,B_6) = k1_xboole_0
      | ~ r1_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_217,plain,(
    k3_xboole_0('#skF_3','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_206,c_6])).

tff(c_24,plain,(
    ! [A_20,B_21] : k4_xboole_0(A_20,k4_xboole_0(A_20,B_21)) = k3_xboole_0(A_20,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1241,plain,(
    ! [A_76,B_77] : k4_xboole_0(A_76,k3_xboole_0(A_76,B_77)) = k3_xboole_0(A_76,k4_xboole_0(A_76,B_77)) ),
    inference(superposition,[status(thm),theory(equality)],[c_334,c_24])).

tff(c_1296,plain,(
    k3_xboole_0('#skF_3',k4_xboole_0('#skF_3','#skF_2')) = k4_xboole_0('#skF_3',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_217,c_1241])).

tff(c_1319,plain,(
    k3_xboole_0('#skF_3',k4_xboole_0('#skF_3','#skF_2')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_1296])).

tff(c_487,plain,(
    ! [A_51,B_52] : r1_tarski(k3_xboole_0(A_51,B_52),A_51) ),
    inference(superposition,[status(thm),theory(equality)],[c_334,c_18])).

tff(c_529,plain,(
    ! [A_54,B_55] : r1_tarski(k3_xboole_0(A_54,B_55),B_55) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_487])).

tff(c_14,plain,(
    ! [A_11,B_12] :
      ( k2_xboole_0(A_11,B_12) = B_12
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_551,plain,(
    ! [A_54,B_55] : k2_xboole_0(k3_xboole_0(A_54,B_55),B_55) = B_55 ),
    inference(resolution,[status(thm)],[c_529,c_14])).

tff(c_1436,plain,(
    k2_xboole_0('#skF_3',k4_xboole_0('#skF_3','#skF_2')) = k4_xboole_0('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1319,c_551])).

tff(c_1451,plain,(
    k4_xboole_0('#skF_3','#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_283,c_1436])).

tff(c_30,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_269,plain,(
    k2_xboole_0('#skF_1','#skF_2') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_30,c_256])).

tff(c_427,plain,(
    ! [A_48,B_49,C_50] : k4_xboole_0(k4_xboole_0(A_48,B_49),C_50) = k4_xboole_0(A_48,k2_xboole_0(B_49,C_50)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_940,plain,(
    ! [A_70,B_71,C_72] : r1_tarski(k4_xboole_0(A_70,k2_xboole_0(B_71,C_72)),k4_xboole_0(A_70,B_71)) ),
    inference(superposition,[status(thm),theory(equality)],[c_427,c_18])).

tff(c_988,plain,(
    ! [A_70] : r1_tarski(k4_xboole_0(A_70,'#skF_2'),k4_xboole_0(A_70,'#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_269,c_940])).

tff(c_1460,plain,(
    r1_tarski('#skF_3',k4_xboole_0('#skF_3','#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1451,c_988])).

tff(c_1492,plain,(
    k2_xboole_0('#skF_3',k4_xboole_0('#skF_3','#skF_1')) = k4_xboole_0('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_1460,c_14])).

tff(c_1494,plain,(
    k4_xboole_0('#skF_3','#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_283,c_1492])).

tff(c_1512,plain,(
    k4_xboole_0('#skF_3','#skF_3') = k3_xboole_0('#skF_3','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1494,c_24])).

tff(c_1524,plain,(
    k3_xboole_0('#skF_1','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_559,c_4,c_1512])).

tff(c_1526,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_255,c_1524])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n005.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:24:47 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.71/1.45  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.71/1.45  
% 2.71/1.45  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.71/1.46  %$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.71/1.46  
% 2.71/1.46  %Foreground sorts:
% 2.71/1.46  
% 2.71/1.46  
% 2.71/1.46  %Background operators:
% 2.71/1.46  
% 2.71/1.46  
% 2.71/1.46  %Foreground operators:
% 2.71/1.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.71/1.46  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.71/1.46  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.71/1.46  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.71/1.46  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.71/1.46  tff('#skF_2', type, '#skF_2': $i).
% 2.71/1.46  tff('#skF_3', type, '#skF_3': $i).
% 2.71/1.46  tff('#skF_1', type, '#skF_1': $i).
% 2.71/1.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.71/1.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.71/1.46  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.71/1.46  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.71/1.46  
% 3.06/1.47  tff(f_33, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 3.06/1.47  tff(f_60, negated_conjecture, ~(![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_xboole_1)).
% 3.06/1.47  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.06/1.47  tff(f_53, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.06/1.47  tff(f_47, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 3.06/1.47  tff(f_43, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 3.06/1.47  tff(f_45, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 3.06/1.47  tff(f_49, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 3.06/1.47  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 3.06/1.47  tff(f_39, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 3.06/1.47  tff(f_51, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 3.06/1.47  tff(c_244, plain, (![A_37, B_38]: (r1_xboole_0(A_37, B_38) | k3_xboole_0(A_37, B_38)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.06/1.47  tff(c_26, plain, (~r1_xboole_0('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.06/1.47  tff(c_255, plain, (k3_xboole_0('#skF_1', '#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_244, c_26])).
% 3.06/1.47  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(B_4, A_3)=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.06/1.47  tff(c_334, plain, (![A_44, B_45]: (k4_xboole_0(A_44, k4_xboole_0(A_44, B_45))=k3_xboole_0(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.06/1.47  tff(c_18, plain, (![A_14, B_15]: (r1_tarski(k4_xboole_0(A_14, B_15), A_14))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.06/1.47  tff(c_256, plain, (![A_39, B_40]: (k2_xboole_0(A_39, B_40)=B_40 | ~r1_tarski(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.06/1.47  tff(c_274, plain, (![A_41, B_42]: (k2_xboole_0(k4_xboole_0(A_41, B_42), A_41)=A_41)), inference(resolution, [status(thm)], [c_18, c_256])).
% 3.06/1.47  tff(c_16, plain, (![A_13]: (k2_xboole_0(A_13, k1_xboole_0)=A_13)), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.06/1.47  tff(c_287, plain, (![B_42]: (k4_xboole_0(k1_xboole_0, B_42)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_274, c_16])).
% 3.06/1.47  tff(c_371, plain, (![B_46]: (k3_xboole_0(k1_xboole_0, B_46)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_334, c_287])).
% 3.06/1.47  tff(c_385, plain, (![B_4]: (k3_xboole_0(B_4, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_4, c_371])).
% 3.06/1.47  tff(c_20, plain, (![A_16]: (k4_xboole_0(A_16, k1_xboole_0)=A_16)), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.06/1.47  tff(c_366, plain, (![A_16]: (k4_xboole_0(A_16, A_16)=k3_xboole_0(A_16, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_20, c_334])).
% 3.06/1.47  tff(c_559, plain, (![A_16]: (k4_xboole_0(A_16, A_16)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_385, c_366])).
% 3.06/1.47  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.06/1.47  tff(c_283, plain, (![A_41, B_42]: (k2_xboole_0(A_41, k4_xboole_0(A_41, B_42))=A_41)), inference(superposition, [status(thm), theory('equality')], [c_274, c_2])).
% 3.06/1.47  tff(c_28, plain, (r1_xboole_0('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.06/1.47  tff(c_203, plain, (![B_33, A_34]: (r1_xboole_0(B_33, A_34) | ~r1_xboole_0(A_34, B_33))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.06/1.47  tff(c_206, plain, (r1_xboole_0('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_28, c_203])).
% 3.06/1.47  tff(c_6, plain, (![A_5, B_6]: (k3_xboole_0(A_5, B_6)=k1_xboole_0 | ~r1_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.06/1.47  tff(c_217, plain, (k3_xboole_0('#skF_3', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_206, c_6])).
% 3.06/1.47  tff(c_24, plain, (![A_20, B_21]: (k4_xboole_0(A_20, k4_xboole_0(A_20, B_21))=k3_xboole_0(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.06/1.47  tff(c_1241, plain, (![A_76, B_77]: (k4_xboole_0(A_76, k3_xboole_0(A_76, B_77))=k3_xboole_0(A_76, k4_xboole_0(A_76, B_77)))), inference(superposition, [status(thm), theory('equality')], [c_334, c_24])).
% 3.06/1.47  tff(c_1296, plain, (k3_xboole_0('#skF_3', k4_xboole_0('#skF_3', '#skF_2'))=k4_xboole_0('#skF_3', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_217, c_1241])).
% 3.06/1.47  tff(c_1319, plain, (k3_xboole_0('#skF_3', k4_xboole_0('#skF_3', '#skF_2'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_20, c_1296])).
% 3.06/1.47  tff(c_487, plain, (![A_51, B_52]: (r1_tarski(k3_xboole_0(A_51, B_52), A_51))), inference(superposition, [status(thm), theory('equality')], [c_334, c_18])).
% 3.06/1.47  tff(c_529, plain, (![A_54, B_55]: (r1_tarski(k3_xboole_0(A_54, B_55), B_55))), inference(superposition, [status(thm), theory('equality')], [c_4, c_487])).
% 3.06/1.47  tff(c_14, plain, (![A_11, B_12]: (k2_xboole_0(A_11, B_12)=B_12 | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.06/1.47  tff(c_551, plain, (![A_54, B_55]: (k2_xboole_0(k3_xboole_0(A_54, B_55), B_55)=B_55)), inference(resolution, [status(thm)], [c_529, c_14])).
% 3.06/1.47  tff(c_1436, plain, (k2_xboole_0('#skF_3', k4_xboole_0('#skF_3', '#skF_2'))=k4_xboole_0('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1319, c_551])).
% 3.06/1.47  tff(c_1451, plain, (k4_xboole_0('#skF_3', '#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_283, c_1436])).
% 3.06/1.47  tff(c_30, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.06/1.47  tff(c_269, plain, (k2_xboole_0('#skF_1', '#skF_2')='#skF_2'), inference(resolution, [status(thm)], [c_30, c_256])).
% 3.06/1.47  tff(c_427, plain, (![A_48, B_49, C_50]: (k4_xboole_0(k4_xboole_0(A_48, B_49), C_50)=k4_xboole_0(A_48, k2_xboole_0(B_49, C_50)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.06/1.47  tff(c_940, plain, (![A_70, B_71, C_72]: (r1_tarski(k4_xboole_0(A_70, k2_xboole_0(B_71, C_72)), k4_xboole_0(A_70, B_71)))), inference(superposition, [status(thm), theory('equality')], [c_427, c_18])).
% 3.06/1.47  tff(c_988, plain, (![A_70]: (r1_tarski(k4_xboole_0(A_70, '#skF_2'), k4_xboole_0(A_70, '#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_269, c_940])).
% 3.06/1.47  tff(c_1460, plain, (r1_tarski('#skF_3', k4_xboole_0('#skF_3', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_1451, c_988])).
% 3.06/1.47  tff(c_1492, plain, (k2_xboole_0('#skF_3', k4_xboole_0('#skF_3', '#skF_1'))=k4_xboole_0('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_1460, c_14])).
% 3.06/1.47  tff(c_1494, plain, (k4_xboole_0('#skF_3', '#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_283, c_1492])).
% 3.06/1.47  tff(c_1512, plain, (k4_xboole_0('#skF_3', '#skF_3')=k3_xboole_0('#skF_3', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1494, c_24])).
% 3.06/1.47  tff(c_1524, plain, (k3_xboole_0('#skF_1', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_559, c_4, c_1512])).
% 3.06/1.47  tff(c_1526, plain, $false, inference(negUnitSimplification, [status(thm)], [c_255, c_1524])).
% 3.06/1.47  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.06/1.47  
% 3.06/1.47  Inference rules
% 3.06/1.47  ----------------------
% 3.06/1.47  #Ref     : 0
% 3.06/1.47  #Sup     : 370
% 3.06/1.47  #Fact    : 0
% 3.06/1.47  #Define  : 0
% 3.06/1.47  #Split   : 0
% 3.06/1.47  #Chain   : 0
% 3.06/1.47  #Close   : 0
% 3.06/1.47  
% 3.06/1.47  Ordering : KBO
% 3.06/1.47  
% 3.06/1.47  Simplification rules
% 3.06/1.47  ----------------------
% 3.06/1.47  #Subsume      : 2
% 3.06/1.47  #Demod        : 248
% 3.06/1.47  #Tautology    : 282
% 3.06/1.47  #SimpNegUnit  : 1
% 3.06/1.47  #BackRed      : 4
% 3.06/1.47  
% 3.06/1.47  #Partial instantiations: 0
% 3.06/1.47  #Strategies tried      : 1
% 3.06/1.47  
% 3.06/1.47  Timing (in seconds)
% 3.06/1.47  ----------------------
% 3.06/1.47  Preprocessing        : 0.28
% 3.06/1.47  Parsing              : 0.15
% 3.06/1.47  CNF conversion       : 0.02
% 3.06/1.47  Main loop            : 0.43
% 3.06/1.47  Inferencing          : 0.16
% 3.06/1.47  Reduction            : 0.17
% 3.06/1.47  Demodulation         : 0.13
% 3.06/1.47  BG Simplification    : 0.02
% 3.06/1.47  Subsumption          : 0.06
% 3.06/1.47  Abstraction          : 0.02
% 3.06/1.47  MUC search           : 0.00
% 3.06/1.47  Cooper               : 0.00
% 3.06/1.48  Total                : 0.74
% 3.06/1.48  Index Insertion      : 0.00
% 3.06/1.48  Index Deletion       : 0.00
% 3.06/1.48  Index Matching       : 0.00
% 3.06/1.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
