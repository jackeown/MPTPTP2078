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
% DateTime   : Thu Dec  3 09:44:22 EST 2020

% Result     : Theorem 11.92s
% Output     : CNFRefutation 12.04s
% Verified   : 
% Statistics : Number of formulae       :   60 (  89 expanded)
%              Number of leaves         :   21 (  38 expanded)
%              Depth                    :    8
%              Number of atoms          :   58 ( 100 expanded)
%              Number of equality atoms :   36 (  60 expanded)
%              Maximal formula depth    :    6 (   3 average)
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

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_56,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_xboole_0(A,k4_xboole_0(B,C))
       => r1_xboole_0(B,k4_xboole_0(A,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_xboole_1)).

tff(f_45,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_43,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_51,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

tff(c_130,plain,(
    ! [A_40,B_41] :
      ( r1_xboole_0(A_40,B_41)
      | k3_xboole_0(A_40,B_41) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6,plain,(
    ! [B_4,A_3] :
      ( r1_xboole_0(B_4,A_3)
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_210,plain,(
    ! [B_48,A_49] :
      ( r1_xboole_0(B_48,A_49)
      | k3_xboole_0(A_49,B_48) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_130,c_6])).

tff(c_24,plain,(
    ~ r1_xboole_0('#skF_2',k4_xboole_0('#skF_1','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_221,plain,(
    k3_xboole_0(k4_xboole_0('#skF_1','#skF_3'),'#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_210,c_24])).

tff(c_16,plain,(
    ! [A_12,B_13,C_14] : k4_xboole_0(k4_xboole_0(A_12,B_13),C_14) = k4_xboole_0(A_12,k2_xboole_0(B_13,C_14)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_708,plain,(
    ! [A_67,B_68,C_69] : k4_xboole_0(k4_xboole_0(A_67,B_68),C_69) = k4_xboole_0(A_67,k2_xboole_0(B_68,C_69)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_18,plain,(
    ! [A_15,B_16] : k4_xboole_0(A_15,k4_xboole_0(A_15,B_16)) = k3_xboole_0(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_725,plain,(
    ! [A_67,B_68,B_16] : k4_xboole_0(A_67,k2_xboole_0(B_68,k4_xboole_0(k4_xboole_0(A_67,B_68),B_16))) = k3_xboole_0(k4_xboole_0(A_67,B_68),B_16) ),
    inference(superposition,[status(thm),theory(equality)],[c_708,c_18])).

tff(c_790,plain,(
    ! [A_67,B_68,B_16] : k4_xboole_0(A_67,k2_xboole_0(B_68,k4_xboole_0(A_67,k2_xboole_0(B_68,B_16)))) = k3_xboole_0(k4_xboole_0(A_67,B_68),B_16) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_725])).

tff(c_12,plain,(
    ! [A_9,B_10] : k2_xboole_0(A_9,k4_xboole_0(B_10,A_9)) = k2_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_6435,plain,(
    ! [A_180,B_181,B_182] : k4_xboole_0(A_180,k2_xboole_0(B_181,k4_xboole_0(A_180,k2_xboole_0(B_181,B_182)))) = k3_xboole_0(k4_xboole_0(A_180,B_181),B_182) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_725])).

tff(c_6700,plain,(
    ! [A_180,A_9,B_10] : k4_xboole_0(A_180,k2_xboole_0(A_9,k4_xboole_0(A_180,k2_xboole_0(A_9,B_10)))) = k3_xboole_0(k4_xboole_0(A_180,A_9),k4_xboole_0(B_10,A_9)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_6435])).

tff(c_52534,plain,(
    ! [A_544,A_545,B_546] : k3_xboole_0(k4_xboole_0(A_544,A_545),k4_xboole_0(B_546,A_545)) = k3_xboole_0(k4_xboole_0(A_544,A_545),B_546) ),
    inference(demodulation,[status(thm),theory(equality)],[c_790,c_6700])).

tff(c_14,plain,(
    ! [A_11] : k4_xboole_0(A_11,k1_xboole_0) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_41,plain,(
    ! [A_25,B_26] : r1_xboole_0(k4_xboole_0(A_25,B_26),B_26) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_44,plain,(
    ! [A_11] : r1_xboole_0(A_11,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_41])).

tff(c_105,plain,(
    ! [A_38,B_39] :
      ( k3_xboole_0(A_38,B_39) = k1_xboole_0
      | ~ r1_xboole_0(A_38,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_127,plain,(
    ! [A_11] : k3_xboole_0(A_11,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_44,c_105])).

tff(c_222,plain,(
    ! [A_50,B_51] : k2_xboole_0(k3_xboole_0(A_50,B_51),k4_xboole_0(A_50,B_51)) = A_50 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_249,plain,(
    ! [A_11] : k2_xboole_0(k3_xboole_0(A_11,k1_xboole_0),A_11) = A_11 ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_222])).

tff(c_253,plain,(
    ! [A_11] : k2_xboole_0(k1_xboole_0,A_11) = A_11 ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_249])).

tff(c_26,plain,(
    r1_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_46,plain,(
    ! [B_28,A_29] :
      ( r1_xboole_0(B_28,A_29)
      | ~ r1_xboole_0(A_29,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_55,plain,(
    r1_xboole_0(k4_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_46])).

tff(c_125,plain,(
    k3_xboole_0(k4_xboole_0('#skF_2','#skF_3'),'#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_55,c_105])).

tff(c_231,plain,(
    k2_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0('#skF_2','#skF_3'),'#skF_1')) = k4_xboole_0('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_125,c_222])).

tff(c_583,plain,(
    k4_xboole_0(k4_xboole_0('#skF_2','#skF_3'),'#skF_1') = k4_xboole_0('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_253,c_231])).

tff(c_20,plain,(
    ! [A_17,B_18] : k2_xboole_0(k3_xboole_0(A_17,B_18),k4_xboole_0(A_17,B_18)) = A_17 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_22,plain,(
    ! [A_19,B_20] : r1_xboole_0(k4_xboole_0(A_19,B_20),B_20) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1279,plain,(
    ! [A_80,B_81,C_82] : r1_xboole_0(k4_xboole_0(A_80,k2_xboole_0(B_81,C_82)),C_82) ),
    inference(superposition,[status(thm),theory(equality)],[c_708,c_22])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_1328,plain,(
    ! [A_80,B_81,C_82] : k3_xboole_0(k4_xboole_0(A_80,k2_xboole_0(B_81,C_82)),C_82) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1279,c_2])).

tff(c_3533,plain,(
    ! [B_131,A_132] :
      ( k3_xboole_0(B_131,A_132) = k1_xboole_0
      | k3_xboole_0(A_132,B_131) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_210,c_2])).

tff(c_7065,plain,(
    ! [C_189,A_190,B_191] : k3_xboole_0(C_189,k4_xboole_0(A_190,k2_xboole_0(B_191,C_189))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1328,c_3533])).

tff(c_7778,plain,(
    ! [A_196,B_197,A_198] : k3_xboole_0(k4_xboole_0(A_196,B_197),k4_xboole_0(A_198,A_196)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_7065])).

tff(c_7951,plain,(
    ! [B_197] : k3_xboole_0(k4_xboole_0('#skF_1',B_197),k4_xboole_0('#skF_2','#skF_3')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_583,c_7778])).

tff(c_52795,plain,(
    k3_xboole_0(k4_xboole_0('#skF_1','#skF_3'),'#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_52534,c_7951])).

tff(c_53273,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_221,c_52795])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:54:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.92/6.10  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.04/6.10  
% 12.04/6.10  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.04/6.11  %$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 12.04/6.11  
% 12.04/6.11  %Foreground sorts:
% 12.04/6.11  
% 12.04/6.11  
% 12.04/6.11  %Background operators:
% 12.04/6.11  
% 12.04/6.11  
% 12.04/6.11  %Foreground operators:
% 12.04/6.11  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 12.04/6.11  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 12.04/6.11  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 12.04/6.11  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 12.04/6.11  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 12.04/6.11  tff('#skF_2', type, '#skF_2': $i).
% 12.04/6.11  tff('#skF_3', type, '#skF_3': $i).
% 12.04/6.11  tff('#skF_1', type, '#skF_1': $i).
% 12.04/6.11  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 12.04/6.11  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 12.04/6.11  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 12.04/6.11  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 12.04/6.11  
% 12.04/6.12  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 12.04/6.12  tff(f_33, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 12.04/6.12  tff(f_56, negated_conjecture, ~(![A, B, C]: (r1_xboole_0(A, k4_xboole_0(B, C)) => r1_xboole_0(B, k4_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_xboole_1)).
% 12.04/6.12  tff(f_45, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 12.04/6.12  tff(f_47, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 12.04/6.12  tff(f_41, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 12.04/6.12  tff(f_43, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 12.04/6.12  tff(f_51, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 12.04/6.12  tff(f_49, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_xboole_1)).
% 12.04/6.12  tff(c_130, plain, (![A_40, B_41]: (r1_xboole_0(A_40, B_41) | k3_xboole_0(A_40, B_41)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 12.04/6.12  tff(c_6, plain, (![B_4, A_3]: (r1_xboole_0(B_4, A_3) | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 12.04/6.12  tff(c_210, plain, (![B_48, A_49]: (r1_xboole_0(B_48, A_49) | k3_xboole_0(A_49, B_48)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_130, c_6])).
% 12.04/6.12  tff(c_24, plain, (~r1_xboole_0('#skF_2', k4_xboole_0('#skF_1', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_56])).
% 12.04/6.12  tff(c_221, plain, (k3_xboole_0(k4_xboole_0('#skF_1', '#skF_3'), '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_210, c_24])).
% 12.04/6.12  tff(c_16, plain, (![A_12, B_13, C_14]: (k4_xboole_0(k4_xboole_0(A_12, B_13), C_14)=k4_xboole_0(A_12, k2_xboole_0(B_13, C_14)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 12.04/6.12  tff(c_708, plain, (![A_67, B_68, C_69]: (k4_xboole_0(k4_xboole_0(A_67, B_68), C_69)=k4_xboole_0(A_67, k2_xboole_0(B_68, C_69)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 12.04/6.12  tff(c_18, plain, (![A_15, B_16]: (k4_xboole_0(A_15, k4_xboole_0(A_15, B_16))=k3_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_47])).
% 12.04/6.12  tff(c_725, plain, (![A_67, B_68, B_16]: (k4_xboole_0(A_67, k2_xboole_0(B_68, k4_xboole_0(k4_xboole_0(A_67, B_68), B_16)))=k3_xboole_0(k4_xboole_0(A_67, B_68), B_16))), inference(superposition, [status(thm), theory('equality')], [c_708, c_18])).
% 12.04/6.12  tff(c_790, plain, (![A_67, B_68, B_16]: (k4_xboole_0(A_67, k2_xboole_0(B_68, k4_xboole_0(A_67, k2_xboole_0(B_68, B_16))))=k3_xboole_0(k4_xboole_0(A_67, B_68), B_16))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_725])).
% 12.04/6.12  tff(c_12, plain, (![A_9, B_10]: (k2_xboole_0(A_9, k4_xboole_0(B_10, A_9))=k2_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_41])).
% 12.04/6.12  tff(c_6435, plain, (![A_180, B_181, B_182]: (k4_xboole_0(A_180, k2_xboole_0(B_181, k4_xboole_0(A_180, k2_xboole_0(B_181, B_182))))=k3_xboole_0(k4_xboole_0(A_180, B_181), B_182))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_725])).
% 12.04/6.12  tff(c_6700, plain, (![A_180, A_9, B_10]: (k4_xboole_0(A_180, k2_xboole_0(A_9, k4_xboole_0(A_180, k2_xboole_0(A_9, B_10))))=k3_xboole_0(k4_xboole_0(A_180, A_9), k4_xboole_0(B_10, A_9)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_6435])).
% 12.04/6.12  tff(c_52534, plain, (![A_544, A_545, B_546]: (k3_xboole_0(k4_xboole_0(A_544, A_545), k4_xboole_0(B_546, A_545))=k3_xboole_0(k4_xboole_0(A_544, A_545), B_546))), inference(demodulation, [status(thm), theory('equality')], [c_790, c_6700])).
% 12.04/6.12  tff(c_14, plain, (![A_11]: (k4_xboole_0(A_11, k1_xboole_0)=A_11)), inference(cnfTransformation, [status(thm)], [f_43])).
% 12.04/6.12  tff(c_41, plain, (![A_25, B_26]: (r1_xboole_0(k4_xboole_0(A_25, B_26), B_26))), inference(cnfTransformation, [status(thm)], [f_51])).
% 12.04/6.12  tff(c_44, plain, (![A_11]: (r1_xboole_0(A_11, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_14, c_41])).
% 12.04/6.12  tff(c_105, plain, (![A_38, B_39]: (k3_xboole_0(A_38, B_39)=k1_xboole_0 | ~r1_xboole_0(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_29])).
% 12.04/6.12  tff(c_127, plain, (![A_11]: (k3_xboole_0(A_11, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_44, c_105])).
% 12.04/6.12  tff(c_222, plain, (![A_50, B_51]: (k2_xboole_0(k3_xboole_0(A_50, B_51), k4_xboole_0(A_50, B_51))=A_50)), inference(cnfTransformation, [status(thm)], [f_49])).
% 12.04/6.12  tff(c_249, plain, (![A_11]: (k2_xboole_0(k3_xboole_0(A_11, k1_xboole_0), A_11)=A_11)), inference(superposition, [status(thm), theory('equality')], [c_14, c_222])).
% 12.04/6.12  tff(c_253, plain, (![A_11]: (k2_xboole_0(k1_xboole_0, A_11)=A_11)), inference(demodulation, [status(thm), theory('equality')], [c_127, c_249])).
% 12.04/6.12  tff(c_26, plain, (r1_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_56])).
% 12.04/6.12  tff(c_46, plain, (![B_28, A_29]: (r1_xboole_0(B_28, A_29) | ~r1_xboole_0(A_29, B_28))), inference(cnfTransformation, [status(thm)], [f_33])).
% 12.04/6.12  tff(c_55, plain, (r1_xboole_0(k4_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_26, c_46])).
% 12.04/6.12  tff(c_125, plain, (k3_xboole_0(k4_xboole_0('#skF_2', '#skF_3'), '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_55, c_105])).
% 12.04/6.12  tff(c_231, plain, (k2_xboole_0(k1_xboole_0, k4_xboole_0(k4_xboole_0('#skF_2', '#skF_3'), '#skF_1'))=k4_xboole_0('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_125, c_222])).
% 12.04/6.12  tff(c_583, plain, (k4_xboole_0(k4_xboole_0('#skF_2', '#skF_3'), '#skF_1')=k4_xboole_0('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_253, c_231])).
% 12.04/6.12  tff(c_20, plain, (![A_17, B_18]: (k2_xboole_0(k3_xboole_0(A_17, B_18), k4_xboole_0(A_17, B_18))=A_17)), inference(cnfTransformation, [status(thm)], [f_49])).
% 12.04/6.12  tff(c_22, plain, (![A_19, B_20]: (r1_xboole_0(k4_xboole_0(A_19, B_20), B_20))), inference(cnfTransformation, [status(thm)], [f_51])).
% 12.04/6.12  tff(c_1279, plain, (![A_80, B_81, C_82]: (r1_xboole_0(k4_xboole_0(A_80, k2_xboole_0(B_81, C_82)), C_82))), inference(superposition, [status(thm), theory('equality')], [c_708, c_22])).
% 12.04/6.12  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 12.04/6.12  tff(c_1328, plain, (![A_80, B_81, C_82]: (k3_xboole_0(k4_xboole_0(A_80, k2_xboole_0(B_81, C_82)), C_82)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1279, c_2])).
% 12.04/6.12  tff(c_3533, plain, (![B_131, A_132]: (k3_xboole_0(B_131, A_132)=k1_xboole_0 | k3_xboole_0(A_132, B_131)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_210, c_2])).
% 12.04/6.12  tff(c_7065, plain, (![C_189, A_190, B_191]: (k3_xboole_0(C_189, k4_xboole_0(A_190, k2_xboole_0(B_191, C_189)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1328, c_3533])).
% 12.04/6.12  tff(c_7778, plain, (![A_196, B_197, A_198]: (k3_xboole_0(k4_xboole_0(A_196, B_197), k4_xboole_0(A_198, A_196))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_20, c_7065])).
% 12.04/6.12  tff(c_7951, plain, (![B_197]: (k3_xboole_0(k4_xboole_0('#skF_1', B_197), k4_xboole_0('#skF_2', '#skF_3'))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_583, c_7778])).
% 12.04/6.12  tff(c_52795, plain, (k3_xboole_0(k4_xboole_0('#skF_1', '#skF_3'), '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_52534, c_7951])).
% 12.04/6.12  tff(c_53273, plain, $false, inference(negUnitSimplification, [status(thm)], [c_221, c_52795])).
% 12.04/6.12  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.04/6.12  
% 12.04/6.12  Inference rules
% 12.04/6.12  ----------------------
% 12.04/6.12  #Ref     : 0
% 12.04/6.12  #Sup     : 13404
% 12.04/6.12  #Fact    : 0
% 12.04/6.12  #Define  : 0
% 12.04/6.12  #Split   : 0
% 12.04/6.12  #Chain   : 0
% 12.04/6.12  #Close   : 0
% 12.04/6.12  
% 12.04/6.12  Ordering : KBO
% 12.04/6.12  
% 12.04/6.12  Simplification rules
% 12.04/6.12  ----------------------
% 12.04/6.12  #Subsume      : 8
% 12.04/6.12  #Demod        : 15405
% 12.04/6.12  #Tautology    : 10428
% 12.04/6.12  #SimpNegUnit  : 1
% 12.04/6.12  #BackRed      : 6
% 12.04/6.12  
% 12.04/6.12  #Partial instantiations: 0
% 12.04/6.12  #Strategies tried      : 1
% 12.04/6.12  
% 12.04/6.12  Timing (in seconds)
% 12.04/6.12  ----------------------
% 12.04/6.12  Preprocessing        : 0.27
% 12.04/6.12  Parsing              : 0.15
% 12.04/6.12  CNF conversion       : 0.02
% 12.04/6.12  Main loop            : 5.06
% 12.04/6.12  Inferencing          : 0.84
% 12.04/6.12  Reduction            : 2.92
% 12.04/6.12  Demodulation         : 2.58
% 12.04/6.12  BG Simplification    : 0.09
% 12.04/6.12  Subsumption          : 0.98
% 12.04/6.12  Abstraction          : 0.15
% 12.04/6.12  MUC search           : 0.00
% 12.04/6.12  Cooper               : 0.00
% 12.04/6.12  Total                : 5.36
% 12.04/6.12  Index Insertion      : 0.00
% 12.04/6.12  Index Deletion       : 0.00
% 12.04/6.12  Index Matching       : 0.00
% 12.04/6.12  BG Taut test         : 0.00
%------------------------------------------------------------------------------
