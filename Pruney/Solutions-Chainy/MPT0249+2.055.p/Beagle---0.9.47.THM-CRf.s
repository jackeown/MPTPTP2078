%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:31 EST 2020

% Result     : Theorem 2.96s
% Output     : CNFRefutation 2.96s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 629 expanded)
%              Number of leaves         :   31 ( 243 expanded)
%              Depth                    :   17
%              Number of atoms          :   73 ( 675 expanded)
%              Number of equality atoms :   62 ( 648 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_76,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k1_tarski(A) = k2_xboole_0(B,C)
          & B != C
          & B != k1_xboole_0
          & C != k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_zfmisc_1)).

tff(f_39,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(c_40,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_14,plain,(
    ! [A_14] : k5_xboole_0(A_14,A_14) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_4,plain,(
    ! [A_3] : k3_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_2,plain,(
    ! [A_1] : k2_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_350,plain,(
    ! [A_80,B_81] : k5_xboole_0(k5_xboole_0(A_80,B_81),k2_xboole_0(A_80,B_81)) = k3_xboole_0(A_80,B_81) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_390,plain,(
    ! [A_1] : k5_xboole_0(k5_xboole_0(A_1,A_1),A_1) = k3_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_350])).

tff(c_396,plain,(
    ! [A_1] : k5_xboole_0(k1_xboole_0,A_1) = A_1 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_14,c_390])).

tff(c_12,plain,(
    ! [A_11,B_12,C_13] : k5_xboole_0(k5_xboole_0(A_11,B_12),C_13) = k5_xboole_0(A_11,k5_xboole_0(B_12,C_13)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_398,plain,(
    ! [A_82] : k5_xboole_0(k1_xboole_0,A_82) = A_82 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_14,c_390])).

tff(c_269,plain,(
    ! [A_75,B_76,C_77] : k5_xboole_0(k5_xboole_0(A_75,B_76),C_77) = k5_xboole_0(A_75,k5_xboole_0(B_76,C_77)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_283,plain,(
    ! [A_75,B_76] : k5_xboole_0(A_75,k5_xboole_0(B_76,k5_xboole_0(A_75,B_76))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_269,c_14])).

tff(c_451,plain,(
    ! [A_83] : k5_xboole_0(A_83,k5_xboole_0(A_83,k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_398,c_283])).

tff(c_470,plain,(
    ! [A_83,C_13] : k5_xboole_0(A_83,k5_xboole_0(k5_xboole_0(A_83,k1_xboole_0),C_13)) = k5_xboole_0(k1_xboole_0,C_13) ),
    inference(superposition,[status(thm),theory(equality)],[c_451,c_12])).

tff(c_549,plain,(
    ! [A_90,C_91] : k5_xboole_0(A_90,k5_xboole_0(A_90,C_91)) = C_91 ),
    inference(demodulation,[status(thm),theory(equality)],[c_396,c_396,c_12,c_470])).

tff(c_616,plain,(
    ! [A_14] : k5_xboole_0(A_14,k1_xboole_0) = A_14 ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_549])).

tff(c_599,plain,(
    ! [B_76,A_75] : k5_xboole_0(B_76,k5_xboole_0(A_75,B_76)) = k5_xboole_0(A_75,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_283,c_549])).

tff(c_818,plain,(
    ! [B_101,A_102] : k5_xboole_0(B_101,k5_xboole_0(A_102,B_101)) = A_102 ),
    inference(demodulation,[status(thm),theory(equality)],[c_616,c_599])).

tff(c_815,plain,(
    ! [B_76,A_75] : k5_xboole_0(B_76,k5_xboole_0(A_75,B_76)) = A_75 ),
    inference(demodulation,[status(thm),theory(equality)],[c_616,c_599])).

tff(c_821,plain,(
    ! [A_102,B_101] : k5_xboole_0(k5_xboole_0(A_102,B_101),A_102) = B_101 ),
    inference(superposition,[status(thm),theory(equality)],[c_818,c_815])).

tff(c_42,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_46,plain,(
    k2_xboole_0('#skF_2','#skF_3') = k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_87,plain,(
    ! [A_56,B_57] : r1_tarski(A_56,k2_xboole_0(A_56,B_57)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_90,plain,(
    r1_tarski('#skF_2',k1_tarski('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_87])).

tff(c_150,plain,(
    ! [B_67,A_68] :
      ( k1_tarski(B_67) = A_68
      | k1_xboole_0 = A_68
      | ~ r1_tarski(A_68,k1_tarski(B_67)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_153,plain,
    ( k1_tarski('#skF_1') = '#skF_2'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_90,c_150])).

tff(c_167,plain,(
    k1_tarski('#skF_1') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_153])).

tff(c_182,plain,(
    k2_xboole_0('#skF_2','#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_167,c_46])).

tff(c_384,plain,(
    k5_xboole_0(k5_xboole_0('#skF_2','#skF_3'),'#skF_2') = k3_xboole_0('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_182,c_350])).

tff(c_905,plain,(
    k3_xboole_0('#skF_2','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_821,c_384])).

tff(c_44,plain,(
    '#skF_2' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_8,plain,(
    ! [A_7,B_8] : r1_tarski(k4_xboole_0(A_7,B_8),A_7) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_32,plain,(
    ! [B_46,A_45] :
      ( k1_tarski(B_46) = A_45
      | k1_xboole_0 = A_45
      | ~ r1_tarski(A_45,k1_tarski(B_46)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_187,plain,(
    ! [A_45] :
      ( k1_tarski('#skF_1') = A_45
      | k1_xboole_0 = A_45
      | ~ r1_tarski(A_45,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_167,c_32])).

tff(c_207,plain,(
    ! [A_70] :
      ( A_70 = '#skF_2'
      | k1_xboole_0 = A_70
      | ~ r1_tarski(A_70,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_167,c_187])).

tff(c_228,plain,(
    ! [B_8] :
      ( k4_xboole_0('#skF_2',B_8) = '#skF_2'
      | k4_xboole_0('#skF_2',B_8) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_207])).

tff(c_6,plain,(
    ! [A_5,B_6] : k5_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = k4_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_863,plain,(
    k5_xboole_0('#skF_2',k3_xboole_0('#skF_2','#skF_3')) = k5_xboole_0('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_384,c_818])).

tff(c_900,plain,(
    k5_xboole_0('#skF_2','#skF_3') = k4_xboole_0('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_863])).

tff(c_1000,plain,(
    k5_xboole_0(k4_xboole_0('#skF_2','#skF_3'),'#skF_2') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_900,c_821])).

tff(c_1379,plain,
    ( k5_xboole_0(k1_xboole_0,'#skF_2') = '#skF_3'
    | k4_xboole_0('#skF_2','#skF_3') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_228,c_1000])).

tff(c_1384,plain,
    ( '#skF_2' = '#skF_3'
    | k4_xboole_0('#skF_2','#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_396,c_1379])).

tff(c_1385,plain,(
    k4_xboole_0('#skF_2','#skF_3') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_1384])).

tff(c_613,plain,(
    ! [A_5,B_6] : k5_xboole_0(A_5,k4_xboole_0(A_5,B_6)) = k3_xboole_0(A_5,B_6) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_549])).

tff(c_1392,plain,(
    k5_xboole_0('#skF_2','#skF_2') = k3_xboole_0('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1385,c_613])).

tff(c_1404,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_905,c_14,c_1392])).

tff(c_1406,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_1404])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:59:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.96/1.58  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.96/1.58  
% 2.96/1.58  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.96/1.59  %$ r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.96/1.59  
% 2.96/1.59  %Foreground sorts:
% 2.96/1.59  
% 2.96/1.59  
% 2.96/1.59  %Background operators:
% 2.96/1.59  
% 2.96/1.59  
% 2.96/1.59  %Foreground operators:
% 2.96/1.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.96/1.59  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.96/1.59  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.96/1.59  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.96/1.59  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.96/1.59  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.96/1.59  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.96/1.59  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.96/1.59  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.96/1.59  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.96/1.59  tff('#skF_2', type, '#skF_2': $i).
% 2.96/1.59  tff('#skF_3', type, '#skF_3': $i).
% 2.96/1.59  tff('#skF_1', type, '#skF_1': $i).
% 2.96/1.59  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.96/1.59  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.96/1.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.96/1.59  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.96/1.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.96/1.59  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.96/1.59  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.96/1.59  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.96/1.59  
% 2.96/1.60  tff(f_76, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~(B = C)) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_zfmisc_1)).
% 2.96/1.60  tff(f_39, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 2.96/1.60  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 2.96/1.60  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 2.96/1.60  tff(f_41, axiom, (![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_xboole_1)).
% 2.96/1.60  tff(f_37, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 2.96/1.60  tff(f_35, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.96/1.60  tff(f_61, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 2.96/1.60  tff(f_33, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 2.96/1.60  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.96/1.60  tff(c_40, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.96/1.60  tff(c_14, plain, (![A_14]: (k5_xboole_0(A_14, A_14)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.96/1.60  tff(c_4, plain, (![A_3]: (k3_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.96/1.60  tff(c_2, plain, (![A_1]: (k2_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.96/1.60  tff(c_350, plain, (![A_80, B_81]: (k5_xboole_0(k5_xboole_0(A_80, B_81), k2_xboole_0(A_80, B_81))=k3_xboole_0(A_80, B_81))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.96/1.60  tff(c_390, plain, (![A_1]: (k5_xboole_0(k5_xboole_0(A_1, A_1), A_1)=k3_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_350])).
% 2.96/1.60  tff(c_396, plain, (![A_1]: (k5_xboole_0(k1_xboole_0, A_1)=A_1)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_14, c_390])).
% 2.96/1.60  tff(c_12, plain, (![A_11, B_12, C_13]: (k5_xboole_0(k5_xboole_0(A_11, B_12), C_13)=k5_xboole_0(A_11, k5_xboole_0(B_12, C_13)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.96/1.60  tff(c_398, plain, (![A_82]: (k5_xboole_0(k1_xboole_0, A_82)=A_82)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_14, c_390])).
% 2.96/1.60  tff(c_269, plain, (![A_75, B_76, C_77]: (k5_xboole_0(k5_xboole_0(A_75, B_76), C_77)=k5_xboole_0(A_75, k5_xboole_0(B_76, C_77)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.96/1.60  tff(c_283, plain, (![A_75, B_76]: (k5_xboole_0(A_75, k5_xboole_0(B_76, k5_xboole_0(A_75, B_76)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_269, c_14])).
% 2.96/1.60  tff(c_451, plain, (![A_83]: (k5_xboole_0(A_83, k5_xboole_0(A_83, k1_xboole_0))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_398, c_283])).
% 2.96/1.60  tff(c_470, plain, (![A_83, C_13]: (k5_xboole_0(A_83, k5_xboole_0(k5_xboole_0(A_83, k1_xboole_0), C_13))=k5_xboole_0(k1_xboole_0, C_13))), inference(superposition, [status(thm), theory('equality')], [c_451, c_12])).
% 2.96/1.60  tff(c_549, plain, (![A_90, C_91]: (k5_xboole_0(A_90, k5_xboole_0(A_90, C_91))=C_91)), inference(demodulation, [status(thm), theory('equality')], [c_396, c_396, c_12, c_470])).
% 2.96/1.60  tff(c_616, plain, (![A_14]: (k5_xboole_0(A_14, k1_xboole_0)=A_14)), inference(superposition, [status(thm), theory('equality')], [c_14, c_549])).
% 2.96/1.60  tff(c_599, plain, (![B_76, A_75]: (k5_xboole_0(B_76, k5_xboole_0(A_75, B_76))=k5_xboole_0(A_75, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_283, c_549])).
% 2.96/1.60  tff(c_818, plain, (![B_101, A_102]: (k5_xboole_0(B_101, k5_xboole_0(A_102, B_101))=A_102)), inference(demodulation, [status(thm), theory('equality')], [c_616, c_599])).
% 2.96/1.60  tff(c_815, plain, (![B_76, A_75]: (k5_xboole_0(B_76, k5_xboole_0(A_75, B_76))=A_75)), inference(demodulation, [status(thm), theory('equality')], [c_616, c_599])).
% 2.96/1.60  tff(c_821, plain, (![A_102, B_101]: (k5_xboole_0(k5_xboole_0(A_102, B_101), A_102)=B_101)), inference(superposition, [status(thm), theory('equality')], [c_818, c_815])).
% 2.96/1.60  tff(c_42, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.96/1.60  tff(c_46, plain, (k2_xboole_0('#skF_2', '#skF_3')=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.96/1.60  tff(c_87, plain, (![A_56, B_57]: (r1_tarski(A_56, k2_xboole_0(A_56, B_57)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.96/1.60  tff(c_90, plain, (r1_tarski('#skF_2', k1_tarski('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_46, c_87])).
% 2.96/1.60  tff(c_150, plain, (![B_67, A_68]: (k1_tarski(B_67)=A_68 | k1_xboole_0=A_68 | ~r1_tarski(A_68, k1_tarski(B_67)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.96/1.60  tff(c_153, plain, (k1_tarski('#skF_1')='#skF_2' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_90, c_150])).
% 2.96/1.60  tff(c_167, plain, (k1_tarski('#skF_1')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_42, c_153])).
% 2.96/1.60  tff(c_182, plain, (k2_xboole_0('#skF_2', '#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_167, c_46])).
% 2.96/1.60  tff(c_384, plain, (k5_xboole_0(k5_xboole_0('#skF_2', '#skF_3'), '#skF_2')=k3_xboole_0('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_182, c_350])).
% 2.96/1.60  tff(c_905, plain, (k3_xboole_0('#skF_2', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_821, c_384])).
% 2.96/1.60  tff(c_44, plain, ('#skF_2'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.96/1.60  tff(c_8, plain, (![A_7, B_8]: (r1_tarski(k4_xboole_0(A_7, B_8), A_7))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.96/1.60  tff(c_32, plain, (![B_46, A_45]: (k1_tarski(B_46)=A_45 | k1_xboole_0=A_45 | ~r1_tarski(A_45, k1_tarski(B_46)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.96/1.60  tff(c_187, plain, (![A_45]: (k1_tarski('#skF_1')=A_45 | k1_xboole_0=A_45 | ~r1_tarski(A_45, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_167, c_32])).
% 2.96/1.60  tff(c_207, plain, (![A_70]: (A_70='#skF_2' | k1_xboole_0=A_70 | ~r1_tarski(A_70, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_167, c_187])).
% 2.96/1.60  tff(c_228, plain, (![B_8]: (k4_xboole_0('#skF_2', B_8)='#skF_2' | k4_xboole_0('#skF_2', B_8)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_207])).
% 2.96/1.60  tff(c_6, plain, (![A_5, B_6]: (k5_xboole_0(A_5, k3_xboole_0(A_5, B_6))=k4_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.96/1.60  tff(c_863, plain, (k5_xboole_0('#skF_2', k3_xboole_0('#skF_2', '#skF_3'))=k5_xboole_0('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_384, c_818])).
% 2.96/1.60  tff(c_900, plain, (k5_xboole_0('#skF_2', '#skF_3')=k4_xboole_0('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_863])).
% 2.96/1.60  tff(c_1000, plain, (k5_xboole_0(k4_xboole_0('#skF_2', '#skF_3'), '#skF_2')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_900, c_821])).
% 2.96/1.60  tff(c_1379, plain, (k5_xboole_0(k1_xboole_0, '#skF_2')='#skF_3' | k4_xboole_0('#skF_2', '#skF_3')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_228, c_1000])).
% 2.96/1.60  tff(c_1384, plain, ('#skF_2'='#skF_3' | k4_xboole_0('#skF_2', '#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_396, c_1379])).
% 2.96/1.60  tff(c_1385, plain, (k4_xboole_0('#skF_2', '#skF_3')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_44, c_1384])).
% 2.96/1.60  tff(c_613, plain, (![A_5, B_6]: (k5_xboole_0(A_5, k4_xboole_0(A_5, B_6))=k3_xboole_0(A_5, B_6))), inference(superposition, [status(thm), theory('equality')], [c_6, c_549])).
% 2.96/1.60  tff(c_1392, plain, (k5_xboole_0('#skF_2', '#skF_2')=k3_xboole_0('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1385, c_613])).
% 2.96/1.60  tff(c_1404, plain, (k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_905, c_14, c_1392])).
% 2.96/1.60  tff(c_1406, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_1404])).
% 2.96/1.60  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.96/1.60  
% 2.96/1.60  Inference rules
% 2.96/1.60  ----------------------
% 2.96/1.60  #Ref     : 0
% 2.96/1.60  #Sup     : 342
% 2.96/1.60  #Fact    : 1
% 2.96/1.60  #Define  : 0
% 2.96/1.60  #Split   : 0
% 2.96/1.60  #Chain   : 0
% 2.96/1.60  #Close   : 0
% 2.96/1.60  
% 2.96/1.60  Ordering : KBO
% 2.96/1.60  
% 2.96/1.60  Simplification rules
% 2.96/1.60  ----------------------
% 2.96/1.60  #Subsume      : 2
% 2.96/1.60  #Demod        : 173
% 2.96/1.60  #Tautology    : 210
% 2.96/1.60  #SimpNegUnit  : 7
% 2.96/1.60  #BackRed      : 7
% 2.96/1.60  
% 2.96/1.60  #Partial instantiations: 0
% 2.96/1.60  #Strategies tried      : 1
% 2.96/1.60  
% 2.96/1.60  Timing (in seconds)
% 2.96/1.60  ----------------------
% 2.96/1.60  Preprocessing        : 0.30
% 2.96/1.60  Parsing              : 0.15
% 2.96/1.60  CNF conversion       : 0.02
% 2.96/1.60  Main loop            : 0.47
% 2.96/1.60  Inferencing          : 0.18
% 2.96/1.60  Reduction            : 0.17
% 2.96/1.60  Demodulation         : 0.13
% 2.96/1.60  BG Simplification    : 0.02
% 2.96/1.61  Subsumption          : 0.06
% 2.96/1.61  Abstraction          : 0.02
% 2.96/1.61  MUC search           : 0.00
% 2.96/1.61  Cooper               : 0.00
% 2.96/1.61  Total                : 0.80
% 2.96/1.61  Index Insertion      : 0.00
% 2.96/1.61  Index Deletion       : 0.00
% 2.96/1.61  Index Matching       : 0.00
% 2.96/1.61  BG Taut test         : 0.00
%------------------------------------------------------------------------------
