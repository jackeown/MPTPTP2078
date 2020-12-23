%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:45 EST 2020

% Result     : Theorem 9.09s
% Output     : CNFRefutation 9.09s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 523 expanded)
%              Number of leaves         :   19 ( 188 expanded)
%              Depth                    :   18
%              Number of atoms          :   66 ( 653 expanded)
%              Number of equality atoms :   59 ( 524 expanded)
%              Maximal formula depth    :    9 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_48,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( k2_xboole_0(A,B) = k2_xboole_0(C,D)
          & r1_xboole_0(C,A)
          & r1_xboole_0(D,B) )
       => C = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_37,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

tff(c_16,plain,(
    '#skF_2' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_14,plain,(
    ! [A_12,B_13] : k2_xboole_0(k3_xboole_0(A_12,B_13),k4_xboole_0(A_12,B_13)) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_22,plain,(
    k2_xboole_0('#skF_3','#skF_4') = k2_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_23,plain,(
    k2_xboole_0('#skF_1','#skF_2') = k2_xboole_0('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_22])).

tff(c_12,plain,(
    ! [A_9,B_10,C_11] : k4_xboole_0(k4_xboole_0(A_9,B_10),C_11) = k4_xboole_0(A_9,k2_xboole_0(B_10,C_11)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_18,plain,(
    r1_xboole_0('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_95,plain,(
    ! [A_20,B_21] :
      ( k3_xboole_0(A_20,B_21) = k1_xboole_0
      | ~ r1_xboole_0(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_106,plain,(
    k3_xboole_0('#skF_4','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_18,c_95])).

tff(c_135,plain,(
    ! [A_22,B_23] : k2_xboole_0(k3_xboole_0(A_22,B_23),k4_xboole_0(A_22,B_23)) = A_22 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_150,plain,(
    k2_xboole_0(k1_xboole_0,k4_xboole_0('#skF_4','#skF_2')) = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_106,c_135])).

tff(c_20,plain,(
    r1_xboole_0('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_107,plain,(
    k3_xboole_0('#skF_3','#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_20,c_95])).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_115,plain,(
    k3_xboole_0('#skF_1','#skF_3') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_107,c_4])).

tff(c_144,plain,(
    k2_xboole_0(k1_xboole_0,k4_xboole_0('#skF_1','#skF_3')) = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_115,c_135])).

tff(c_10,plain,(
    ! [A_7,B_8] : k4_xboole_0(k2_xboole_0(A_7,B_8),B_8) = k4_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_324,plain,(
    ! [A_30,B_31,C_32] : k4_xboole_0(k4_xboole_0(A_30,B_31),C_32) = k4_xboole_0(A_30,k2_xboole_0(B_31,C_32)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_351,plain,(
    ! [A_7,B_8,C_32] : k4_xboole_0(k2_xboole_0(A_7,B_8),k2_xboole_0(B_8,C_32)) = k4_xboole_0(k4_xboole_0(A_7,B_8),C_32) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_324])).

tff(c_971,plain,(
    ! [A_37,B_38,C_39] : k4_xboole_0(k2_xboole_0(A_37,B_38),k2_xboole_0(B_38,C_39)) = k4_xboole_0(A_37,k2_xboole_0(B_38,C_39)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_351])).

tff(c_1066,plain,(
    ! [A_37] : k4_xboole_0(A_37,k2_xboole_0(k1_xboole_0,k4_xboole_0('#skF_1','#skF_3'))) = k4_xboole_0(k2_xboole_0(A_37,k1_xboole_0),'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_144,c_971])).

tff(c_1867,plain,(
    ! [A_50] : k4_xboole_0(k2_xboole_0(A_50,k1_xboole_0),'#skF_1') = k4_xboole_0(A_50,'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_144,c_1066])).

tff(c_2083,plain,(
    ! [B_55] : k4_xboole_0(k2_xboole_0(k1_xboole_0,B_55),'#skF_1') = k4_xboole_0(B_55,'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1867])).

tff(c_2128,plain,(
    k4_xboole_0(k4_xboole_0('#skF_4','#skF_2'),'#skF_1') = k4_xboole_0('#skF_4','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_150,c_2083])).

tff(c_4158,plain,(
    k4_xboole_0('#skF_4',k2_xboole_0('#skF_2','#skF_1')) = k4_xboole_0('#skF_4','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_2128])).

tff(c_4167,plain,(
    k4_xboole_0('#skF_4',k2_xboole_0('#skF_4','#skF_3')) = k4_xboole_0('#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_23,c_2,c_4158])).

tff(c_1072,plain,(
    ! [A_37] : k4_xboole_0(A_37,k2_xboole_0(k1_xboole_0,k4_xboole_0('#skF_4','#skF_2'))) = k4_xboole_0(k2_xboole_0(A_37,k1_xboole_0),'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_150,c_971])).

tff(c_1226,plain,(
    ! [A_42] : k4_xboole_0(k2_xboole_0(A_42,k1_xboole_0),'#skF_4') = k4_xboole_0(A_42,'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_150,c_1072])).

tff(c_1719,plain,(
    ! [B_48] : k4_xboole_0(k2_xboole_0(k1_xboole_0,B_48),'#skF_4') = k4_xboole_0(B_48,'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1226])).

tff(c_1761,plain,(
    k4_xboole_0(k4_xboole_0('#skF_1','#skF_3'),'#skF_4') = k4_xboole_0('#skF_1','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_144,c_1719])).

tff(c_2528,plain,(
    k4_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_4')) = k4_xboole_0('#skF_1','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1761,c_12])).

tff(c_2544,plain,(
    k4_xboole_0('#skF_1',k2_xboole_0('#skF_4','#skF_3')) = k4_xboole_0('#skF_1','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_2528])).

tff(c_1090,plain,(
    ! [A_37,A_1,B_2] : k4_xboole_0(k2_xboole_0(A_37,A_1),k2_xboole_0(B_2,A_1)) = k4_xboole_0(A_37,k2_xboole_0(A_1,B_2)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_971])).

tff(c_3277,plain,(
    ! [A_68,A_69,B_70] : k4_xboole_0(k2_xboole_0(A_68,A_69),k2_xboole_0(B_70,A_69)) = k4_xboole_0(A_68,k2_xboole_0(A_69,B_70)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_971])).

tff(c_3595,plain,(
    ! [B_71] : k4_xboole_0(k2_xboole_0('#skF_4','#skF_3'),k2_xboole_0(B_71,'#skF_2')) = k4_xboole_0('#skF_1',k2_xboole_0('#skF_2',B_71)) ),
    inference(superposition,[status(thm),theory(equality)],[c_23,c_3277])).

tff(c_3665,plain,(
    k4_xboole_0(k2_xboole_0('#skF_4','#skF_3'),k2_xboole_0('#skF_4','#skF_3')) = k4_xboole_0('#skF_1',k2_xboole_0('#skF_2','#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_23,c_3595])).

tff(c_3680,plain,(
    k4_xboole_0('#skF_4',k2_xboole_0('#skF_4','#skF_3')) = k4_xboole_0('#skF_1','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2544,c_2,c_1090,c_23,c_2,c_3665])).

tff(c_6802,plain,(
    k4_xboole_0('#skF_1','#skF_4') = k4_xboole_0('#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4167,c_3680])).

tff(c_153,plain,(
    ! [B_4,A_3] : k2_xboole_0(k3_xboole_0(B_4,A_3),k4_xboole_0(A_3,B_4)) = A_3 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_135])).

tff(c_6875,plain,(
    k2_xboole_0(k3_xboole_0('#skF_4','#skF_1'),k4_xboole_0('#skF_4','#skF_1')) = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_6802,c_153])).

tff(c_6887,plain,(
    '#skF_1' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_6875])).

tff(c_147,plain,(
    k2_xboole_0(k1_xboole_0,k4_xboole_0('#skF_3','#skF_1')) = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_107,c_135])).

tff(c_6927,plain,(
    k2_xboole_0(k1_xboole_0,k4_xboole_0('#skF_3','#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6887,c_147])).

tff(c_159,plain,(
    ! [A_24,B_25] : k4_xboole_0(k2_xboole_0(A_24,B_25),B_25) = k4_xboole_0(A_24,B_25) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_177,plain,(
    ! [A_1,B_2] : k4_xboole_0(k2_xboole_0(A_1,B_2),A_1) = k4_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_159])).

tff(c_267,plain,(
    ! [A_28,B_29] : k4_xboole_0(k2_xboole_0(A_28,B_29),A_28) = k4_xboole_0(B_29,A_28) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_159])).

tff(c_314,plain,(
    k4_xboole_0(k2_xboole_0('#skF_4','#skF_3'),'#skF_1') = k4_xboole_0('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_23,c_267])).

tff(c_6925,plain,(
    k4_xboole_0(k2_xboole_0('#skF_4','#skF_3'),'#skF_4') = k4_xboole_0('#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6887,c_6887,c_314])).

tff(c_6944,plain,(
    k4_xboole_0('#skF_2','#skF_4') = k4_xboole_0('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_177,c_6925])).

tff(c_213,plain,(
    ! [B_26,A_27] : k2_xboole_0(k3_xboole_0(B_26,A_27),k4_xboole_0(A_27,B_26)) = A_27 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_135])).

tff(c_245,plain,(
    k2_xboole_0(k1_xboole_0,k4_xboole_0('#skF_2','#skF_4')) = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_106,c_213])).

tff(c_7676,plain,(
    k2_xboole_0(k1_xboole_0,k4_xboole_0('#skF_3','#skF_4')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6944,c_245])).

tff(c_7677,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6927,c_7676])).

tff(c_7679,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_16,c_7677])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:48:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.09/2.95  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.09/2.96  
% 9.09/2.96  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.09/2.96  %$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 9.09/2.96  
% 9.09/2.96  %Foreground sorts:
% 9.09/2.96  
% 9.09/2.96  
% 9.09/2.96  %Background operators:
% 9.09/2.96  
% 9.09/2.96  
% 9.09/2.96  %Foreground operators:
% 9.09/2.96  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.09/2.96  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 9.09/2.96  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.09/2.96  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 9.09/2.96  tff('#skF_2', type, '#skF_2': $i).
% 9.09/2.96  tff('#skF_3', type, '#skF_3': $i).
% 9.09/2.96  tff('#skF_1', type, '#skF_1': $i).
% 9.09/2.96  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.09/2.96  tff('#skF_4', type, '#skF_4': $i).
% 9.09/2.96  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.09/2.96  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 9.09/2.96  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 9.09/2.96  
% 9.09/2.97  tff(f_48, negated_conjecture, ~(![A, B, C, D]: ((((k2_xboole_0(A, B) = k2_xboole_0(C, D)) & r1_xboole_0(C, A)) & r1_xboole_0(D, B)) => (C = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_xboole_1)).
% 9.09/2.97  tff(f_39, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_xboole_1)).
% 9.09/2.97  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 9.09/2.97  tff(f_37, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 9.09/2.97  tff(f_33, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 9.09/2.97  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 9.09/2.97  tff(f_35, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_xboole_1)).
% 9.09/2.97  tff(c_16, plain, ('#skF_2'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_48])).
% 9.09/2.97  tff(c_14, plain, (![A_12, B_13]: (k2_xboole_0(k3_xboole_0(A_12, B_13), k4_xboole_0(A_12, B_13))=A_12)), inference(cnfTransformation, [status(thm)], [f_39])).
% 9.09/2.97  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 9.09/2.97  tff(c_22, plain, (k2_xboole_0('#skF_3', '#skF_4')=k2_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_48])).
% 9.09/2.97  tff(c_23, plain, (k2_xboole_0('#skF_1', '#skF_2')=k2_xboole_0('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_22])).
% 9.09/2.97  tff(c_12, plain, (![A_9, B_10, C_11]: (k4_xboole_0(k4_xboole_0(A_9, B_10), C_11)=k4_xboole_0(A_9, k2_xboole_0(B_10, C_11)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 9.09/2.97  tff(c_18, plain, (r1_xboole_0('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_48])).
% 9.09/2.97  tff(c_95, plain, (![A_20, B_21]: (k3_xboole_0(A_20, B_21)=k1_xboole_0 | ~r1_xboole_0(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_33])).
% 9.09/2.97  tff(c_106, plain, (k3_xboole_0('#skF_4', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_18, c_95])).
% 9.09/2.97  tff(c_135, plain, (![A_22, B_23]: (k2_xboole_0(k3_xboole_0(A_22, B_23), k4_xboole_0(A_22, B_23))=A_22)), inference(cnfTransformation, [status(thm)], [f_39])).
% 9.09/2.97  tff(c_150, plain, (k2_xboole_0(k1_xboole_0, k4_xboole_0('#skF_4', '#skF_2'))='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_106, c_135])).
% 9.09/2.97  tff(c_20, plain, (r1_xboole_0('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_48])).
% 9.09/2.97  tff(c_107, plain, (k3_xboole_0('#skF_3', '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_20, c_95])).
% 9.09/2.97  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(B_4, A_3)=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 9.09/2.97  tff(c_115, plain, (k3_xboole_0('#skF_1', '#skF_3')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_107, c_4])).
% 9.09/2.97  tff(c_144, plain, (k2_xboole_0(k1_xboole_0, k4_xboole_0('#skF_1', '#skF_3'))='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_115, c_135])).
% 9.09/2.97  tff(c_10, plain, (![A_7, B_8]: (k4_xboole_0(k2_xboole_0(A_7, B_8), B_8)=k4_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_35])).
% 9.09/2.97  tff(c_324, plain, (![A_30, B_31, C_32]: (k4_xboole_0(k4_xboole_0(A_30, B_31), C_32)=k4_xboole_0(A_30, k2_xboole_0(B_31, C_32)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 9.09/2.97  tff(c_351, plain, (![A_7, B_8, C_32]: (k4_xboole_0(k2_xboole_0(A_7, B_8), k2_xboole_0(B_8, C_32))=k4_xboole_0(k4_xboole_0(A_7, B_8), C_32))), inference(superposition, [status(thm), theory('equality')], [c_10, c_324])).
% 9.09/2.97  tff(c_971, plain, (![A_37, B_38, C_39]: (k4_xboole_0(k2_xboole_0(A_37, B_38), k2_xboole_0(B_38, C_39))=k4_xboole_0(A_37, k2_xboole_0(B_38, C_39)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_351])).
% 9.09/2.97  tff(c_1066, plain, (![A_37]: (k4_xboole_0(A_37, k2_xboole_0(k1_xboole_0, k4_xboole_0('#skF_1', '#skF_3')))=k4_xboole_0(k2_xboole_0(A_37, k1_xboole_0), '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_144, c_971])).
% 9.09/2.97  tff(c_1867, plain, (![A_50]: (k4_xboole_0(k2_xboole_0(A_50, k1_xboole_0), '#skF_1')=k4_xboole_0(A_50, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_144, c_1066])).
% 9.09/2.97  tff(c_2083, plain, (![B_55]: (k4_xboole_0(k2_xboole_0(k1_xboole_0, B_55), '#skF_1')=k4_xboole_0(B_55, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1867])).
% 9.09/2.97  tff(c_2128, plain, (k4_xboole_0(k4_xboole_0('#skF_4', '#skF_2'), '#skF_1')=k4_xboole_0('#skF_4', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_150, c_2083])).
% 9.09/2.97  tff(c_4158, plain, (k4_xboole_0('#skF_4', k2_xboole_0('#skF_2', '#skF_1'))=k4_xboole_0('#skF_4', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_12, c_2128])).
% 9.09/2.97  tff(c_4167, plain, (k4_xboole_0('#skF_4', k2_xboole_0('#skF_4', '#skF_3'))=k4_xboole_0('#skF_4', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_23, c_2, c_4158])).
% 9.09/2.97  tff(c_1072, plain, (![A_37]: (k4_xboole_0(A_37, k2_xboole_0(k1_xboole_0, k4_xboole_0('#skF_4', '#skF_2')))=k4_xboole_0(k2_xboole_0(A_37, k1_xboole_0), '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_150, c_971])).
% 9.09/2.97  tff(c_1226, plain, (![A_42]: (k4_xboole_0(k2_xboole_0(A_42, k1_xboole_0), '#skF_4')=k4_xboole_0(A_42, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_150, c_1072])).
% 9.09/2.97  tff(c_1719, plain, (![B_48]: (k4_xboole_0(k2_xboole_0(k1_xboole_0, B_48), '#skF_4')=k4_xboole_0(B_48, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1226])).
% 9.09/2.97  tff(c_1761, plain, (k4_xboole_0(k4_xboole_0('#skF_1', '#skF_3'), '#skF_4')=k4_xboole_0('#skF_1', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_144, c_1719])).
% 9.09/2.98  tff(c_2528, plain, (k4_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_4'))=k4_xboole_0('#skF_1', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1761, c_12])).
% 9.09/2.98  tff(c_2544, plain, (k4_xboole_0('#skF_1', k2_xboole_0('#skF_4', '#skF_3'))=k4_xboole_0('#skF_1', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_2528])).
% 9.09/2.98  tff(c_1090, plain, (![A_37, A_1, B_2]: (k4_xboole_0(k2_xboole_0(A_37, A_1), k2_xboole_0(B_2, A_1))=k4_xboole_0(A_37, k2_xboole_0(A_1, B_2)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_971])).
% 9.09/2.98  tff(c_3277, plain, (![A_68, A_69, B_70]: (k4_xboole_0(k2_xboole_0(A_68, A_69), k2_xboole_0(B_70, A_69))=k4_xboole_0(A_68, k2_xboole_0(A_69, B_70)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_971])).
% 9.09/2.98  tff(c_3595, plain, (![B_71]: (k4_xboole_0(k2_xboole_0('#skF_4', '#skF_3'), k2_xboole_0(B_71, '#skF_2'))=k4_xboole_0('#skF_1', k2_xboole_0('#skF_2', B_71)))), inference(superposition, [status(thm), theory('equality')], [c_23, c_3277])).
% 9.09/2.98  tff(c_3665, plain, (k4_xboole_0(k2_xboole_0('#skF_4', '#skF_3'), k2_xboole_0('#skF_4', '#skF_3'))=k4_xboole_0('#skF_1', k2_xboole_0('#skF_2', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_23, c_3595])).
% 9.09/2.98  tff(c_3680, plain, (k4_xboole_0('#skF_4', k2_xboole_0('#skF_4', '#skF_3'))=k4_xboole_0('#skF_1', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2544, c_2, c_1090, c_23, c_2, c_3665])).
% 9.09/2.98  tff(c_6802, plain, (k4_xboole_0('#skF_1', '#skF_4')=k4_xboole_0('#skF_4', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4167, c_3680])).
% 9.09/2.98  tff(c_153, plain, (![B_4, A_3]: (k2_xboole_0(k3_xboole_0(B_4, A_3), k4_xboole_0(A_3, B_4))=A_3)), inference(superposition, [status(thm), theory('equality')], [c_4, c_135])).
% 9.09/2.98  tff(c_6875, plain, (k2_xboole_0(k3_xboole_0('#skF_4', '#skF_1'), k4_xboole_0('#skF_4', '#skF_1'))='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_6802, c_153])).
% 9.09/2.98  tff(c_6887, plain, ('#skF_1'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_14, c_6875])).
% 9.09/2.98  tff(c_147, plain, (k2_xboole_0(k1_xboole_0, k4_xboole_0('#skF_3', '#skF_1'))='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_107, c_135])).
% 9.09/2.98  tff(c_6927, plain, (k2_xboole_0(k1_xboole_0, k4_xboole_0('#skF_3', '#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_6887, c_147])).
% 9.09/2.98  tff(c_159, plain, (![A_24, B_25]: (k4_xboole_0(k2_xboole_0(A_24, B_25), B_25)=k4_xboole_0(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_35])).
% 9.09/2.98  tff(c_177, plain, (![A_1, B_2]: (k4_xboole_0(k2_xboole_0(A_1, B_2), A_1)=k4_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_159])).
% 9.09/2.98  tff(c_267, plain, (![A_28, B_29]: (k4_xboole_0(k2_xboole_0(A_28, B_29), A_28)=k4_xboole_0(B_29, A_28))), inference(superposition, [status(thm), theory('equality')], [c_2, c_159])).
% 9.09/2.98  tff(c_314, plain, (k4_xboole_0(k2_xboole_0('#skF_4', '#skF_3'), '#skF_1')=k4_xboole_0('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_23, c_267])).
% 9.09/2.98  tff(c_6925, plain, (k4_xboole_0(k2_xboole_0('#skF_4', '#skF_3'), '#skF_4')=k4_xboole_0('#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_6887, c_6887, c_314])).
% 9.09/2.98  tff(c_6944, plain, (k4_xboole_0('#skF_2', '#skF_4')=k4_xboole_0('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_177, c_6925])).
% 9.09/2.98  tff(c_213, plain, (![B_26, A_27]: (k2_xboole_0(k3_xboole_0(B_26, A_27), k4_xboole_0(A_27, B_26))=A_27)), inference(superposition, [status(thm), theory('equality')], [c_4, c_135])).
% 9.09/2.98  tff(c_245, plain, (k2_xboole_0(k1_xboole_0, k4_xboole_0('#skF_2', '#skF_4'))='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_106, c_213])).
% 9.09/2.98  tff(c_7676, plain, (k2_xboole_0(k1_xboole_0, k4_xboole_0('#skF_3', '#skF_4'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_6944, c_245])).
% 9.09/2.98  tff(c_7677, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_6927, c_7676])).
% 9.09/2.98  tff(c_7679, plain, $false, inference(negUnitSimplification, [status(thm)], [c_16, c_7677])).
% 9.09/2.98  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.09/2.98  
% 9.09/2.98  Inference rules
% 9.09/2.98  ----------------------
% 9.09/2.98  #Ref     : 0
% 9.09/2.98  #Sup     : 2047
% 9.09/2.98  #Fact    : 0
% 9.09/2.98  #Define  : 0
% 9.09/2.98  #Split   : 0
% 9.09/2.98  #Chain   : 0
% 9.09/2.98  #Close   : 0
% 9.09/2.98  
% 9.09/2.98  Ordering : KBO
% 9.09/2.98  
% 9.09/2.98  Simplification rules
% 9.09/2.98  ----------------------
% 9.09/2.98  #Subsume      : 6
% 9.09/2.98  #Demod        : 2753
% 9.09/2.98  #Tautology    : 613
% 9.09/2.98  #SimpNegUnit  : 1
% 9.09/2.98  #BackRed      : 67
% 9.09/2.98  
% 9.09/2.98  #Partial instantiations: 0
% 9.09/2.98  #Strategies tried      : 1
% 9.09/2.98  
% 9.09/2.98  Timing (in seconds)
% 9.09/2.98  ----------------------
% 9.09/2.98  Preprocessing        : 0.27
% 9.09/2.98  Parsing              : 0.14
% 9.09/2.98  CNF conversion       : 0.02
% 9.09/2.98  Main loop            : 1.94
% 9.09/2.98  Inferencing          : 0.37
% 9.09/2.98  Reduction            : 1.13
% 9.09/2.98  Demodulation         : 0.99
% 9.09/2.98  BG Simplification    : 0.06
% 9.09/2.98  Subsumption          : 0.28
% 9.09/2.98  Abstraction          : 0.08
% 9.09/2.98  MUC search           : 0.00
% 9.09/2.98  Cooper               : 0.00
% 9.09/2.98  Total                : 2.24
% 9.09/2.98  Index Insertion      : 0.00
% 9.09/2.98  Index Deletion       : 0.00
% 9.09/2.98  Index Matching       : 0.00
% 9.09/2.98  BG Taut test         : 0.00
%------------------------------------------------------------------------------
