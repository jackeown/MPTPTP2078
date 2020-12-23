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
% DateTime   : Thu Dec  3 09:57:25 EST 2020

% Result     : Theorem 5.16s
% Output     : CNFRefutation 5.16s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 290 expanded)
%              Number of leaves         :   25 ( 102 expanded)
%              Depth                    :   18
%              Number of atoms          :   88 ( 648 expanded)
%              Number of equality atoms :   39 ( 110 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

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

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_52,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_59,axiom,(
    ! [A,B] :
      ( A != B
     => r1_xboole_0(k1_tarski(A),k1_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_zfmisc_1)).

tff(f_78,negated_conjecture,(
    ~ ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( k3_xboole_0(A,k1_tarski(B)) = k1_tarski(B)
     => r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_zfmisc_1)).

tff(f_75,axiom,(
    ! [A] : k1_setfam_1(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_setfam_1)).

tff(f_54,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_73,axiom,(
    ! [A,B] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & k1_setfam_1(k2_xboole_0(A,B)) != k3_xboole_0(k1_setfam_1(A),k1_setfam_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_setfam_1)).

tff(c_1418,plain,(
    ! [A_527,B_528] :
      ( r2_hidden('#skF_3'(A_527,B_528),k3_xboole_0(A_527,B_528))
      | r1_xboole_0(A_527,B_528) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_6,plain,(
    ! [D_6,A_1,B_2] :
      ( r2_hidden(D_6,A_1)
      | ~ r2_hidden(D_6,k3_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_1613,plain,(
    ! [A_527,B_528] :
      ( r2_hidden('#skF_3'(A_527,B_528),A_527)
      | r1_xboole_0(A_527,B_528) ) ),
    inference(resolution,[status(thm)],[c_1418,c_6])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,k3_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_1720,plain,(
    ! [A_596,B_597] :
      ( r2_hidden('#skF_3'(A_596,B_597),B_597)
      | r1_xboole_0(A_596,B_597) ) ),
    inference(resolution,[status(thm)],[c_1418,c_4])).

tff(c_26,plain,(
    ! [A_9,B_10,C_13] :
      ( ~ r1_xboole_0(A_9,B_10)
      | ~ r2_hidden(C_13,k3_xboole_0(A_9,B_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_1932,plain,(
    ! [A_664,B_665,A_666] :
      ( ~ r1_xboole_0(A_664,B_665)
      | r1_xboole_0(A_666,k3_xboole_0(A_664,B_665)) ) ),
    inference(resolution,[status(thm)],[c_1720,c_26])).

tff(c_20,plain,(
    ! [A_7,B_8] :
      ( k3_xboole_0(A_7,B_8) = k1_xboole_0
      | ~ r1_xboole_0(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2147,plain,(
    ! [A_769,A_770,B_771] :
      ( k3_xboole_0(A_769,k3_xboole_0(A_770,B_771)) = k1_xboole_0
      | ~ r1_xboole_0(A_770,B_771) ) ),
    inference(resolution,[status(thm)],[c_1932,c_20])).

tff(c_2174,plain,(
    ! [D_6,A_769,A_770,B_771] :
      ( r2_hidden(D_6,A_769)
      | ~ r2_hidden(D_6,k1_xboole_0)
      | ~ r1_xboole_0(A_770,B_771) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2147,c_6])).

tff(c_3047,plain,(
    ! [A_770,B_771] : ~ r1_xboole_0(A_770,B_771) ),
    inference(splitLeft,[status(thm)],[c_2174])).

tff(c_30,plain,(
    ! [A_16,B_17] :
      ( r1_xboole_0(k1_tarski(A_16),k1_tarski(B_17))
      | B_17 = A_16 ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_3056,plain,(
    ! [B_907,A_908] : B_907 = A_908 ),
    inference(negUnitSimplification,[status(thm)],[c_3047,c_30])).

tff(c_38,plain,(
    k1_setfam_1(k2_tarski('#skF_4','#skF_5')) != k3_xboole_0('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_3168,plain,(
    ! [B_907] : k3_xboole_0('#skF_4','#skF_5') != B_907 ),
    inference(superposition,[status(thm),theory(equality)],[c_3056,c_38])).

tff(c_3180,plain,(
    $false ),
    inference(reflexivity,[status(thm),theory(equality)],[c_3168])).

tff(c_3182,plain,(
    ! [D_1165,A_1166] :
      ( r2_hidden(D_1165,A_1166)
      | ~ r2_hidden(D_1165,k1_xboole_0) ) ),
    inference(splitRight,[status(thm)],[c_2174])).

tff(c_3191,plain,(
    ! [B_1167,A_1168] :
      ( r2_hidden('#skF_3'(k1_xboole_0,B_1167),A_1168)
      | r1_xboole_0(k1_xboole_0,B_1167) ) ),
    inference(resolution,[status(thm)],[c_1613,c_3182])).

tff(c_3208,plain,(
    ! [A_9,B_10,B_1167] :
      ( ~ r1_xboole_0(A_9,B_10)
      | r1_xboole_0(k1_xboole_0,B_1167) ) ),
    inference(resolution,[status(thm)],[c_3191,c_26])).

tff(c_3210,plain,(
    ! [A_9,B_10] : ~ r1_xboole_0(A_9,B_10) ),
    inference(splitLeft,[status(thm)],[c_3208])).

tff(c_3217,plain,(
    ! [B_17,A_16] : B_17 = A_16 ),
    inference(negUnitSimplification,[status(thm)],[c_3210,c_30])).

tff(c_22,plain,(
    ! [A_7,B_8] :
      ( r1_xboole_0(A_7,B_8)
      | k3_xboole_0(A_7,B_8) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_3345,plain,(
    ! [A_1461,B_1462] : k3_xboole_0(A_1461,B_1462) != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_3210,c_22])).

tff(c_3347,plain,(
    ! [B_17] : k1_xboole_0 != B_17 ),
    inference(superposition,[status(thm),theory(equality)],[c_3217,c_3345])).

tff(c_3353,plain,(
    $false ),
    inference(reflexivity,[status(thm),theory(equality)],[c_3347])).

tff(c_3354,plain,(
    ! [B_1167] : r1_xboole_0(k1_xboole_0,B_1167) ),
    inference(splitRight,[status(thm)],[c_3208])).

tff(c_3356,plain,(
    ! [B_1495] : r1_xboole_0(k1_xboole_0,B_1495) ),
    inference(splitRight,[status(thm)],[c_3208])).

tff(c_3364,plain,(
    ! [B_1496] : k3_xboole_0(k1_xboole_0,B_1496) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_3356,c_20])).

tff(c_3397,plain,(
    ! [B_1496,C_13] :
      ( ~ r1_xboole_0(k1_xboole_0,B_1496)
      | ~ r2_hidden(C_13,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3364,c_26])).

tff(c_3418,plain,(
    ! [C_13] : ~ r2_hidden(C_13,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3354,c_3397])).

tff(c_32,plain,(
    ! [B_19,A_18] :
      ( r2_hidden(B_19,A_18)
      | k3_xboole_0(A_18,k1_tarski(B_19)) != k1_tarski(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_3391,plain,(
    ! [B_19] :
      ( r2_hidden(B_19,k1_xboole_0)
      | k1_tarski(B_19) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3364,c_32])).

tff(c_3546,plain,(
    ! [B_19] : k1_tarski(B_19) != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_3418,c_3391])).

tff(c_36,plain,(
    ! [A_22] : k1_setfam_1(k1_tarski(A_22)) = A_22 ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_28,plain,(
    ! [A_14,B_15] : k2_xboole_0(k1_tarski(A_14),k1_tarski(B_15)) = k2_tarski(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_2647,plain,(
    ! [A_839,B_840] :
      ( k3_xboole_0(k1_setfam_1(A_839),k1_setfam_1(B_840)) = k1_setfam_1(k2_xboole_0(A_839,B_840))
      | k1_xboole_0 = B_840
      | k1_xboole_0 = A_839 ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_3044,plain,(
    ! [A_839,A_22] :
      ( k1_setfam_1(k2_xboole_0(A_839,k1_tarski(A_22))) = k3_xboole_0(k1_setfam_1(A_839),A_22)
      | k1_tarski(A_22) = k1_xboole_0
      | k1_xboole_0 = A_839 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_2647])).

tff(c_5841,plain,(
    ! [A_1605,A_1606] :
      ( k1_setfam_1(k2_xboole_0(A_1605,k1_tarski(A_1606))) = k3_xboole_0(k1_setfam_1(A_1605),A_1606)
      | k1_xboole_0 = A_1605 ) ),
    inference(negUnitSimplification,[status(thm)],[c_3546,c_3044])).

tff(c_5862,plain,(
    ! [A_14,B_15] :
      ( k3_xboole_0(k1_setfam_1(k1_tarski(A_14)),B_15) = k1_setfam_1(k2_tarski(A_14,B_15))
      | k1_tarski(A_14) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_5841])).

tff(c_5868,plain,(
    ! [A_14,B_15] :
      ( k1_setfam_1(k2_tarski(A_14,B_15)) = k3_xboole_0(A_14,B_15)
      | k1_tarski(A_14) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_5862])).

tff(c_5869,plain,(
    ! [A_14,B_15] : k1_setfam_1(k2_tarski(A_14,B_15)) = k3_xboole_0(A_14,B_15) ),
    inference(negUnitSimplification,[status(thm)],[c_3546,c_5868])).

tff(c_5874,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5869,c_38])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:50:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.16/1.92  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.16/1.93  
% 5.16/1.93  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.16/1.93  %$ r2_hidden > r1_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_2 > #skF_4
% 5.16/1.93  
% 5.16/1.93  %Foreground sorts:
% 5.16/1.93  
% 5.16/1.93  
% 5.16/1.93  %Background operators:
% 5.16/1.93  
% 5.16/1.93  
% 5.16/1.93  %Foreground operators:
% 5.16/1.93  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 5.16/1.93  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.16/1.93  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.16/1.93  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.16/1.93  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.16/1.93  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 5.16/1.93  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.16/1.93  tff('#skF_5', type, '#skF_5': $i).
% 5.16/1.93  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 5.16/1.93  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 5.16/1.93  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.16/1.93  tff('#skF_4', type, '#skF_4': $i).
% 5.16/1.93  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.16/1.93  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.16/1.93  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.16/1.93  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 5.16/1.93  
% 5.16/1.94  tff(f_52, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 5.16/1.94  tff(f_34, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 5.16/1.94  tff(f_38, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 5.16/1.94  tff(f_59, axiom, (![A, B]: (~(A = B) => r1_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_zfmisc_1)).
% 5.16/1.94  tff(f_78, negated_conjecture, ~(![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 5.16/1.94  tff(f_63, axiom, (![A, B]: ((k3_xboole_0(A, k1_tarski(B)) = k1_tarski(B)) => r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_zfmisc_1)).
% 5.16/1.94  tff(f_75, axiom, (![A]: (k1_setfam_1(k1_tarski(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_setfam_1)).
% 5.16/1.94  tff(f_54, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_enumset1)).
% 5.16/1.94  tff(f_73, axiom, (![A, B]: ~((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(k1_setfam_1(k2_xboole_0(A, B)) = k3_xboole_0(k1_setfam_1(A), k1_setfam_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_setfam_1)).
% 5.16/1.94  tff(c_1418, plain, (![A_527, B_528]: (r2_hidden('#skF_3'(A_527, B_528), k3_xboole_0(A_527, B_528)) | r1_xboole_0(A_527, B_528))), inference(cnfTransformation, [status(thm)], [f_52])).
% 5.16/1.94  tff(c_6, plain, (![D_6, A_1, B_2]: (r2_hidden(D_6, A_1) | ~r2_hidden(D_6, k3_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 5.16/1.94  tff(c_1613, plain, (![A_527, B_528]: (r2_hidden('#skF_3'(A_527, B_528), A_527) | r1_xboole_0(A_527, B_528))), inference(resolution, [status(thm)], [c_1418, c_6])).
% 5.16/1.94  tff(c_4, plain, (![D_6, B_2, A_1]: (r2_hidden(D_6, B_2) | ~r2_hidden(D_6, k3_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 5.16/1.94  tff(c_1720, plain, (![A_596, B_597]: (r2_hidden('#skF_3'(A_596, B_597), B_597) | r1_xboole_0(A_596, B_597))), inference(resolution, [status(thm)], [c_1418, c_4])).
% 5.16/1.94  tff(c_26, plain, (![A_9, B_10, C_13]: (~r1_xboole_0(A_9, B_10) | ~r2_hidden(C_13, k3_xboole_0(A_9, B_10)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 5.16/1.94  tff(c_1932, plain, (![A_664, B_665, A_666]: (~r1_xboole_0(A_664, B_665) | r1_xboole_0(A_666, k3_xboole_0(A_664, B_665)))), inference(resolution, [status(thm)], [c_1720, c_26])).
% 5.16/1.94  tff(c_20, plain, (![A_7, B_8]: (k3_xboole_0(A_7, B_8)=k1_xboole_0 | ~r1_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.16/1.94  tff(c_2147, plain, (![A_769, A_770, B_771]: (k3_xboole_0(A_769, k3_xboole_0(A_770, B_771))=k1_xboole_0 | ~r1_xboole_0(A_770, B_771))), inference(resolution, [status(thm)], [c_1932, c_20])).
% 5.16/1.94  tff(c_2174, plain, (![D_6, A_769, A_770, B_771]: (r2_hidden(D_6, A_769) | ~r2_hidden(D_6, k1_xboole_0) | ~r1_xboole_0(A_770, B_771))), inference(superposition, [status(thm), theory('equality')], [c_2147, c_6])).
% 5.16/1.94  tff(c_3047, plain, (![A_770, B_771]: (~r1_xboole_0(A_770, B_771))), inference(splitLeft, [status(thm)], [c_2174])).
% 5.16/1.94  tff(c_30, plain, (![A_16, B_17]: (r1_xboole_0(k1_tarski(A_16), k1_tarski(B_17)) | B_17=A_16)), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.16/1.94  tff(c_3056, plain, (![B_907, A_908]: (B_907=A_908)), inference(negUnitSimplification, [status(thm)], [c_3047, c_30])).
% 5.16/1.94  tff(c_38, plain, (k1_setfam_1(k2_tarski('#skF_4', '#skF_5'))!=k3_xboole_0('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.16/1.94  tff(c_3168, plain, (![B_907]: (k3_xboole_0('#skF_4', '#skF_5')!=B_907)), inference(superposition, [status(thm), theory('equality')], [c_3056, c_38])).
% 5.16/1.94  tff(c_3180, plain, $false, inference(reflexivity, [status(thm), theory('equality')], [c_3168])).
% 5.16/1.94  tff(c_3182, plain, (![D_1165, A_1166]: (r2_hidden(D_1165, A_1166) | ~r2_hidden(D_1165, k1_xboole_0))), inference(splitRight, [status(thm)], [c_2174])).
% 5.16/1.94  tff(c_3191, plain, (![B_1167, A_1168]: (r2_hidden('#skF_3'(k1_xboole_0, B_1167), A_1168) | r1_xboole_0(k1_xboole_0, B_1167))), inference(resolution, [status(thm)], [c_1613, c_3182])).
% 5.16/1.94  tff(c_3208, plain, (![A_9, B_10, B_1167]: (~r1_xboole_0(A_9, B_10) | r1_xboole_0(k1_xboole_0, B_1167))), inference(resolution, [status(thm)], [c_3191, c_26])).
% 5.16/1.94  tff(c_3210, plain, (![A_9, B_10]: (~r1_xboole_0(A_9, B_10))), inference(splitLeft, [status(thm)], [c_3208])).
% 5.16/1.94  tff(c_3217, plain, (![B_17, A_16]: (B_17=A_16)), inference(negUnitSimplification, [status(thm)], [c_3210, c_30])).
% 5.16/1.94  tff(c_22, plain, (![A_7, B_8]: (r1_xboole_0(A_7, B_8) | k3_xboole_0(A_7, B_8)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.16/1.94  tff(c_3345, plain, (![A_1461, B_1462]: (k3_xboole_0(A_1461, B_1462)!=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_3210, c_22])).
% 5.16/1.94  tff(c_3347, plain, (![B_17]: (k1_xboole_0!=B_17)), inference(superposition, [status(thm), theory('equality')], [c_3217, c_3345])).
% 5.16/1.94  tff(c_3353, plain, $false, inference(reflexivity, [status(thm), theory('equality')], [c_3347])).
% 5.16/1.94  tff(c_3354, plain, (![B_1167]: (r1_xboole_0(k1_xboole_0, B_1167))), inference(splitRight, [status(thm)], [c_3208])).
% 5.16/1.94  tff(c_3356, plain, (![B_1495]: (r1_xboole_0(k1_xboole_0, B_1495))), inference(splitRight, [status(thm)], [c_3208])).
% 5.16/1.94  tff(c_3364, plain, (![B_1496]: (k3_xboole_0(k1_xboole_0, B_1496)=k1_xboole_0)), inference(resolution, [status(thm)], [c_3356, c_20])).
% 5.16/1.94  tff(c_3397, plain, (![B_1496, C_13]: (~r1_xboole_0(k1_xboole_0, B_1496) | ~r2_hidden(C_13, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_3364, c_26])).
% 5.16/1.94  tff(c_3418, plain, (![C_13]: (~r2_hidden(C_13, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_3354, c_3397])).
% 5.16/1.94  tff(c_32, plain, (![B_19, A_18]: (r2_hidden(B_19, A_18) | k3_xboole_0(A_18, k1_tarski(B_19))!=k1_tarski(B_19))), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.16/1.94  tff(c_3391, plain, (![B_19]: (r2_hidden(B_19, k1_xboole_0) | k1_tarski(B_19)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_3364, c_32])).
% 5.16/1.94  tff(c_3546, plain, (![B_19]: (k1_tarski(B_19)!=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_3418, c_3391])).
% 5.16/1.94  tff(c_36, plain, (![A_22]: (k1_setfam_1(k1_tarski(A_22))=A_22)), inference(cnfTransformation, [status(thm)], [f_75])).
% 5.16/1.94  tff(c_28, plain, (![A_14, B_15]: (k2_xboole_0(k1_tarski(A_14), k1_tarski(B_15))=k2_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.16/1.94  tff(c_2647, plain, (![A_839, B_840]: (k3_xboole_0(k1_setfam_1(A_839), k1_setfam_1(B_840))=k1_setfam_1(k2_xboole_0(A_839, B_840)) | k1_xboole_0=B_840 | k1_xboole_0=A_839)), inference(cnfTransformation, [status(thm)], [f_73])).
% 5.16/1.94  tff(c_3044, plain, (![A_839, A_22]: (k1_setfam_1(k2_xboole_0(A_839, k1_tarski(A_22)))=k3_xboole_0(k1_setfam_1(A_839), A_22) | k1_tarski(A_22)=k1_xboole_0 | k1_xboole_0=A_839)), inference(superposition, [status(thm), theory('equality')], [c_36, c_2647])).
% 5.16/1.94  tff(c_5841, plain, (![A_1605, A_1606]: (k1_setfam_1(k2_xboole_0(A_1605, k1_tarski(A_1606)))=k3_xboole_0(k1_setfam_1(A_1605), A_1606) | k1_xboole_0=A_1605)), inference(negUnitSimplification, [status(thm)], [c_3546, c_3044])).
% 5.16/1.94  tff(c_5862, plain, (![A_14, B_15]: (k3_xboole_0(k1_setfam_1(k1_tarski(A_14)), B_15)=k1_setfam_1(k2_tarski(A_14, B_15)) | k1_tarski(A_14)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_28, c_5841])).
% 5.16/1.94  tff(c_5868, plain, (![A_14, B_15]: (k1_setfam_1(k2_tarski(A_14, B_15))=k3_xboole_0(A_14, B_15) | k1_tarski(A_14)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_36, c_5862])).
% 5.16/1.94  tff(c_5869, plain, (![A_14, B_15]: (k1_setfam_1(k2_tarski(A_14, B_15))=k3_xboole_0(A_14, B_15))), inference(negUnitSimplification, [status(thm)], [c_3546, c_5868])).
% 5.16/1.94  tff(c_5874, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5869, c_38])).
% 5.16/1.94  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.16/1.94  
% 5.16/1.94  Inference rules
% 5.16/1.94  ----------------------
% 5.16/1.94  #Ref     : 3
% 5.16/1.94  #Sup     : 1296
% 5.16/1.94  #Fact    : 0
% 5.16/1.94  #Define  : 0
% 5.16/1.94  #Split   : 3
% 5.16/1.94  #Chain   : 0
% 5.16/1.94  #Close   : 0
% 5.16/1.94  
% 5.16/1.94  Ordering : KBO
% 5.16/1.94  
% 5.16/1.94  Simplification rules
% 5.16/1.94  ----------------------
% 5.16/1.94  #Subsume      : 282
% 5.16/1.94  #Demod        : 370
% 5.16/1.94  #Tautology    : 285
% 5.16/1.94  #SimpNegUnit  : 51
% 5.16/1.94  #BackRed      : 14
% 5.16/1.94  
% 5.16/1.94  #Partial instantiations: 946
% 5.16/1.94  #Strategies tried      : 1
% 5.16/1.94  
% 5.16/1.94  Timing (in seconds)
% 5.16/1.94  ----------------------
% 5.16/1.94  Preprocessing        : 0.29
% 5.16/1.94  Parsing              : 0.16
% 5.16/1.95  CNF conversion       : 0.02
% 5.16/1.95  Main loop            : 0.88
% 5.16/1.95  Inferencing          : 0.33
% 5.16/1.95  Reduction            : 0.21
% 5.16/1.95  Demodulation         : 0.14
% 5.16/1.95  BG Simplification    : 0.04
% 5.16/1.95  Subsumption          : 0.22
% 5.16/1.95  Abstraction          : 0.05
% 5.16/1.95  MUC search           : 0.00
% 5.16/1.95  Cooper               : 0.00
% 5.16/1.95  Total                : 1.20
% 5.16/1.95  Index Insertion      : 0.00
% 5.16/1.95  Index Deletion       : 0.00
% 5.16/1.95  Index Matching       : 0.00
% 5.16/1.95  BG Taut test         : 0.00
%------------------------------------------------------------------------------
