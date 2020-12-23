%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:18 EST 2020

% Result     : Theorem 9.30s
% Output     : CNFRefutation 9.53s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 146 expanded)
%              Number of leaves         :   22 (  58 expanded)
%              Depth                    :   14
%              Number of atoms          :   75 ( 154 expanded)
%              Number of equality atoms :   57 ( 116 expanded)
%              Maximal formula depth    :    7 (   3 average)
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

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_54,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r1_tarski(A,B)
          & r1_xboole_0(B,C) )
       => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

tff(f_43,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_41,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_45,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(c_119,plain,(
    ! [A_30,B_31] :
      ( r1_xboole_0(A_30,B_31)
      | k3_xboole_0(A_30,B_31) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_24,plain,(
    ~ r1_xboole_0('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_123,plain,(
    k3_xboole_0('#skF_1','#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_119,c_24])).

tff(c_18,plain,(
    ! [A_13] : k4_xboole_0(A_13,k1_xboole_0) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_47,plain,(
    ! [A_21,B_22] : r1_tarski(k4_xboole_0(A_21,B_22),A_21) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_50,plain,(
    ! [A_13] : r1_tarski(A_13,A_13) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_47])).

tff(c_124,plain,(
    ! [A_32,B_33] :
      ( k4_xboole_0(A_32,B_33) = k1_xboole_0
      | ~ r1_tarski(A_32,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_138,plain,(
    ! [A_13] : k4_xboole_0(A_13,A_13) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_50,c_124])).

tff(c_248,plain,(
    ! [A_39,B_40] : k4_xboole_0(A_39,k4_xboole_0(A_39,B_40)) = k3_xboole_0(A_39,B_40) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_283,plain,(
    ! [A_13] : k4_xboole_0(A_13,A_13) = k3_xboole_0(A_13,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_248])).

tff(c_294,plain,(
    ! [A_41] : k3_xboole_0(A_41,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_283])).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_299,plain,(
    ! [A_41] : k3_xboole_0(k1_xboole_0,A_41) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_294,c_4])).

tff(c_28,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_140,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_28,c_124])).

tff(c_280,plain,(
    k4_xboole_0('#skF_1',k1_xboole_0) = k3_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_140,c_248])).

tff(c_288,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_280])).

tff(c_22,plain,(
    ! [A_17,B_18] : k4_xboole_0(A_17,k4_xboole_0(A_17,B_18)) = k3_xboole_0(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_16,plain,(
    ! [A_11,B_12] : r1_tarski(k4_xboole_0(A_11,B_12),A_11) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_555,plain,(
    ! [A_52,B_53] : k4_xboole_0(k4_xboole_0(A_52,B_53),A_52) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_16,c_124])).

tff(c_569,plain,(
    ! [A_52,B_53] : k4_xboole_0(k4_xboole_0(A_52,B_53),k1_xboole_0) = k3_xboole_0(k4_xboole_0(A_52,B_53),A_52) ),
    inference(superposition,[status(thm),theory(equality)],[c_555,c_22])).

tff(c_7956,plain,(
    ! [A_224,B_225] : k3_xboole_0(k4_xboole_0(A_224,B_225),A_224) = k4_xboole_0(A_224,B_225) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_569])).

tff(c_11754,plain,(
    ! [A_275,B_276] : k3_xboole_0(A_275,k4_xboole_0(A_275,B_276)) = k4_xboole_0(A_275,B_276) ),
    inference(superposition,[status(thm),theory(equality)],[c_7956,c_4])).

tff(c_26,plain,(
    r1_xboole_0('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_152,plain,(
    ! [A_34,B_35] :
      ( k3_xboole_0(A_34,B_35) = k1_xboole_0
      | ~ r1_xboole_0(A_34,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_160,plain,(
    k3_xboole_0('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_26,c_152])).

tff(c_2042,plain,(
    ! [A_94,B_95] : k4_xboole_0(A_94,k3_xboole_0(A_94,B_95)) = k3_xboole_0(A_94,k4_xboole_0(A_94,B_95)) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_248])).

tff(c_2112,plain,(
    k3_xboole_0('#skF_2',k4_xboole_0('#skF_2','#skF_3')) = k4_xboole_0('#skF_2',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_160,c_2042])).

tff(c_2137,plain,(
    k3_xboole_0('#skF_2',k4_xboole_0('#skF_2','#skF_3')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_2112])).

tff(c_11896,plain,(
    k4_xboole_0('#skF_2','#skF_3') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_11754,c_2137])).

tff(c_20,plain,(
    ! [A_14,B_15,C_16] : k4_xboole_0(k4_xboole_0(A_14,B_15),C_16) = k4_xboole_0(A_14,k2_xboole_0(B_15,C_16)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_12324,plain,(
    ! [C_16] : k4_xboole_0('#skF_2',k2_xboole_0('#skF_3',C_16)) = k4_xboole_0('#skF_2',C_16) ),
    inference(superposition,[status(thm),theory(equality)],[c_11896,c_20])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_10,plain,(
    ! [A_7] : k2_xboole_0(A_7,A_7) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_334,plain,(
    ! [A_43,B_44,C_45] : k4_xboole_0(k4_xboole_0(A_43,B_44),C_45) = k4_xboole_0(A_43,k2_xboole_0(B_44,C_45)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_3166,plain,(
    ! [A_117,B_118,C_119] : k4_xboole_0(k4_xboole_0(A_117,B_118),k4_xboole_0(A_117,k2_xboole_0(B_118,C_119))) = k3_xboole_0(k4_xboole_0(A_117,B_118),C_119) ),
    inference(superposition,[status(thm),theory(equality)],[c_334,c_22])).

tff(c_3340,plain,(
    ! [A_117,A_7] : k4_xboole_0(k4_xboole_0(A_117,A_7),k4_xboole_0(A_117,A_7)) = k3_xboole_0(k4_xboole_0(A_117,A_7),A_7) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_3166])).

tff(c_3510,plain,(
    ! [A_123,A_124] : k3_xboole_0(A_123,k4_xboole_0(A_124,A_123)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_4,c_3340])).

tff(c_19310,plain,(
    ! [C_320,A_321,B_322] : k3_xboole_0(C_320,k4_xboole_0(A_321,k2_xboole_0(B_322,C_320))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_3510])).

tff(c_19628,plain,(
    ! [B_323,A_324,A_325] : k3_xboole_0(B_323,k4_xboole_0(A_324,k2_xboole_0(B_323,A_325))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_19310])).

tff(c_19949,plain,(
    ! [C_326] : k3_xboole_0('#skF_3',k4_xboole_0('#skF_2',C_326)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_12324,c_19628])).

tff(c_20340,plain,(
    ! [B_328] : k3_xboole_0('#skF_3',k3_xboole_0('#skF_2',B_328)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_19949])).

tff(c_20898,plain,(
    ! [A_331] : k3_xboole_0('#skF_3',k3_xboole_0(A_331,'#skF_2')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_20340])).

tff(c_21020,plain,(
    k3_xboole_0('#skF_3','#skF_1') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_288,c_20898])).

tff(c_448,plain,(
    ! [A_47,B_48] : r1_tarski(k3_xboole_0(A_47,B_48),A_47) ),
    inference(superposition,[status(thm),theory(equality)],[c_248,c_16])).

tff(c_14,plain,(
    ! [A_9,B_10] :
      ( k4_xboole_0(A_9,B_10) = k1_xboole_0
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_476,plain,(
    ! [A_47,B_48] : k4_xboole_0(k3_xboole_0(A_47,B_48),A_47) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_448,c_14])).

tff(c_387,plain,(
    ! [A_13,C_45] : k4_xboole_0(A_13,k2_xboole_0(k1_xboole_0,C_45)) = k4_xboole_0(A_13,C_45) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_334])).

tff(c_347,plain,(
    ! [A_43,B_44,B_18] : k4_xboole_0(A_43,k2_xboole_0(B_44,k4_xboole_0(k4_xboole_0(A_43,B_44),B_18))) = k3_xboole_0(k4_xboole_0(A_43,B_44),B_18) ),
    inference(superposition,[status(thm),theory(equality)],[c_334,c_22])).

tff(c_4662,plain,(
    ! [A_150,B_151,B_152] : k4_xboole_0(A_150,k2_xboole_0(B_151,k4_xboole_0(A_150,k2_xboole_0(B_151,B_152)))) = k3_xboole_0(k4_xboole_0(A_150,B_151),B_152) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_347])).

tff(c_4798,plain,(
    ! [A_13,C_45] : k4_xboole_0(A_13,k2_xboole_0(k1_xboole_0,k4_xboole_0(A_13,C_45))) = k3_xboole_0(k4_xboole_0(A_13,k1_xboole_0),C_45) ),
    inference(superposition,[status(thm),theory(equality)],[c_387,c_4662])).

tff(c_16558,plain,(
    ! [A_302,C_303] : k4_xboole_0(A_302,k2_xboole_0(k1_xboole_0,k4_xboole_0(A_302,C_303))) = k3_xboole_0(A_302,C_303) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_4798])).

tff(c_16863,plain,(
    ! [A_47,B_48] : k4_xboole_0(k3_xboole_0(A_47,B_48),k2_xboole_0(k1_xboole_0,k1_xboole_0)) = k3_xboole_0(k3_xboole_0(A_47,B_48),A_47) ),
    inference(superposition,[status(thm),theory(equality)],[c_476,c_16558])).

tff(c_16980,plain,(
    ! [A_47,B_48] : k3_xboole_0(k3_xboole_0(A_47,B_48),A_47) = k3_xboole_0(A_47,B_48) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_10,c_16863])).

tff(c_21082,plain,(
    k3_xboole_0(k1_xboole_0,'#skF_3') = k3_xboole_0('#skF_3','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_21020,c_16980])).

tff(c_21179,plain,(
    k3_xboole_0('#skF_1','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_299,c_4,c_21082])).

tff(c_21181,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_123,c_21179])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:43:02 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.30/3.51  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.30/3.52  
% 9.30/3.52  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.30/3.52  %$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 9.30/3.52  
% 9.30/3.52  %Foreground sorts:
% 9.30/3.52  
% 9.30/3.52  
% 9.30/3.52  %Background operators:
% 9.30/3.52  
% 9.30/3.52  
% 9.30/3.52  %Foreground operators:
% 9.30/3.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.30/3.52  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 9.30/3.52  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.30/3.52  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.30/3.52  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 9.30/3.52  tff('#skF_2', type, '#skF_2': $i).
% 9.30/3.52  tff('#skF_3', type, '#skF_3': $i).
% 9.30/3.52  tff('#skF_1', type, '#skF_1': $i).
% 9.30/3.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.30/3.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.30/3.52  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 9.30/3.52  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 9.30/3.52  
% 9.53/3.54  tff(f_33, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 9.53/3.54  tff(f_54, negated_conjecture, ~(![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_xboole_1)).
% 9.53/3.54  tff(f_43, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 9.53/3.54  tff(f_41, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 9.53/3.54  tff(f_39, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 9.53/3.54  tff(f_47, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 9.53/3.54  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 9.53/3.54  tff(f_45, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 9.53/3.54  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 9.53/3.54  tff(f_35, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 9.53/3.54  tff(c_119, plain, (![A_30, B_31]: (r1_xboole_0(A_30, B_31) | k3_xboole_0(A_30, B_31)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 9.53/3.54  tff(c_24, plain, (~r1_xboole_0('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_54])).
% 9.53/3.54  tff(c_123, plain, (k3_xboole_0('#skF_1', '#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_119, c_24])).
% 9.53/3.54  tff(c_18, plain, (![A_13]: (k4_xboole_0(A_13, k1_xboole_0)=A_13)), inference(cnfTransformation, [status(thm)], [f_43])).
% 9.53/3.54  tff(c_47, plain, (![A_21, B_22]: (r1_tarski(k4_xboole_0(A_21, B_22), A_21))), inference(cnfTransformation, [status(thm)], [f_41])).
% 9.53/3.54  tff(c_50, plain, (![A_13]: (r1_tarski(A_13, A_13))), inference(superposition, [status(thm), theory('equality')], [c_18, c_47])).
% 9.53/3.54  tff(c_124, plain, (![A_32, B_33]: (k4_xboole_0(A_32, B_33)=k1_xboole_0 | ~r1_tarski(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_39])).
% 9.53/3.54  tff(c_138, plain, (![A_13]: (k4_xboole_0(A_13, A_13)=k1_xboole_0)), inference(resolution, [status(thm)], [c_50, c_124])).
% 9.53/3.54  tff(c_248, plain, (![A_39, B_40]: (k4_xboole_0(A_39, k4_xboole_0(A_39, B_40))=k3_xboole_0(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_47])).
% 9.53/3.54  tff(c_283, plain, (![A_13]: (k4_xboole_0(A_13, A_13)=k3_xboole_0(A_13, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_18, c_248])).
% 9.53/3.54  tff(c_294, plain, (![A_41]: (k3_xboole_0(A_41, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_138, c_283])).
% 9.53/3.54  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(B_4, A_3)=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 9.53/3.54  tff(c_299, plain, (![A_41]: (k3_xboole_0(k1_xboole_0, A_41)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_294, c_4])).
% 9.53/3.54  tff(c_28, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_54])).
% 9.53/3.54  tff(c_140, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_28, c_124])).
% 9.53/3.54  tff(c_280, plain, (k4_xboole_0('#skF_1', k1_xboole_0)=k3_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_140, c_248])).
% 9.53/3.54  tff(c_288, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_18, c_280])).
% 9.53/3.54  tff(c_22, plain, (![A_17, B_18]: (k4_xboole_0(A_17, k4_xboole_0(A_17, B_18))=k3_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_47])).
% 9.53/3.54  tff(c_16, plain, (![A_11, B_12]: (r1_tarski(k4_xboole_0(A_11, B_12), A_11))), inference(cnfTransformation, [status(thm)], [f_41])).
% 9.53/3.54  tff(c_555, plain, (![A_52, B_53]: (k4_xboole_0(k4_xboole_0(A_52, B_53), A_52)=k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_124])).
% 9.53/3.54  tff(c_569, plain, (![A_52, B_53]: (k4_xboole_0(k4_xboole_0(A_52, B_53), k1_xboole_0)=k3_xboole_0(k4_xboole_0(A_52, B_53), A_52))), inference(superposition, [status(thm), theory('equality')], [c_555, c_22])).
% 9.53/3.54  tff(c_7956, plain, (![A_224, B_225]: (k3_xboole_0(k4_xboole_0(A_224, B_225), A_224)=k4_xboole_0(A_224, B_225))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_569])).
% 9.53/3.54  tff(c_11754, plain, (![A_275, B_276]: (k3_xboole_0(A_275, k4_xboole_0(A_275, B_276))=k4_xboole_0(A_275, B_276))), inference(superposition, [status(thm), theory('equality')], [c_7956, c_4])).
% 9.53/3.54  tff(c_26, plain, (r1_xboole_0('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_54])).
% 9.53/3.54  tff(c_152, plain, (![A_34, B_35]: (k3_xboole_0(A_34, B_35)=k1_xboole_0 | ~r1_xboole_0(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_33])).
% 9.53/3.54  tff(c_160, plain, (k3_xboole_0('#skF_2', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_26, c_152])).
% 9.53/3.54  tff(c_2042, plain, (![A_94, B_95]: (k4_xboole_0(A_94, k3_xboole_0(A_94, B_95))=k3_xboole_0(A_94, k4_xboole_0(A_94, B_95)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_248])).
% 9.53/3.54  tff(c_2112, plain, (k3_xboole_0('#skF_2', k4_xboole_0('#skF_2', '#skF_3'))=k4_xboole_0('#skF_2', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_160, c_2042])).
% 9.53/3.54  tff(c_2137, plain, (k3_xboole_0('#skF_2', k4_xboole_0('#skF_2', '#skF_3'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_18, c_2112])).
% 9.53/3.54  tff(c_11896, plain, (k4_xboole_0('#skF_2', '#skF_3')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_11754, c_2137])).
% 9.53/3.54  tff(c_20, plain, (![A_14, B_15, C_16]: (k4_xboole_0(k4_xboole_0(A_14, B_15), C_16)=k4_xboole_0(A_14, k2_xboole_0(B_15, C_16)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 9.53/3.54  tff(c_12324, plain, (![C_16]: (k4_xboole_0('#skF_2', k2_xboole_0('#skF_3', C_16))=k4_xboole_0('#skF_2', C_16))), inference(superposition, [status(thm), theory('equality')], [c_11896, c_20])).
% 9.53/3.54  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 9.53/3.54  tff(c_10, plain, (![A_7]: (k2_xboole_0(A_7, A_7)=A_7)), inference(cnfTransformation, [status(thm)], [f_35])).
% 9.53/3.54  tff(c_334, plain, (![A_43, B_44, C_45]: (k4_xboole_0(k4_xboole_0(A_43, B_44), C_45)=k4_xboole_0(A_43, k2_xboole_0(B_44, C_45)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 9.53/3.54  tff(c_3166, plain, (![A_117, B_118, C_119]: (k4_xboole_0(k4_xboole_0(A_117, B_118), k4_xboole_0(A_117, k2_xboole_0(B_118, C_119)))=k3_xboole_0(k4_xboole_0(A_117, B_118), C_119))), inference(superposition, [status(thm), theory('equality')], [c_334, c_22])).
% 9.53/3.54  tff(c_3340, plain, (![A_117, A_7]: (k4_xboole_0(k4_xboole_0(A_117, A_7), k4_xboole_0(A_117, A_7))=k3_xboole_0(k4_xboole_0(A_117, A_7), A_7))), inference(superposition, [status(thm), theory('equality')], [c_10, c_3166])).
% 9.53/3.54  tff(c_3510, plain, (![A_123, A_124]: (k3_xboole_0(A_123, k4_xboole_0(A_124, A_123))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_138, c_4, c_3340])).
% 9.53/3.54  tff(c_19310, plain, (![C_320, A_321, B_322]: (k3_xboole_0(C_320, k4_xboole_0(A_321, k2_xboole_0(B_322, C_320)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_20, c_3510])).
% 9.53/3.54  tff(c_19628, plain, (![B_323, A_324, A_325]: (k3_xboole_0(B_323, k4_xboole_0(A_324, k2_xboole_0(B_323, A_325)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_19310])).
% 9.53/3.54  tff(c_19949, plain, (![C_326]: (k3_xboole_0('#skF_3', k4_xboole_0('#skF_2', C_326))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_12324, c_19628])).
% 9.53/3.54  tff(c_20340, plain, (![B_328]: (k3_xboole_0('#skF_3', k3_xboole_0('#skF_2', B_328))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_22, c_19949])).
% 9.53/3.54  tff(c_20898, plain, (![A_331]: (k3_xboole_0('#skF_3', k3_xboole_0(A_331, '#skF_2'))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_4, c_20340])).
% 9.53/3.54  tff(c_21020, plain, (k3_xboole_0('#skF_3', '#skF_1')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_288, c_20898])).
% 9.53/3.54  tff(c_448, plain, (![A_47, B_48]: (r1_tarski(k3_xboole_0(A_47, B_48), A_47))), inference(superposition, [status(thm), theory('equality')], [c_248, c_16])).
% 9.53/3.54  tff(c_14, plain, (![A_9, B_10]: (k4_xboole_0(A_9, B_10)=k1_xboole_0 | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_39])).
% 9.53/3.54  tff(c_476, plain, (![A_47, B_48]: (k4_xboole_0(k3_xboole_0(A_47, B_48), A_47)=k1_xboole_0)), inference(resolution, [status(thm)], [c_448, c_14])).
% 9.53/3.54  tff(c_387, plain, (![A_13, C_45]: (k4_xboole_0(A_13, k2_xboole_0(k1_xboole_0, C_45))=k4_xboole_0(A_13, C_45))), inference(superposition, [status(thm), theory('equality')], [c_18, c_334])).
% 9.53/3.54  tff(c_347, plain, (![A_43, B_44, B_18]: (k4_xboole_0(A_43, k2_xboole_0(B_44, k4_xboole_0(k4_xboole_0(A_43, B_44), B_18)))=k3_xboole_0(k4_xboole_0(A_43, B_44), B_18))), inference(superposition, [status(thm), theory('equality')], [c_334, c_22])).
% 9.53/3.54  tff(c_4662, plain, (![A_150, B_151, B_152]: (k4_xboole_0(A_150, k2_xboole_0(B_151, k4_xboole_0(A_150, k2_xboole_0(B_151, B_152))))=k3_xboole_0(k4_xboole_0(A_150, B_151), B_152))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_347])).
% 9.53/3.54  tff(c_4798, plain, (![A_13, C_45]: (k4_xboole_0(A_13, k2_xboole_0(k1_xboole_0, k4_xboole_0(A_13, C_45)))=k3_xboole_0(k4_xboole_0(A_13, k1_xboole_0), C_45))), inference(superposition, [status(thm), theory('equality')], [c_387, c_4662])).
% 9.53/3.54  tff(c_16558, plain, (![A_302, C_303]: (k4_xboole_0(A_302, k2_xboole_0(k1_xboole_0, k4_xboole_0(A_302, C_303)))=k3_xboole_0(A_302, C_303))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_4798])).
% 9.53/3.54  tff(c_16863, plain, (![A_47, B_48]: (k4_xboole_0(k3_xboole_0(A_47, B_48), k2_xboole_0(k1_xboole_0, k1_xboole_0))=k3_xboole_0(k3_xboole_0(A_47, B_48), A_47))), inference(superposition, [status(thm), theory('equality')], [c_476, c_16558])).
% 9.53/3.54  tff(c_16980, plain, (![A_47, B_48]: (k3_xboole_0(k3_xboole_0(A_47, B_48), A_47)=k3_xboole_0(A_47, B_48))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_10, c_16863])).
% 9.53/3.54  tff(c_21082, plain, (k3_xboole_0(k1_xboole_0, '#skF_3')=k3_xboole_0('#skF_3', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_21020, c_16980])).
% 9.53/3.54  tff(c_21179, plain, (k3_xboole_0('#skF_1', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_299, c_4, c_21082])).
% 9.53/3.54  tff(c_21181, plain, $false, inference(negUnitSimplification, [status(thm)], [c_123, c_21179])).
% 9.53/3.54  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.53/3.54  
% 9.53/3.54  Inference rules
% 9.53/3.54  ----------------------
% 9.53/3.54  #Ref     : 0
% 9.53/3.54  #Sup     : 5132
% 9.53/3.54  #Fact    : 0
% 9.53/3.54  #Define  : 0
% 9.53/3.54  #Split   : 0
% 9.53/3.54  #Chain   : 0
% 9.53/3.54  #Close   : 0
% 9.53/3.54  
% 9.53/3.54  Ordering : KBO
% 9.53/3.54  
% 9.53/3.54  Simplification rules
% 9.53/3.54  ----------------------
% 9.53/3.54  #Subsume      : 10
% 9.53/3.54  #Demod        : 5822
% 9.53/3.54  #Tautology    : 3998
% 9.53/3.54  #SimpNegUnit  : 1
% 9.53/3.54  #BackRed      : 44
% 9.53/3.54  
% 9.53/3.54  #Partial instantiations: 0
% 9.53/3.54  #Strategies tried      : 1
% 9.53/3.54  
% 9.53/3.54  Timing (in seconds)
% 9.53/3.54  ----------------------
% 9.53/3.54  Preprocessing        : 0.27
% 9.53/3.54  Parsing              : 0.15
% 9.53/3.54  CNF conversion       : 0.02
% 9.53/3.54  Main loop            : 2.50
% 9.53/3.54  Inferencing          : 0.54
% 9.53/3.54  Reduction            : 1.39
% 9.53/3.55  Demodulation         : 1.21
% 9.53/3.55  BG Simplification    : 0.06
% 9.53/3.55  Subsumption          : 0.37
% 9.53/3.55  Abstraction          : 0.08
% 9.53/3.55  MUC search           : 0.00
% 9.53/3.55  Cooper               : 0.00
% 9.53/3.55  Total                : 2.80
% 9.53/3.55  Index Insertion      : 0.00
% 9.53/3.55  Index Deletion       : 0.00
% 9.53/3.55  Index Matching       : 0.00
% 9.53/3.55  BG Taut test         : 0.00
%------------------------------------------------------------------------------
