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
% DateTime   : Thu Dec  3 09:43:54 EST 2020

% Result     : Theorem 4.38s
% Output     : CNFRefutation 4.47s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 148 expanded)
%              Number of leaves         :   22 (  59 expanded)
%              Depth                    :   13
%              Number of atoms          :   66 ( 156 expanded)
%              Number of equality atoms :   48 ( 116 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

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

tff(f_35,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_54,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r1_tarski(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,C) )
       => r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_xboole_1)).

tff(f_39,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_41,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_47,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_43,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(c_103,plain,(
    ! [A_30,B_31] :
      ( r1_tarski(A_30,B_31)
      | k4_xboole_0(A_30,B_31) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_24,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_107,plain,(
    k4_xboole_0('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_103,c_24])).

tff(c_14,plain,(
    ! [A_9] : k4_xboole_0(A_9,k1_xboole_0) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_241,plain,(
    ! [A_43,B_44] : k4_xboole_0(k2_xboole_0(A_43,B_44),B_44) = k4_xboole_0(A_43,B_44) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_251,plain,(
    ! [A_43] : k4_xboole_0(A_43,k1_xboole_0) = k2_xboole_0(A_43,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_241,c_14])).

tff(c_269,plain,(
    ! [A_45] : k2_xboole_0(A_45,k1_xboole_0) = A_45 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_251])).

tff(c_40,plain,(
    ! [B_22,A_23] : k2_xboole_0(B_22,A_23) = k2_xboole_0(A_23,B_22) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_22,plain,(
    ! [A_17,B_18] : r1_tarski(A_17,k2_xboole_0(A_17,B_18)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_55,plain,(
    ! [A_23,B_22] : r1_tarski(A_23,k2_xboole_0(B_22,A_23)) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_22])).

tff(c_311,plain,(
    ! [A_46] : r1_tarski(k1_xboole_0,A_46) ),
    inference(superposition,[status(thm),theory(equality)],[c_269,c_55])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( k4_xboole_0(A_5,B_6) = k1_xboole_0
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_315,plain,(
    ! [A_46] : k4_xboole_0(k1_xboole_0,A_46) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_311,c_10])).

tff(c_26,plain,(
    r1_xboole_0('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_89,plain,(
    ! [A_26,B_27] :
      ( k3_xboole_0(A_26,B_27) = k1_xboole_0
      | ~ r1_xboole_0(A_26,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_93,plain,(
    k3_xboole_0('#skF_1','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_26,c_89])).

tff(c_266,plain,(
    ! [A_43] : k2_xboole_0(A_43,k1_xboole_0) = A_43 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_251])).

tff(c_16,plain,(
    ! [A_10,B_11] : k4_xboole_0(k2_xboole_0(A_10,B_11),B_11) = k4_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_108,plain,(
    ! [A_32,B_33] :
      ( k4_xboole_0(A_32,B_33) = k1_xboole_0
      | ~ r1_tarski(A_32,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_125,plain,(
    ! [A_34,B_35] : k4_xboole_0(A_34,k2_xboole_0(A_34,B_35)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_22,c_108])).

tff(c_135,plain,(
    ! [B_2,A_1] : k4_xboole_0(B_2,k2_xboole_0(A_1,B_2)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_125])).

tff(c_12,plain,(
    ! [A_7,B_8] : k2_xboole_0(A_7,k4_xboole_0(B_8,A_7)) = k2_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_321,plain,(
    ! [A_48,B_49] : k2_xboole_0(A_48,k4_xboole_0(B_49,A_48)) = k2_xboole_0(A_48,B_49) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_348,plain,(
    ! [B_11,A_10] : k2_xboole_0(B_11,k4_xboole_0(A_10,B_11)) = k2_xboole_0(B_11,k2_xboole_0(A_10,B_11)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_321])).

tff(c_1027,plain,(
    ! [B_66,A_67] : k2_xboole_0(B_66,k2_xboole_0(A_67,B_66)) = k2_xboole_0(B_66,A_67) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_348])).

tff(c_1050,plain,(
    ! [B_66,A_67] : k4_xboole_0(k2_xboole_0(B_66,A_67),k2_xboole_0(A_67,B_66)) = k4_xboole_0(B_66,k2_xboole_0(A_67,B_66)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1027,c_16])).

tff(c_1102,plain,(
    ! [B_66,A_67] : k4_xboole_0(k2_xboole_0(B_66,A_67),k2_xboole_0(A_67,B_66)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_1050])).

tff(c_450,plain,(
    ! [A_51,B_52,C_53] : k4_xboole_0(k4_xboole_0(A_51,B_52),C_53) = k4_xboole_0(A_51,k2_xboole_0(B_52,C_53)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2648,plain,(
    ! [C_95,A_96,B_97] : k2_xboole_0(C_95,k4_xboole_0(A_96,k2_xboole_0(B_97,C_95))) = k2_xboole_0(C_95,k4_xboole_0(A_96,B_97)) ),
    inference(superposition,[status(thm),theory(equality)],[c_450,c_12])).

tff(c_2748,plain,(
    ! [B_66,A_67] : k2_xboole_0(B_66,k4_xboole_0(k2_xboole_0(B_66,A_67),A_67)) = k2_xboole_0(B_66,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1102,c_2648])).

tff(c_2838,plain,(
    ! [B_66,A_67] : k2_xboole_0(B_66,k4_xboole_0(B_66,A_67)) = B_66 ),
    inference(demodulation,[status(thm),theory(equality)],[c_266,c_16,c_2748])).

tff(c_20,plain,(
    ! [A_15,B_16] : k4_xboole_0(A_15,k4_xboole_0(A_15,B_16)) = k3_xboole_0(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_360,plain,(
    ! [A_15,B_16] : k2_xboole_0(k4_xboole_0(A_15,B_16),k3_xboole_0(A_15,B_16)) = k2_xboole_0(k4_xboole_0(A_15,B_16),A_15) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_321])).

tff(c_375,plain,(
    ! [A_15,B_16] : k2_xboole_0(k4_xboole_0(A_15,B_16),k3_xboole_0(A_15,B_16)) = k2_xboole_0(A_15,k4_xboole_0(A_15,B_16)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_360])).

tff(c_3957,plain,(
    ! [A_112,B_113] : k2_xboole_0(k4_xboole_0(A_112,B_113),k3_xboole_0(A_112,B_113)) = A_112 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2838,c_375])).

tff(c_4128,plain,(
    k2_xboole_0(k4_xboole_0('#skF_1','#skF_3'),k1_xboole_0) = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_93,c_3957])).

tff(c_327,plain,(
    ! [A_48,B_49] : k4_xboole_0(k2_xboole_0(A_48,B_49),k4_xboole_0(B_49,A_48)) = k4_xboole_0(A_48,k4_xboole_0(B_49,A_48)) ),
    inference(superposition,[status(thm),theory(equality)],[c_321,c_16])).

tff(c_4185,plain,(
    k4_xboole_0(k4_xboole_0('#skF_1','#skF_3'),k4_xboole_0(k1_xboole_0,k4_xboole_0('#skF_1','#skF_3'))) = k4_xboole_0('#skF_1',k4_xboole_0(k1_xboole_0,k4_xboole_0('#skF_1','#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_4128,c_327])).

tff(c_4264,plain,(
    k4_xboole_0('#skF_1','#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_315,c_14,c_315,c_4185])).

tff(c_28,plain,(
    r1_tarski('#skF_1',k2_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_29,plain,(
    r1_tarski('#skF_1',k2_xboole_0('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_28])).

tff(c_124,plain,(
    k4_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_29,c_108])).

tff(c_2805,plain,(
    k2_xboole_0('#skF_2',k4_xboole_0('#skF_1','#skF_3')) = k2_xboole_0('#skF_2',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_124,c_2648])).

tff(c_2853,plain,(
    k2_xboole_0('#skF_2',k4_xboole_0('#skF_1','#skF_3')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_266,c_2805])).

tff(c_2909,plain,(
    k4_xboole_0(k4_xboole_0('#skF_1','#skF_3'),'#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2853,c_135])).

tff(c_4284,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4264,c_2909])).

tff(c_4290,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_107,c_4284])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n006.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 12:07:07 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.38/1.79  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.38/1.80  
% 4.38/1.80  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.38/1.80  %$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 4.38/1.80  
% 4.38/1.80  %Foreground sorts:
% 4.38/1.80  
% 4.38/1.80  
% 4.38/1.80  %Background operators:
% 4.38/1.80  
% 4.38/1.80  
% 4.38/1.80  %Foreground operators:
% 4.38/1.80  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.38/1.80  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.38/1.80  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.38/1.80  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.38/1.80  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.38/1.80  tff('#skF_2', type, '#skF_2': $i).
% 4.38/1.80  tff('#skF_3', type, '#skF_3': $i).
% 4.38/1.80  tff('#skF_1', type, '#skF_1': $i).
% 4.38/1.80  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.38/1.80  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.38/1.80  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.38/1.80  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.38/1.80  
% 4.47/1.82  tff(f_35, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 4.47/1.82  tff(f_54, negated_conjecture, ~(![A, B, C]: ((r1_tarski(A, k2_xboole_0(B, C)) & r1_xboole_0(A, C)) => r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_xboole_1)).
% 4.47/1.82  tff(f_39, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 4.47/1.82  tff(f_41, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_xboole_1)).
% 4.47/1.82  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 4.47/1.82  tff(f_47, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 4.47/1.82  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 4.47/1.82  tff(f_37, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 4.47/1.82  tff(f_43, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 4.47/1.82  tff(f_45, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 4.47/1.82  tff(c_103, plain, (![A_30, B_31]: (r1_tarski(A_30, B_31) | k4_xboole_0(A_30, B_31)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.47/1.82  tff(c_24, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.47/1.82  tff(c_107, plain, (k4_xboole_0('#skF_1', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_103, c_24])).
% 4.47/1.82  tff(c_14, plain, (![A_9]: (k4_xboole_0(A_9, k1_xboole_0)=A_9)), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.47/1.82  tff(c_241, plain, (![A_43, B_44]: (k4_xboole_0(k2_xboole_0(A_43, B_44), B_44)=k4_xboole_0(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.47/1.82  tff(c_251, plain, (![A_43]: (k4_xboole_0(A_43, k1_xboole_0)=k2_xboole_0(A_43, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_241, c_14])).
% 4.47/1.82  tff(c_269, plain, (![A_45]: (k2_xboole_0(A_45, k1_xboole_0)=A_45)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_251])).
% 4.47/1.82  tff(c_40, plain, (![B_22, A_23]: (k2_xboole_0(B_22, A_23)=k2_xboole_0(A_23, B_22))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.47/1.82  tff(c_22, plain, (![A_17, B_18]: (r1_tarski(A_17, k2_xboole_0(A_17, B_18)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.47/1.82  tff(c_55, plain, (![A_23, B_22]: (r1_tarski(A_23, k2_xboole_0(B_22, A_23)))), inference(superposition, [status(thm), theory('equality')], [c_40, c_22])).
% 4.47/1.82  tff(c_311, plain, (![A_46]: (r1_tarski(k1_xboole_0, A_46))), inference(superposition, [status(thm), theory('equality')], [c_269, c_55])).
% 4.47/1.82  tff(c_10, plain, (![A_5, B_6]: (k4_xboole_0(A_5, B_6)=k1_xboole_0 | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.47/1.82  tff(c_315, plain, (![A_46]: (k4_xboole_0(k1_xboole_0, A_46)=k1_xboole_0)), inference(resolution, [status(thm)], [c_311, c_10])).
% 4.47/1.82  tff(c_26, plain, (r1_xboole_0('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.47/1.82  tff(c_89, plain, (![A_26, B_27]: (k3_xboole_0(A_26, B_27)=k1_xboole_0 | ~r1_xboole_0(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.47/1.82  tff(c_93, plain, (k3_xboole_0('#skF_1', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_26, c_89])).
% 4.47/1.82  tff(c_266, plain, (![A_43]: (k2_xboole_0(A_43, k1_xboole_0)=A_43)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_251])).
% 4.47/1.82  tff(c_16, plain, (![A_10, B_11]: (k4_xboole_0(k2_xboole_0(A_10, B_11), B_11)=k4_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.47/1.82  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.47/1.82  tff(c_108, plain, (![A_32, B_33]: (k4_xboole_0(A_32, B_33)=k1_xboole_0 | ~r1_tarski(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.47/1.82  tff(c_125, plain, (![A_34, B_35]: (k4_xboole_0(A_34, k2_xboole_0(A_34, B_35))=k1_xboole_0)), inference(resolution, [status(thm)], [c_22, c_108])).
% 4.47/1.82  tff(c_135, plain, (![B_2, A_1]: (k4_xboole_0(B_2, k2_xboole_0(A_1, B_2))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_125])).
% 4.47/1.82  tff(c_12, plain, (![A_7, B_8]: (k2_xboole_0(A_7, k4_xboole_0(B_8, A_7))=k2_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.47/1.82  tff(c_321, plain, (![A_48, B_49]: (k2_xboole_0(A_48, k4_xboole_0(B_49, A_48))=k2_xboole_0(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.47/1.82  tff(c_348, plain, (![B_11, A_10]: (k2_xboole_0(B_11, k4_xboole_0(A_10, B_11))=k2_xboole_0(B_11, k2_xboole_0(A_10, B_11)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_321])).
% 4.47/1.82  tff(c_1027, plain, (![B_66, A_67]: (k2_xboole_0(B_66, k2_xboole_0(A_67, B_66))=k2_xboole_0(B_66, A_67))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_348])).
% 4.47/1.82  tff(c_1050, plain, (![B_66, A_67]: (k4_xboole_0(k2_xboole_0(B_66, A_67), k2_xboole_0(A_67, B_66))=k4_xboole_0(B_66, k2_xboole_0(A_67, B_66)))), inference(superposition, [status(thm), theory('equality')], [c_1027, c_16])).
% 4.47/1.82  tff(c_1102, plain, (![B_66, A_67]: (k4_xboole_0(k2_xboole_0(B_66, A_67), k2_xboole_0(A_67, B_66))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_135, c_1050])).
% 4.47/1.82  tff(c_450, plain, (![A_51, B_52, C_53]: (k4_xboole_0(k4_xboole_0(A_51, B_52), C_53)=k4_xboole_0(A_51, k2_xboole_0(B_52, C_53)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.47/1.82  tff(c_2648, plain, (![C_95, A_96, B_97]: (k2_xboole_0(C_95, k4_xboole_0(A_96, k2_xboole_0(B_97, C_95)))=k2_xboole_0(C_95, k4_xboole_0(A_96, B_97)))), inference(superposition, [status(thm), theory('equality')], [c_450, c_12])).
% 4.47/1.82  tff(c_2748, plain, (![B_66, A_67]: (k2_xboole_0(B_66, k4_xboole_0(k2_xboole_0(B_66, A_67), A_67))=k2_xboole_0(B_66, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1102, c_2648])).
% 4.47/1.82  tff(c_2838, plain, (![B_66, A_67]: (k2_xboole_0(B_66, k4_xboole_0(B_66, A_67))=B_66)), inference(demodulation, [status(thm), theory('equality')], [c_266, c_16, c_2748])).
% 4.47/1.82  tff(c_20, plain, (![A_15, B_16]: (k4_xboole_0(A_15, k4_xboole_0(A_15, B_16))=k3_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.47/1.82  tff(c_360, plain, (![A_15, B_16]: (k2_xboole_0(k4_xboole_0(A_15, B_16), k3_xboole_0(A_15, B_16))=k2_xboole_0(k4_xboole_0(A_15, B_16), A_15))), inference(superposition, [status(thm), theory('equality')], [c_20, c_321])).
% 4.47/1.82  tff(c_375, plain, (![A_15, B_16]: (k2_xboole_0(k4_xboole_0(A_15, B_16), k3_xboole_0(A_15, B_16))=k2_xboole_0(A_15, k4_xboole_0(A_15, B_16)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_360])).
% 4.47/1.82  tff(c_3957, plain, (![A_112, B_113]: (k2_xboole_0(k4_xboole_0(A_112, B_113), k3_xboole_0(A_112, B_113))=A_112)), inference(demodulation, [status(thm), theory('equality')], [c_2838, c_375])).
% 4.47/1.82  tff(c_4128, plain, (k2_xboole_0(k4_xboole_0('#skF_1', '#skF_3'), k1_xboole_0)='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_93, c_3957])).
% 4.47/1.82  tff(c_327, plain, (![A_48, B_49]: (k4_xboole_0(k2_xboole_0(A_48, B_49), k4_xboole_0(B_49, A_48))=k4_xboole_0(A_48, k4_xboole_0(B_49, A_48)))), inference(superposition, [status(thm), theory('equality')], [c_321, c_16])).
% 4.47/1.82  tff(c_4185, plain, (k4_xboole_0(k4_xboole_0('#skF_1', '#skF_3'), k4_xboole_0(k1_xboole_0, k4_xboole_0('#skF_1', '#skF_3')))=k4_xboole_0('#skF_1', k4_xboole_0(k1_xboole_0, k4_xboole_0('#skF_1', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_4128, c_327])).
% 4.47/1.82  tff(c_4264, plain, (k4_xboole_0('#skF_1', '#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_14, c_315, c_14, c_315, c_4185])).
% 4.47/1.82  tff(c_28, plain, (r1_tarski('#skF_1', k2_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.47/1.82  tff(c_29, plain, (r1_tarski('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_28])).
% 4.47/1.82  tff(c_124, plain, (k4_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))=k1_xboole_0), inference(resolution, [status(thm)], [c_29, c_108])).
% 4.47/1.82  tff(c_2805, plain, (k2_xboole_0('#skF_2', k4_xboole_0('#skF_1', '#skF_3'))=k2_xboole_0('#skF_2', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_124, c_2648])).
% 4.47/1.82  tff(c_2853, plain, (k2_xboole_0('#skF_2', k4_xboole_0('#skF_1', '#skF_3'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_266, c_2805])).
% 4.47/1.82  tff(c_2909, plain, (k4_xboole_0(k4_xboole_0('#skF_1', '#skF_3'), '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_2853, c_135])).
% 4.47/1.82  tff(c_4284, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_4264, c_2909])).
% 4.47/1.82  tff(c_4290, plain, $false, inference(negUnitSimplification, [status(thm)], [c_107, c_4284])).
% 4.47/1.82  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.47/1.82  
% 4.47/1.82  Inference rules
% 4.47/1.82  ----------------------
% 4.47/1.82  #Ref     : 0
% 4.47/1.82  #Sup     : 1060
% 4.47/1.82  #Fact    : 0
% 4.47/1.82  #Define  : 0
% 4.47/1.82  #Split   : 0
% 4.47/1.82  #Chain   : 0
% 4.47/1.82  #Close   : 0
% 4.47/1.82  
% 4.47/1.82  Ordering : KBO
% 4.47/1.82  
% 4.47/1.82  Simplification rules
% 4.47/1.82  ----------------------
% 4.47/1.82  #Subsume      : 1
% 4.47/1.82  #Demod        : 1392
% 4.47/1.82  #Tautology    : 782
% 4.47/1.82  #SimpNegUnit  : 1
% 4.47/1.82  #BackRed      : 8
% 4.47/1.82  
% 4.47/1.82  #Partial instantiations: 0
% 4.47/1.82  #Strategies tried      : 1
% 4.47/1.82  
% 4.47/1.82  Timing (in seconds)
% 4.47/1.82  ----------------------
% 4.49/1.82  Preprocessing        : 0.27
% 4.49/1.82  Parsing              : 0.15
% 4.49/1.82  CNF conversion       : 0.02
% 4.49/1.82  Main loop            : 0.79
% 4.49/1.82  Inferencing          : 0.22
% 4.49/1.82  Reduction            : 0.40
% 4.49/1.82  Demodulation         : 0.34
% 4.49/1.82  BG Simplification    : 0.03
% 4.49/1.82  Subsumption          : 0.10
% 4.49/1.82  Abstraction          : 0.04
% 4.49/1.82  MUC search           : 0.00
% 4.49/1.82  Cooper               : 0.00
% 4.49/1.82  Total                : 1.09
% 4.49/1.82  Index Insertion      : 0.00
% 4.49/1.82  Index Deletion       : 0.00
% 4.49/1.82  Index Matching       : 0.00
% 4.49/1.82  BG Taut test         : 0.00
%------------------------------------------------------------------------------
