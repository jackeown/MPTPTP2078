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
% DateTime   : Thu Dec  3 09:43:53 EST 2020

% Result     : Theorem 4.26s
% Output     : CNFRefutation 4.26s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 158 expanded)
%              Number of leaves         :   29 (  64 expanded)
%              Depth                    :   18
%              Number of atoms          :   93 ( 225 expanded)
%              Number of equality atoms :   45 (  94 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_93,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r1_tarski(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,C) )
       => r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_78,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_56,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_70,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_84,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_82,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_80,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_76,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_86,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(c_38,plain,(
    ~ r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),A_3)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_28,plain,(
    ! [A_24] : k4_xboole_0(A_24,k1_xboole_0) = A_24 ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_459,plain,(
    ! [A_71,B_72] :
      ( r2_hidden('#skF_2'(A_71,B_72),B_72)
      | r1_xboole_0(A_71,B_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_40,plain,(
    r1_xboole_0('#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_104,plain,(
    ! [A_43,B_44] :
      ( k3_xboole_0(A_43,B_44) = k1_xboole_0
      | ~ r1_xboole_0(A_43,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_112,plain,(
    k3_xboole_0('#skF_4','#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_40,c_104])).

tff(c_148,plain,(
    ! [A_51,B_52,C_53] :
      ( ~ r1_xboole_0(A_51,B_52)
      | ~ r2_hidden(C_53,k3_xboole_0(A_51,B_52)) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_151,plain,(
    ! [C_53] :
      ( ~ r1_xboole_0('#skF_4','#skF_6')
      | ~ r2_hidden(C_53,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_112,c_148])).

tff(c_153,plain,(
    ! [C_53] : ~ r2_hidden(C_53,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_151])).

tff(c_470,plain,(
    ! [A_73] : r1_xboole_0(A_73,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_459,c_153])).

tff(c_10,plain,(
    ! [A_8,B_9] :
      ( k3_xboole_0(A_8,B_9) = k1_xboole_0
      | ~ r1_xboole_0(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_474,plain,(
    ! [A_73] : k3_xboole_0(A_73,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_470,c_10])).

tff(c_624,plain,(
    ! [A_78,B_79] : k4_xboole_0(A_78,k4_xboole_0(A_78,B_79)) = k3_xboole_0(A_78,B_79) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_662,plain,(
    ! [A_24] : k4_xboole_0(A_24,A_24) = k3_xboole_0(A_24,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_624])).

tff(c_710,plain,(
    ! [A_80] : k4_xboole_0(A_80,A_80) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_474,c_662])).

tff(c_34,plain,(
    ! [A_30,B_31] : k4_xboole_0(A_30,k4_xboole_0(A_30,B_31)) = k3_xboole_0(A_30,B_31) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_715,plain,(
    ! [A_80] : k4_xboole_0(A_80,k1_xboole_0) = k3_xboole_0(A_80,A_80) ),
    inference(superposition,[status(thm),theory(equality)],[c_710,c_34])).

tff(c_739,plain,(
    ! [A_80] : k3_xboole_0(A_80,A_80) = A_80 ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_715])).

tff(c_12,plain,(
    ! [A_8,B_9] :
      ( r1_xboole_0(A_8,B_9)
      | k3_xboole_0(A_8,B_9) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_787,plain,(
    ! [A_81] : k3_xboole_0(A_81,A_81) = A_81 ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_715])).

tff(c_22,plain,(
    ! [A_15,B_16,C_19] :
      ( ~ r1_xboole_0(A_15,B_16)
      | ~ r2_hidden(C_19,k3_xboole_0(A_15,B_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_829,plain,(
    ! [A_82,C_83] :
      ( ~ r1_xboole_0(A_82,A_82)
      | ~ r2_hidden(C_83,A_82) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_787,c_22])).

tff(c_838,plain,(
    ! [C_83,B_9] :
      ( ~ r2_hidden(C_83,B_9)
      | k3_xboole_0(B_9,B_9) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_12,c_829])).

tff(c_854,plain,(
    ! [C_87,B_88] :
      ( ~ r2_hidden(C_87,B_88)
      | k1_xboole_0 != B_88 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_739,c_838])).

tff(c_914,plain,(
    ! [A_93,B_94] :
      ( k1_xboole_0 != A_93
      | r1_tarski(A_93,B_94) ) ),
    inference(resolution,[status(thm)],[c_8,c_854])).

tff(c_24,plain,(
    ! [A_20,B_21] :
      ( k2_xboole_0(A_20,B_21) = B_21
      | ~ r1_tarski(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_964,plain,(
    ! [A_97,B_98] :
      ( k2_xboole_0(A_97,B_98) = B_98
      | k1_xboole_0 != A_97 ) ),
    inference(resolution,[status(thm)],[c_914,c_24])).

tff(c_1133,plain,(
    ! [A_1] : k2_xboole_0(A_1,k1_xboole_0) = A_1 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_964])).

tff(c_130,plain,(
    ! [A_47,B_48] : k4_xboole_0(A_47,k3_xboole_0(A_47,B_48)) = k4_xboole_0(A_47,B_48) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_139,plain,(
    k4_xboole_0('#skF_4',k1_xboole_0) = k4_xboole_0('#skF_4','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_112,c_130])).

tff(c_142,plain,(
    k4_xboole_0('#skF_4','#skF_6') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_139])).

tff(c_1377,plain,(
    ! [A_112,B_113,C_114] : k4_xboole_0(k4_xboole_0(A_112,B_113),C_114) = k4_xboole_0(A_112,k2_xboole_0(B_113,C_114)) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_3377,plain,(
    ! [C_177] : k4_xboole_0('#skF_4',k2_xboole_0('#skF_6',C_177)) = k4_xboole_0('#skF_4',C_177) ),
    inference(superposition,[status(thm),theory(equality)],[c_142,c_1377])).

tff(c_42,plain,(
    r1_tarski('#skF_4',k2_xboole_0('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_43,plain,(
    r1_tarski('#skF_4',k2_xboole_0('#skF_6','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_42])).

tff(c_117,plain,(
    ! [A_45,B_46] :
      ( k2_xboole_0(A_45,B_46) = B_46
      | ~ r1_tarski(A_45,B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_129,plain,(
    k2_xboole_0('#skF_4',k2_xboole_0('#skF_6','#skF_5')) = k2_xboole_0('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_43,c_117])).

tff(c_26,plain,(
    ! [A_22,B_23] : k2_xboole_0(A_22,k4_xboole_0(B_23,A_22)) = k2_xboole_0(A_22,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_674,plain,(
    ! [A_24] : k4_xboole_0(A_24,A_24) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_474,c_662])).

tff(c_1393,plain,(
    ! [A_112,B_113] : k4_xboole_0(A_112,k2_xboole_0(B_113,k4_xboole_0(A_112,B_113))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1377,c_674])).

tff(c_1467,plain,(
    ! [A_115,B_116] : k4_xboole_0(A_115,k2_xboole_0(B_116,A_115)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_1393])).

tff(c_1543,plain,(
    ! [B_117,A_118] : k4_xboole_0(B_117,k2_xboole_0(B_117,A_118)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1467])).

tff(c_1607,plain,(
    k4_xboole_0('#skF_4',k2_xboole_0('#skF_6','#skF_5')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_129,c_1543])).

tff(c_3398,plain,(
    k4_xboole_0('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_3377,c_1607])).

tff(c_3524,plain,(
    k2_xboole_0('#skF_5',k1_xboole_0) = k2_xboole_0('#skF_5','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3398,c_26])).

tff(c_3545,plain,(
    k2_xboole_0('#skF_4','#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1133,c_2,c_3524])).

tff(c_36,plain,(
    ! [A_32,B_33] : r1_tarski(A_32,k2_xboole_0(A_32,B_33)) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_3656,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_3545,c_36])).

tff(c_3680,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_3656])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n006.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:42:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.26/1.78  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.26/1.78  
% 4.26/1.78  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.26/1.78  %$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2 > #skF_1
% 4.26/1.78  
% 4.26/1.78  %Foreground sorts:
% 4.26/1.78  
% 4.26/1.78  
% 4.26/1.78  %Background operators:
% 4.26/1.78  
% 4.26/1.78  
% 4.26/1.78  %Foreground operators:
% 4.26/1.78  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.26/1.78  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.26/1.78  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.26/1.78  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.26/1.78  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.26/1.78  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.26/1.78  tff('#skF_5', type, '#skF_5': $i).
% 4.26/1.78  tff('#skF_6', type, '#skF_6': $i).
% 4.26/1.78  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.26/1.78  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.26/1.78  tff('#skF_4', type, '#skF_4': $i).
% 4.26/1.78  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.26/1.78  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.26/1.78  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.26/1.78  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.26/1.78  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.26/1.78  
% 4.26/1.80  tff(f_93, negated_conjecture, ~(![A, B, C]: ((r1_tarski(A, k2_xboole_0(B, C)) & r1_xboole_0(A, C)) => r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_xboole_1)).
% 4.26/1.80  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 4.26/1.80  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 4.26/1.80  tff(f_78, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 4.26/1.80  tff(f_56, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 4.26/1.80  tff(f_38, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 4.26/1.80  tff(f_70, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 4.26/1.80  tff(f_84, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 4.26/1.80  tff(f_74, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 4.26/1.80  tff(f_82, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 4.26/1.80  tff(f_80, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 4.26/1.80  tff(f_76, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 4.26/1.80  tff(f_86, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 4.26/1.80  tff(c_38, plain, (~r1_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_93])).
% 4.26/1.80  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.26/1.80  tff(c_8, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), A_3) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.26/1.80  tff(c_28, plain, (![A_24]: (k4_xboole_0(A_24, k1_xboole_0)=A_24)), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.26/1.80  tff(c_459, plain, (![A_71, B_72]: (r2_hidden('#skF_2'(A_71, B_72), B_72) | r1_xboole_0(A_71, B_72))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.26/1.80  tff(c_40, plain, (r1_xboole_0('#skF_4', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_93])).
% 4.26/1.80  tff(c_104, plain, (![A_43, B_44]: (k3_xboole_0(A_43, B_44)=k1_xboole_0 | ~r1_xboole_0(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.26/1.80  tff(c_112, plain, (k3_xboole_0('#skF_4', '#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_40, c_104])).
% 4.26/1.80  tff(c_148, plain, (![A_51, B_52, C_53]: (~r1_xboole_0(A_51, B_52) | ~r2_hidden(C_53, k3_xboole_0(A_51, B_52)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.26/1.80  tff(c_151, plain, (![C_53]: (~r1_xboole_0('#skF_4', '#skF_6') | ~r2_hidden(C_53, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_112, c_148])).
% 4.26/1.80  tff(c_153, plain, (![C_53]: (~r2_hidden(C_53, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_151])).
% 4.26/1.80  tff(c_470, plain, (![A_73]: (r1_xboole_0(A_73, k1_xboole_0))), inference(resolution, [status(thm)], [c_459, c_153])).
% 4.26/1.80  tff(c_10, plain, (![A_8, B_9]: (k3_xboole_0(A_8, B_9)=k1_xboole_0 | ~r1_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.26/1.80  tff(c_474, plain, (![A_73]: (k3_xboole_0(A_73, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_470, c_10])).
% 4.26/1.80  tff(c_624, plain, (![A_78, B_79]: (k4_xboole_0(A_78, k4_xboole_0(A_78, B_79))=k3_xboole_0(A_78, B_79))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.26/1.80  tff(c_662, plain, (![A_24]: (k4_xboole_0(A_24, A_24)=k3_xboole_0(A_24, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_28, c_624])).
% 4.26/1.80  tff(c_710, plain, (![A_80]: (k4_xboole_0(A_80, A_80)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_474, c_662])).
% 4.26/1.80  tff(c_34, plain, (![A_30, B_31]: (k4_xboole_0(A_30, k4_xboole_0(A_30, B_31))=k3_xboole_0(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.26/1.80  tff(c_715, plain, (![A_80]: (k4_xboole_0(A_80, k1_xboole_0)=k3_xboole_0(A_80, A_80))), inference(superposition, [status(thm), theory('equality')], [c_710, c_34])).
% 4.26/1.80  tff(c_739, plain, (![A_80]: (k3_xboole_0(A_80, A_80)=A_80)), inference(demodulation, [status(thm), theory('equality')], [c_28, c_715])).
% 4.26/1.80  tff(c_12, plain, (![A_8, B_9]: (r1_xboole_0(A_8, B_9) | k3_xboole_0(A_8, B_9)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.26/1.80  tff(c_787, plain, (![A_81]: (k3_xboole_0(A_81, A_81)=A_81)), inference(demodulation, [status(thm), theory('equality')], [c_28, c_715])).
% 4.26/1.80  tff(c_22, plain, (![A_15, B_16, C_19]: (~r1_xboole_0(A_15, B_16) | ~r2_hidden(C_19, k3_xboole_0(A_15, B_16)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.26/1.80  tff(c_829, plain, (![A_82, C_83]: (~r1_xboole_0(A_82, A_82) | ~r2_hidden(C_83, A_82))), inference(superposition, [status(thm), theory('equality')], [c_787, c_22])).
% 4.26/1.80  tff(c_838, plain, (![C_83, B_9]: (~r2_hidden(C_83, B_9) | k3_xboole_0(B_9, B_9)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_829])).
% 4.26/1.80  tff(c_854, plain, (![C_87, B_88]: (~r2_hidden(C_87, B_88) | k1_xboole_0!=B_88)), inference(demodulation, [status(thm), theory('equality')], [c_739, c_838])).
% 4.26/1.80  tff(c_914, plain, (![A_93, B_94]: (k1_xboole_0!=A_93 | r1_tarski(A_93, B_94))), inference(resolution, [status(thm)], [c_8, c_854])).
% 4.26/1.80  tff(c_24, plain, (![A_20, B_21]: (k2_xboole_0(A_20, B_21)=B_21 | ~r1_tarski(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.26/1.80  tff(c_964, plain, (![A_97, B_98]: (k2_xboole_0(A_97, B_98)=B_98 | k1_xboole_0!=A_97)), inference(resolution, [status(thm)], [c_914, c_24])).
% 4.26/1.80  tff(c_1133, plain, (![A_1]: (k2_xboole_0(A_1, k1_xboole_0)=A_1)), inference(superposition, [status(thm), theory('equality')], [c_2, c_964])).
% 4.26/1.80  tff(c_130, plain, (![A_47, B_48]: (k4_xboole_0(A_47, k3_xboole_0(A_47, B_48))=k4_xboole_0(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.26/1.80  tff(c_139, plain, (k4_xboole_0('#skF_4', k1_xboole_0)=k4_xboole_0('#skF_4', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_112, c_130])).
% 4.26/1.80  tff(c_142, plain, (k4_xboole_0('#skF_4', '#skF_6')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_28, c_139])).
% 4.26/1.80  tff(c_1377, plain, (![A_112, B_113, C_114]: (k4_xboole_0(k4_xboole_0(A_112, B_113), C_114)=k4_xboole_0(A_112, k2_xboole_0(B_113, C_114)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.26/1.80  tff(c_3377, plain, (![C_177]: (k4_xboole_0('#skF_4', k2_xboole_0('#skF_6', C_177))=k4_xboole_0('#skF_4', C_177))), inference(superposition, [status(thm), theory('equality')], [c_142, c_1377])).
% 4.26/1.80  tff(c_42, plain, (r1_tarski('#skF_4', k2_xboole_0('#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_93])).
% 4.26/1.80  tff(c_43, plain, (r1_tarski('#skF_4', k2_xboole_0('#skF_6', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_42])).
% 4.26/1.80  tff(c_117, plain, (![A_45, B_46]: (k2_xboole_0(A_45, B_46)=B_46 | ~r1_tarski(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.26/1.80  tff(c_129, plain, (k2_xboole_0('#skF_4', k2_xboole_0('#skF_6', '#skF_5'))=k2_xboole_0('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_43, c_117])).
% 4.26/1.80  tff(c_26, plain, (![A_22, B_23]: (k2_xboole_0(A_22, k4_xboole_0(B_23, A_22))=k2_xboole_0(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.26/1.80  tff(c_674, plain, (![A_24]: (k4_xboole_0(A_24, A_24)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_474, c_662])).
% 4.26/1.80  tff(c_1393, plain, (![A_112, B_113]: (k4_xboole_0(A_112, k2_xboole_0(B_113, k4_xboole_0(A_112, B_113)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1377, c_674])).
% 4.26/1.80  tff(c_1467, plain, (![A_115, B_116]: (k4_xboole_0(A_115, k2_xboole_0(B_116, A_115))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_26, c_1393])).
% 4.26/1.80  tff(c_1543, plain, (![B_117, A_118]: (k4_xboole_0(B_117, k2_xboole_0(B_117, A_118))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_1467])).
% 4.26/1.80  tff(c_1607, plain, (k4_xboole_0('#skF_4', k2_xboole_0('#skF_6', '#skF_5'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_129, c_1543])).
% 4.26/1.80  tff(c_3398, plain, (k4_xboole_0('#skF_4', '#skF_5')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_3377, c_1607])).
% 4.26/1.80  tff(c_3524, plain, (k2_xboole_0('#skF_5', k1_xboole_0)=k2_xboole_0('#skF_5', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3398, c_26])).
% 4.26/1.80  tff(c_3545, plain, (k2_xboole_0('#skF_4', '#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_1133, c_2, c_3524])).
% 4.26/1.80  tff(c_36, plain, (![A_32, B_33]: (r1_tarski(A_32, k2_xboole_0(A_32, B_33)))), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.26/1.80  tff(c_3656, plain, (r1_tarski('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_3545, c_36])).
% 4.26/1.80  tff(c_3680, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_3656])).
% 4.26/1.80  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.26/1.80  
% 4.26/1.80  Inference rules
% 4.26/1.80  ----------------------
% 4.26/1.80  #Ref     : 1
% 4.26/1.80  #Sup     : 939
% 4.26/1.80  #Fact    : 0
% 4.26/1.80  #Define  : 0
% 4.26/1.80  #Split   : 2
% 4.26/1.80  #Chain   : 0
% 4.26/1.80  #Close   : 0
% 4.26/1.80  
% 4.26/1.80  Ordering : KBO
% 4.26/1.80  
% 4.26/1.80  Simplification rules
% 4.26/1.80  ----------------------
% 4.26/1.80  #Subsume      : 218
% 4.26/1.80  #Demod        : 524
% 4.26/1.80  #Tautology    : 486
% 4.26/1.80  #SimpNegUnit  : 38
% 4.26/1.80  #BackRed      : 3
% 4.26/1.80  
% 4.26/1.80  #Partial instantiations: 0
% 4.26/1.80  #Strategies tried      : 1
% 4.26/1.80  
% 4.26/1.80  Timing (in seconds)
% 4.26/1.80  ----------------------
% 4.26/1.80  Preprocessing        : 0.28
% 4.26/1.80  Parsing              : 0.16
% 4.26/1.80  CNF conversion       : 0.02
% 4.26/1.80  Main loop            : 0.72
% 4.26/1.80  Inferencing          : 0.23
% 4.26/1.81  Reduction            : 0.32
% 4.26/1.81  Demodulation         : 0.26
% 4.26/1.81  BG Simplification    : 0.03
% 4.26/1.81  Subsumption          : 0.11
% 4.26/1.81  Abstraction          : 0.03
% 4.26/1.81  MUC search           : 0.00
% 4.26/1.81  Cooper               : 0.00
% 4.26/1.81  Total                : 1.04
% 4.26/1.81  Index Insertion      : 0.00
% 4.26/1.81  Index Deletion       : 0.00
% 4.26/1.81  Index Matching       : 0.00
% 4.26/1.81  BG Taut test         : 0.00
%------------------------------------------------------------------------------
