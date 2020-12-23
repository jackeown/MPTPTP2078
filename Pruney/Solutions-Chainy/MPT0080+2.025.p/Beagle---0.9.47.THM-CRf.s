%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:52 EST 2020

% Result     : Theorem 4.50s
% Output     : CNFRefutation 4.66s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 134 expanded)
%              Number of leaves         :   28 (  55 expanded)
%              Depth                    :   14
%              Number of atoms          :   83 ( 151 expanded)
%              Number of equality atoms :   50 ( 100 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(f_81,negated_conjecture,(
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

tff(f_66,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_62,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_72,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_56,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_60,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_70,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_68,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_74,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_64,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(c_36,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),A_3)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_26,plain,(
    ! [A_22] : k4_xboole_0(A_22,k1_xboole_0) = A_22 ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_22,plain,(
    ! [A_19] : k3_xboole_0(A_19,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_161,plain,(
    ! [A_50,B_51] : k4_xboole_0(A_50,k4_xboole_0(A_50,B_51)) = k3_xboole_0(A_50,B_51) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_176,plain,(
    ! [A_22] : k4_xboole_0(A_22,A_22) = k3_xboole_0(A_22,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_161])).

tff(c_180,plain,(
    ! [A_52] : k4_xboole_0(A_52,A_52) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_176])).

tff(c_32,plain,(
    ! [A_28,B_29] : k4_xboole_0(A_28,k4_xboole_0(A_28,B_29)) = k3_xboole_0(A_28,B_29) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_185,plain,(
    ! [A_52] : k4_xboole_0(A_52,k1_xboole_0) = k3_xboole_0(A_52,A_52) ),
    inference(superposition,[status(thm),theory(equality)],[c_180,c_32])).

tff(c_197,plain,(
    ! [A_52] : k3_xboole_0(A_52,A_52) = A_52 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_185])).

tff(c_12,plain,(
    ! [A_8,B_9] :
      ( r1_xboole_0(A_8,B_9)
      | k3_xboole_0(A_8,B_9) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_307,plain,(
    ! [A_59,B_60,C_61] :
      ( ~ r1_xboole_0(A_59,B_60)
      | ~ r2_hidden(C_61,k3_xboole_0(A_59,B_60)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_561,plain,(
    ! [A_72,C_73] :
      ( ~ r1_xboole_0(A_72,A_72)
      | ~ r2_hidden(C_73,A_72) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_197,c_307])).

tff(c_567,plain,(
    ! [C_73,B_9] :
      ( ~ r2_hidden(C_73,B_9)
      | k3_xboole_0(B_9,B_9) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_12,c_561])).

tff(c_574,plain,(
    ! [C_74,B_75] :
      ( ~ r2_hidden(C_74,B_75)
      | k1_xboole_0 != B_75 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_197,c_567])).

tff(c_581,plain,(
    ! [A_76,B_77] :
      ( k1_xboole_0 != A_76
      | r1_tarski(A_76,B_77) ) ),
    inference(resolution,[status(thm)],[c_8,c_574])).

tff(c_20,plain,(
    ! [A_17,B_18] :
      ( k2_xboole_0(A_17,B_18) = B_18
      | ~ r1_tarski(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_597,plain,(
    ! [A_81,B_82] :
      ( k2_xboole_0(A_81,B_82) = B_82
      | k1_xboole_0 != A_81 ) ),
    inference(resolution,[status(thm)],[c_581,c_20])).

tff(c_661,plain,(
    ! [A_1] : k2_xboole_0(A_1,k1_xboole_0) = A_1 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_597])).

tff(c_38,plain,(
    r1_xboole_0('#skF_3','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_105,plain,(
    ! [A_40,B_41] :
      ( k3_xboole_0(A_40,B_41) = k1_xboole_0
      | ~ r1_xboole_0(A_40,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_113,plain,(
    k3_xboole_0('#skF_3','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_38,c_105])).

tff(c_452,plain,(
    ! [A_67,B_68] : k4_xboole_0(A_67,k3_xboole_0(A_67,B_68)) = k4_xboole_0(A_67,B_68) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_473,plain,(
    k4_xboole_0('#skF_3',k1_xboole_0) = k4_xboole_0('#skF_3','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_113,c_452])).

tff(c_483,plain,(
    k4_xboole_0('#skF_3','#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_473])).

tff(c_941,plain,(
    ! [A_95,B_96,C_97] : k4_xboole_0(k4_xboole_0(A_95,B_96),C_97) = k4_xboole_0(A_95,k2_xboole_0(B_96,C_97)) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_987,plain,(
    ! [C_97] : k4_xboole_0('#skF_3',k2_xboole_0('#skF_5',C_97)) = k4_xboole_0('#skF_3',C_97) ),
    inference(superposition,[status(thm),theory(equality)],[c_483,c_941])).

tff(c_34,plain,(
    ! [A_30,B_31] : r1_tarski(A_30,k2_xboole_0(A_30,B_31)) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_140,plain,(
    ! [A_46,B_47] :
      ( k2_xboole_0(A_46,B_47) = B_47
      | ~ r1_tarski(A_46,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_2013,plain,(
    ! [A_129,B_130] : k2_xboole_0(A_129,k2_xboole_0(A_129,B_130)) = k2_xboole_0(A_129,B_130) ),
    inference(resolution,[status(thm)],[c_34,c_140])).

tff(c_2084,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,k2_xboole_0(A_1,B_2)) = k2_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_2013])).

tff(c_2991,plain,(
    ! [C_155] : k4_xboole_0('#skF_3',k2_xboole_0('#skF_5',C_155)) = k4_xboole_0('#skF_3',C_155) ),
    inference(superposition,[status(thm),theory(equality)],[c_483,c_941])).

tff(c_3042,plain,(
    ! [A_1] : k4_xboole_0('#skF_3',k2_xboole_0(A_1,'#skF_5')) = k4_xboole_0('#skF_3',k2_xboole_0('#skF_5',A_1)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2084,c_2991])).

tff(c_3877,plain,(
    ! [A_169] : k4_xboole_0('#skF_3',k2_xboole_0(A_169,'#skF_5')) = k4_xboole_0('#skF_3',A_169) ),
    inference(demodulation,[status(thm),theory(equality)],[c_987,c_3042])).

tff(c_40,plain,(
    r1_tarski('#skF_3',k2_xboole_0('#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_152,plain,(
    k2_xboole_0('#skF_3',k2_xboole_0('#skF_4','#skF_5')) = k2_xboole_0('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_140])).

tff(c_24,plain,(
    ! [A_20,B_21] : k2_xboole_0(A_20,k4_xboole_0(B_21,A_20)) = k2_xboole_0(A_20,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_179,plain,(
    ! [A_22] : k4_xboole_0(A_22,A_22) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_176])).

tff(c_961,plain,(
    ! [A_95,B_96] : k4_xboole_0(A_95,k2_xboole_0(B_96,k4_xboole_0(A_95,B_96))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_941,c_179])).

tff(c_1032,plain,(
    ! [A_98,B_99] : k4_xboole_0(A_98,k2_xboole_0(B_99,A_98)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_961])).

tff(c_1149,plain,(
    ! [B_102,A_103] : k4_xboole_0(B_102,k2_xboole_0(B_102,A_103)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1032])).

tff(c_1200,plain,(
    k4_xboole_0('#skF_3',k2_xboole_0('#skF_4','#skF_5')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_152,c_1149])).

tff(c_3911,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_3877,c_1200])).

tff(c_4231,plain,(
    k2_xboole_0('#skF_4',k1_xboole_0) = k2_xboole_0('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_3911,c_24])).

tff(c_4256,plain,(
    k2_xboole_0('#skF_4','#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_661,c_4231])).

tff(c_66,plain,(
    ! [B_38,A_39] : k2_xboole_0(B_38,A_39) = k2_xboole_0(A_39,B_38) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_84,plain,(
    ! [B_38,A_39] : r1_tarski(B_38,k2_xboole_0(A_39,B_38)) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_34])).

tff(c_4328,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_4256,c_84])).

tff(c_4357,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_4328])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n025.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:31:21 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.50/1.81  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.61/1.82  
% 4.61/1.82  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.61/1.82  %$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 4.61/1.82  
% 4.61/1.82  %Foreground sorts:
% 4.61/1.82  
% 4.61/1.82  
% 4.61/1.82  %Background operators:
% 4.61/1.82  
% 4.61/1.82  
% 4.61/1.82  %Foreground operators:
% 4.61/1.82  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.61/1.82  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.61/1.82  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.61/1.82  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.61/1.82  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.61/1.82  tff('#skF_5', type, '#skF_5': $i).
% 4.61/1.82  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.61/1.82  tff('#skF_3', type, '#skF_3': $i).
% 4.61/1.82  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.61/1.82  tff('#skF_4', type, '#skF_4': $i).
% 4.61/1.82  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.61/1.82  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.61/1.82  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.61/1.82  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.61/1.82  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.61/1.82  
% 4.66/1.84  tff(f_81, negated_conjecture, ~(![A, B, C]: ((r1_tarski(A, k2_xboole_0(B, C)) & r1_xboole_0(A, C)) => r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_xboole_1)).
% 4.66/1.84  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 4.66/1.84  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 4.66/1.84  tff(f_66, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 4.66/1.84  tff(f_62, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 4.66/1.84  tff(f_72, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 4.66/1.84  tff(f_38, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 4.66/1.84  tff(f_56, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 4.66/1.84  tff(f_60, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 4.66/1.84  tff(f_70, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 4.66/1.84  tff(f_68, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 4.66/1.84  tff(f_74, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 4.66/1.84  tff(f_64, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 4.66/1.84  tff(c_36, plain, (~r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.66/1.84  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.66/1.84  tff(c_8, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), A_3) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.66/1.84  tff(c_26, plain, (![A_22]: (k4_xboole_0(A_22, k1_xboole_0)=A_22)), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.66/1.84  tff(c_22, plain, (![A_19]: (k3_xboole_0(A_19, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.66/1.84  tff(c_161, plain, (![A_50, B_51]: (k4_xboole_0(A_50, k4_xboole_0(A_50, B_51))=k3_xboole_0(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.66/1.84  tff(c_176, plain, (![A_22]: (k4_xboole_0(A_22, A_22)=k3_xboole_0(A_22, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_26, c_161])).
% 4.66/1.84  tff(c_180, plain, (![A_52]: (k4_xboole_0(A_52, A_52)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_176])).
% 4.66/1.84  tff(c_32, plain, (![A_28, B_29]: (k4_xboole_0(A_28, k4_xboole_0(A_28, B_29))=k3_xboole_0(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.66/1.84  tff(c_185, plain, (![A_52]: (k4_xboole_0(A_52, k1_xboole_0)=k3_xboole_0(A_52, A_52))), inference(superposition, [status(thm), theory('equality')], [c_180, c_32])).
% 4.66/1.84  tff(c_197, plain, (![A_52]: (k3_xboole_0(A_52, A_52)=A_52)), inference(demodulation, [status(thm), theory('equality')], [c_26, c_185])).
% 4.66/1.84  tff(c_12, plain, (![A_8, B_9]: (r1_xboole_0(A_8, B_9) | k3_xboole_0(A_8, B_9)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.66/1.84  tff(c_307, plain, (![A_59, B_60, C_61]: (~r1_xboole_0(A_59, B_60) | ~r2_hidden(C_61, k3_xboole_0(A_59, B_60)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.66/1.84  tff(c_561, plain, (![A_72, C_73]: (~r1_xboole_0(A_72, A_72) | ~r2_hidden(C_73, A_72))), inference(superposition, [status(thm), theory('equality')], [c_197, c_307])).
% 4.66/1.84  tff(c_567, plain, (![C_73, B_9]: (~r2_hidden(C_73, B_9) | k3_xboole_0(B_9, B_9)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_561])).
% 4.66/1.84  tff(c_574, plain, (![C_74, B_75]: (~r2_hidden(C_74, B_75) | k1_xboole_0!=B_75)), inference(demodulation, [status(thm), theory('equality')], [c_197, c_567])).
% 4.66/1.84  tff(c_581, plain, (![A_76, B_77]: (k1_xboole_0!=A_76 | r1_tarski(A_76, B_77))), inference(resolution, [status(thm)], [c_8, c_574])).
% 4.66/1.84  tff(c_20, plain, (![A_17, B_18]: (k2_xboole_0(A_17, B_18)=B_18 | ~r1_tarski(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.66/1.84  tff(c_597, plain, (![A_81, B_82]: (k2_xboole_0(A_81, B_82)=B_82 | k1_xboole_0!=A_81)), inference(resolution, [status(thm)], [c_581, c_20])).
% 4.66/1.84  tff(c_661, plain, (![A_1]: (k2_xboole_0(A_1, k1_xboole_0)=A_1)), inference(superposition, [status(thm), theory('equality')], [c_2, c_597])).
% 4.66/1.84  tff(c_38, plain, (r1_xboole_0('#skF_3', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.66/1.84  tff(c_105, plain, (![A_40, B_41]: (k3_xboole_0(A_40, B_41)=k1_xboole_0 | ~r1_xboole_0(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.66/1.84  tff(c_113, plain, (k3_xboole_0('#skF_3', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_38, c_105])).
% 4.66/1.84  tff(c_452, plain, (![A_67, B_68]: (k4_xboole_0(A_67, k3_xboole_0(A_67, B_68))=k4_xboole_0(A_67, B_68))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.66/1.84  tff(c_473, plain, (k4_xboole_0('#skF_3', k1_xboole_0)=k4_xboole_0('#skF_3', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_113, c_452])).
% 4.66/1.84  tff(c_483, plain, (k4_xboole_0('#skF_3', '#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_26, c_473])).
% 4.66/1.84  tff(c_941, plain, (![A_95, B_96, C_97]: (k4_xboole_0(k4_xboole_0(A_95, B_96), C_97)=k4_xboole_0(A_95, k2_xboole_0(B_96, C_97)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.66/1.84  tff(c_987, plain, (![C_97]: (k4_xboole_0('#skF_3', k2_xboole_0('#skF_5', C_97))=k4_xboole_0('#skF_3', C_97))), inference(superposition, [status(thm), theory('equality')], [c_483, c_941])).
% 4.66/1.84  tff(c_34, plain, (![A_30, B_31]: (r1_tarski(A_30, k2_xboole_0(A_30, B_31)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.66/1.84  tff(c_140, plain, (![A_46, B_47]: (k2_xboole_0(A_46, B_47)=B_47 | ~r1_tarski(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.66/1.84  tff(c_2013, plain, (![A_129, B_130]: (k2_xboole_0(A_129, k2_xboole_0(A_129, B_130))=k2_xboole_0(A_129, B_130))), inference(resolution, [status(thm)], [c_34, c_140])).
% 4.66/1.84  tff(c_2084, plain, (![B_2, A_1]: (k2_xboole_0(B_2, k2_xboole_0(A_1, B_2))=k2_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_2013])).
% 4.66/1.84  tff(c_2991, plain, (![C_155]: (k4_xboole_0('#skF_3', k2_xboole_0('#skF_5', C_155))=k4_xboole_0('#skF_3', C_155))), inference(superposition, [status(thm), theory('equality')], [c_483, c_941])).
% 4.66/1.84  tff(c_3042, plain, (![A_1]: (k4_xboole_0('#skF_3', k2_xboole_0(A_1, '#skF_5'))=k4_xboole_0('#skF_3', k2_xboole_0('#skF_5', A_1)))), inference(superposition, [status(thm), theory('equality')], [c_2084, c_2991])).
% 4.66/1.84  tff(c_3877, plain, (![A_169]: (k4_xboole_0('#skF_3', k2_xboole_0(A_169, '#skF_5'))=k4_xboole_0('#skF_3', A_169))), inference(demodulation, [status(thm), theory('equality')], [c_987, c_3042])).
% 4.66/1.84  tff(c_40, plain, (r1_tarski('#skF_3', k2_xboole_0('#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.66/1.84  tff(c_152, plain, (k2_xboole_0('#skF_3', k2_xboole_0('#skF_4', '#skF_5'))=k2_xboole_0('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_40, c_140])).
% 4.66/1.84  tff(c_24, plain, (![A_20, B_21]: (k2_xboole_0(A_20, k4_xboole_0(B_21, A_20))=k2_xboole_0(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.66/1.84  tff(c_179, plain, (![A_22]: (k4_xboole_0(A_22, A_22)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_176])).
% 4.66/1.84  tff(c_961, plain, (![A_95, B_96]: (k4_xboole_0(A_95, k2_xboole_0(B_96, k4_xboole_0(A_95, B_96)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_941, c_179])).
% 4.66/1.84  tff(c_1032, plain, (![A_98, B_99]: (k4_xboole_0(A_98, k2_xboole_0(B_99, A_98))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_961])).
% 4.66/1.84  tff(c_1149, plain, (![B_102, A_103]: (k4_xboole_0(B_102, k2_xboole_0(B_102, A_103))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_1032])).
% 4.66/1.84  tff(c_1200, plain, (k4_xboole_0('#skF_3', k2_xboole_0('#skF_4', '#skF_5'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_152, c_1149])).
% 4.66/1.84  tff(c_3911, plain, (k4_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_3877, c_1200])).
% 4.66/1.84  tff(c_4231, plain, (k2_xboole_0('#skF_4', k1_xboole_0)=k2_xboole_0('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_3911, c_24])).
% 4.66/1.84  tff(c_4256, plain, (k2_xboole_0('#skF_4', '#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_661, c_4231])).
% 4.66/1.84  tff(c_66, plain, (![B_38, A_39]: (k2_xboole_0(B_38, A_39)=k2_xboole_0(A_39, B_38))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.66/1.84  tff(c_84, plain, (![B_38, A_39]: (r1_tarski(B_38, k2_xboole_0(A_39, B_38)))), inference(superposition, [status(thm), theory('equality')], [c_66, c_34])).
% 4.66/1.84  tff(c_4328, plain, (r1_tarski('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_4256, c_84])).
% 4.66/1.84  tff(c_4357, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_4328])).
% 4.66/1.84  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.66/1.84  
% 4.66/1.84  Inference rules
% 4.66/1.84  ----------------------
% 4.66/1.84  #Ref     : 1
% 4.66/1.84  #Sup     : 1115
% 4.66/1.84  #Fact    : 0
% 4.66/1.84  #Define  : 0
% 4.66/1.84  #Split   : 3
% 4.66/1.84  #Chain   : 0
% 4.66/1.84  #Close   : 0
% 4.66/1.84  
% 4.66/1.84  Ordering : KBO
% 4.66/1.84  
% 4.66/1.84  Simplification rules
% 4.66/1.84  ----------------------
% 4.66/1.84  #Subsume      : 250
% 4.66/1.84  #Demod        : 781
% 4.66/1.84  #Tautology    : 589
% 4.66/1.84  #SimpNegUnit  : 35
% 4.66/1.84  #BackRed      : 1
% 4.66/1.84  
% 4.66/1.84  #Partial instantiations: 0
% 4.66/1.84  #Strategies tried      : 1
% 4.66/1.84  
% 4.66/1.84  Timing (in seconds)
% 4.66/1.84  ----------------------
% 4.66/1.84  Preprocessing        : 0.28
% 4.66/1.84  Parsing              : 0.16
% 4.66/1.84  CNF conversion       : 0.02
% 4.66/1.84  Main loop            : 0.79
% 4.66/1.84  Inferencing          : 0.24
% 4.66/1.84  Reduction            : 0.36
% 4.66/1.84  Demodulation         : 0.29
% 4.66/1.84  BG Simplification    : 0.03
% 4.66/1.84  Subsumption          : 0.12
% 4.66/1.84  Abstraction          : 0.03
% 4.66/1.84  MUC search           : 0.00
% 4.66/1.84  Cooper               : 0.00
% 4.66/1.84  Total                : 1.11
% 4.66/1.84  Index Insertion      : 0.00
% 4.66/1.84  Index Deletion       : 0.00
% 4.66/1.84  Index Matching       : 0.00
% 4.66/1.84  BG Taut test         : 0.00
%------------------------------------------------------------------------------
