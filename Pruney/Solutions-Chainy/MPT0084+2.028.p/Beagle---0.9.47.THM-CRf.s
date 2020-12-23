%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:08 EST 2020

% Result     : Theorem 4.44s
% Output     : CNFRefutation 4.57s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 133 expanded)
%              Number of leaves         :   25 (  55 expanded)
%              Depth                    :   15
%              Number of atoms          :   81 ( 164 expanded)
%              Number of equality atoms :   41 (  83 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_74,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( ~ r1_xboole_0(A,B)
          & r1_tarski(A,C)
          & r1_xboole_0(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_xboole_1)).

tff(f_65,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_55,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_41,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_57,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_61,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_63,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_49,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(c_30,plain,(
    ~ r1_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_24,plain,(
    ! [A_21] : r1_xboole_0(A_21,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_14,plain,(
    ! [A_12] : k3_xboole_0(A_12,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_146,plain,(
    ! [A_33,B_34,C_35] :
      ( ~ r1_xboole_0(A_33,B_34)
      | ~ r2_hidden(C_35,k3_xboole_0(A_33,B_34)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_162,plain,(
    ! [A_12,C_35] :
      ( ~ r1_xboole_0(A_12,k1_xboole_0)
      | ~ r2_hidden(C_35,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_146])).

tff(c_165,plain,(
    ! [C_35] : ~ r2_hidden(C_35,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_162])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_16,plain,(
    ! [A_13] : k4_xboole_0(A_13,k1_xboole_0) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_192,plain,(
    ! [A_39,B_40] : k4_xboole_0(A_39,k4_xboole_0(A_39,B_40)) = k3_xboole_0(A_39,B_40) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_210,plain,(
    ! [A_13] : k4_xboole_0(A_13,A_13) = k3_xboole_0(A_13,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_192])).

tff(c_214,plain,(
    ! [A_13] : k4_xboole_0(A_13,A_13) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_210])).

tff(c_20,plain,(
    ! [A_16,B_17] : k4_xboole_0(A_16,k4_xboole_0(A_16,B_17)) = k3_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_276,plain,(
    ! [A_43,B_44] : k4_xboole_0(A_43,k3_xboole_0(A_43,B_44)) = k4_xboole_0(A_43,B_44) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_282,plain,(
    ! [A_43,B_44] : k4_xboole_0(A_43,k4_xboole_0(A_43,B_44)) = k3_xboole_0(A_43,k3_xboole_0(A_43,B_44)) ),
    inference(superposition,[status(thm),theory(equality)],[c_276,c_20])).

tff(c_439,plain,(
    ! [A_50,B_51] : k3_xboole_0(A_50,k3_xboole_0(A_50,B_51)) = k3_xboole_0(A_50,B_51) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_282])).

tff(c_300,plain,(
    ! [A_1,B_2] : k4_xboole_0(A_1,k3_xboole_0(B_2,A_1)) = k4_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_276])).

tff(c_448,plain,(
    ! [A_50,B_51] : k4_xboole_0(k3_xboole_0(A_50,B_51),k3_xboole_0(A_50,B_51)) = k4_xboole_0(k3_xboole_0(A_50,B_51),A_50) ),
    inference(superposition,[status(thm),theory(equality)],[c_439,c_300])).

tff(c_503,plain,(
    ! [A_52,B_53] : k4_xboole_0(k3_xboole_0(A_52,B_53),A_52) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_214,c_448])).

tff(c_532,plain,(
    ! [B_2,A_1] : k4_xboole_0(k3_xboole_0(B_2,A_1),A_1) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_503])).

tff(c_28,plain,(
    r1_tarski('#skF_3','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_132,plain,(
    ! [A_29,B_30] :
      ( k4_xboole_0(A_29,B_30) = k1_xboole_0
      | ~ r1_tarski(A_29,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_136,plain,(
    k4_xboole_0('#skF_3','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_28,c_132])).

tff(c_207,plain,(
    k4_xboole_0('#skF_3',k1_xboole_0) = k3_xboole_0('#skF_3','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_136,c_192])).

tff(c_213,plain,(
    k3_xboole_0('#skF_3','#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_207])).

tff(c_22,plain,(
    ! [A_18,B_19,C_20] : k4_xboole_0(k3_xboole_0(A_18,B_19),C_20) = k3_xboole_0(A_18,k4_xboole_0(B_19,C_20)) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_48,plain,(
    ! [B_25,A_26] : k3_xboole_0(B_25,A_26) = k3_xboole_0(A_26,B_25) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_64,plain,(
    ! [A_26] : k3_xboole_0(k1_xboole_0,A_26) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_14])).

tff(c_297,plain,(
    ! [A_26] : k4_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,A_26) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_276])).

tff(c_313,plain,(
    ! [A_26] : k4_xboole_0(k1_xboole_0,A_26) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_297])).

tff(c_26,plain,(
    r1_xboole_0('#skF_3',k3_xboole_0('#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_8,plain,(
    ! [A_8] :
      ( r2_hidden('#skF_2'(A_8),A_8)
      | k1_xboole_0 = A_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_173,plain,(
    ! [A_37,B_38] :
      ( ~ r1_xboole_0(A_37,B_38)
      | k3_xboole_0(A_37,B_38) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_146])).

tff(c_180,plain,(
    k3_xboole_0('#skF_3',k3_xboole_0('#skF_4','#skF_5')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_26,c_173])).

tff(c_728,plain,(
    ! [A_64,B_65,C_66] : k4_xboole_0(k3_xboole_0(A_64,B_65),C_66) = k3_xboole_0(A_64,k4_xboole_0(B_65,C_66)) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_805,plain,(
    ! [C_66] : k3_xboole_0('#skF_3',k4_xboole_0(k3_xboole_0('#skF_4','#skF_5'),C_66)) = k4_xboole_0(k1_xboole_0,C_66) ),
    inference(superposition,[status(thm),theory(equality)],[c_180,c_728])).

tff(c_836,plain,(
    ! [C_66] : k3_xboole_0('#skF_3',k3_xboole_0('#skF_4',k4_xboole_0('#skF_5',C_66))) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_313,c_805])).

tff(c_615,plain,(
    ! [A_56,B_57] :
      ( r2_hidden('#skF_1'(A_56,B_57),k3_xboole_0(A_56,B_57))
      | r1_xboole_0(A_56,B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2450,plain,(
    ! [B_100,A_101] :
      ( r2_hidden('#skF_1'(B_100,A_101),k3_xboole_0(A_101,B_100))
      | r1_xboole_0(B_100,A_101) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_615])).

tff(c_2462,plain,(
    ! [C_66] :
      ( r2_hidden('#skF_1'(k3_xboole_0('#skF_4',k4_xboole_0('#skF_5',C_66)),'#skF_3'),k1_xboole_0)
      | r1_xboole_0(k3_xboole_0('#skF_4',k4_xboole_0('#skF_5',C_66)),'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_836,c_2450])).

tff(c_2561,plain,(
    ! [C_103] : r1_xboole_0(k3_xboole_0('#skF_4',k4_xboole_0('#skF_5',C_103)),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_165,c_2462])).

tff(c_2741,plain,(
    ! [B_108] : r1_xboole_0(k3_xboole_0('#skF_4',k3_xboole_0('#skF_5',B_108)),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_2561])).

tff(c_4081,plain,(
    ! [B_131] : r1_xboole_0(k3_xboole_0('#skF_4',k3_xboole_0(B_131,'#skF_5')),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_2741])).

tff(c_4102,plain,(
    r1_xboole_0(k3_xboole_0('#skF_4','#skF_3'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_213,c_4081])).

tff(c_669,plain,(
    ! [A_59,B_60,C_61] :
      ( ~ r1_xboole_0(A_59,B_60)
      | ~ r2_hidden(C_61,k3_xboole_0(B_60,A_59)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_146])).

tff(c_702,plain,(
    ! [A_59,B_60] :
      ( ~ r1_xboole_0(A_59,B_60)
      | k3_xboole_0(B_60,A_59) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_669])).

tff(c_4131,plain,(
    k3_xboole_0('#skF_3',k3_xboole_0('#skF_4','#skF_3')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4102,c_702])).

tff(c_4309,plain,(
    k4_xboole_0(k3_xboole_0('#skF_4','#skF_3'),k1_xboole_0) = k4_xboole_0(k3_xboole_0('#skF_4','#skF_3'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_4131,c_300])).

tff(c_4335,plain,(
    k3_xboole_0('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_532,c_16,c_4309])).

tff(c_639,plain,(
    ! [B_2,A_1] :
      ( r2_hidden('#skF_1'(B_2,A_1),k3_xboole_0(A_1,B_2))
      | r1_xboole_0(B_2,A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_615])).

tff(c_4357,plain,
    ( r2_hidden('#skF_1'('#skF_3','#skF_4'),k1_xboole_0)
    | r1_xboole_0('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_4335,c_639])).

tff(c_4402,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_165,c_4357])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:54:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.44/1.80  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.50/1.81  
% 4.50/1.81  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.50/1.81  %$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1
% 4.50/1.81  
% 4.50/1.81  %Foreground sorts:
% 4.50/1.81  
% 4.50/1.81  
% 4.50/1.81  %Background operators:
% 4.50/1.81  
% 4.50/1.81  
% 4.50/1.81  %Foreground operators:
% 4.50/1.81  tff('#skF_2', type, '#skF_2': $i > $i).
% 4.50/1.81  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.50/1.81  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.50/1.81  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.50/1.81  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.50/1.81  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.50/1.81  tff('#skF_5', type, '#skF_5': $i).
% 4.50/1.81  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.50/1.81  tff('#skF_3', type, '#skF_3': $i).
% 4.50/1.81  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.50/1.81  tff('#skF_4', type, '#skF_4': $i).
% 4.50/1.81  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.50/1.81  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.50/1.81  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.50/1.81  
% 4.57/1.82  tff(f_74, negated_conjecture, ~(![A, B, C]: ~((~r1_xboole_0(A, B) & r1_tarski(A, C)) & r1_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_xboole_1)).
% 4.57/1.82  tff(f_65, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 4.57/1.82  tff(f_55, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 4.57/1.82  tff(f_41, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 4.57/1.82  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 4.57/1.82  tff(f_57, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 4.57/1.82  tff(f_61, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 4.57/1.82  tff(f_59, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 4.57/1.82  tff(f_53, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 4.57/1.82  tff(f_63, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_xboole_1)).
% 4.57/1.82  tff(f_49, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 4.57/1.82  tff(c_30, plain, (~r1_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.57/1.82  tff(c_24, plain, (![A_21]: (r1_xboole_0(A_21, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.57/1.82  tff(c_14, plain, (![A_12]: (k3_xboole_0(A_12, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.57/1.82  tff(c_146, plain, (![A_33, B_34, C_35]: (~r1_xboole_0(A_33, B_34) | ~r2_hidden(C_35, k3_xboole_0(A_33, B_34)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.57/1.82  tff(c_162, plain, (![A_12, C_35]: (~r1_xboole_0(A_12, k1_xboole_0) | ~r2_hidden(C_35, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_14, c_146])).
% 4.57/1.82  tff(c_165, plain, (![C_35]: (~r2_hidden(C_35, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_162])).
% 4.57/1.82  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.57/1.82  tff(c_16, plain, (![A_13]: (k4_xboole_0(A_13, k1_xboole_0)=A_13)), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.57/1.82  tff(c_192, plain, (![A_39, B_40]: (k4_xboole_0(A_39, k4_xboole_0(A_39, B_40))=k3_xboole_0(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.57/1.82  tff(c_210, plain, (![A_13]: (k4_xboole_0(A_13, A_13)=k3_xboole_0(A_13, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_16, c_192])).
% 4.57/1.82  tff(c_214, plain, (![A_13]: (k4_xboole_0(A_13, A_13)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_210])).
% 4.57/1.82  tff(c_20, plain, (![A_16, B_17]: (k4_xboole_0(A_16, k4_xboole_0(A_16, B_17))=k3_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.57/1.82  tff(c_276, plain, (![A_43, B_44]: (k4_xboole_0(A_43, k3_xboole_0(A_43, B_44))=k4_xboole_0(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.57/1.82  tff(c_282, plain, (![A_43, B_44]: (k4_xboole_0(A_43, k4_xboole_0(A_43, B_44))=k3_xboole_0(A_43, k3_xboole_0(A_43, B_44)))), inference(superposition, [status(thm), theory('equality')], [c_276, c_20])).
% 4.57/1.82  tff(c_439, plain, (![A_50, B_51]: (k3_xboole_0(A_50, k3_xboole_0(A_50, B_51))=k3_xboole_0(A_50, B_51))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_282])).
% 4.57/1.82  tff(c_300, plain, (![A_1, B_2]: (k4_xboole_0(A_1, k3_xboole_0(B_2, A_1))=k4_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_276])).
% 4.57/1.82  tff(c_448, plain, (![A_50, B_51]: (k4_xboole_0(k3_xboole_0(A_50, B_51), k3_xboole_0(A_50, B_51))=k4_xboole_0(k3_xboole_0(A_50, B_51), A_50))), inference(superposition, [status(thm), theory('equality')], [c_439, c_300])).
% 4.57/1.82  tff(c_503, plain, (![A_52, B_53]: (k4_xboole_0(k3_xboole_0(A_52, B_53), A_52)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_214, c_448])).
% 4.57/1.82  tff(c_532, plain, (![B_2, A_1]: (k4_xboole_0(k3_xboole_0(B_2, A_1), A_1)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_503])).
% 4.57/1.82  tff(c_28, plain, (r1_tarski('#skF_3', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.57/1.82  tff(c_132, plain, (![A_29, B_30]: (k4_xboole_0(A_29, B_30)=k1_xboole_0 | ~r1_tarski(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.57/1.82  tff(c_136, plain, (k4_xboole_0('#skF_3', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_28, c_132])).
% 4.57/1.82  tff(c_207, plain, (k4_xboole_0('#skF_3', k1_xboole_0)=k3_xboole_0('#skF_3', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_136, c_192])).
% 4.57/1.82  tff(c_213, plain, (k3_xboole_0('#skF_3', '#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_16, c_207])).
% 4.57/1.82  tff(c_22, plain, (![A_18, B_19, C_20]: (k4_xboole_0(k3_xboole_0(A_18, B_19), C_20)=k3_xboole_0(A_18, k4_xboole_0(B_19, C_20)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.57/1.82  tff(c_48, plain, (![B_25, A_26]: (k3_xboole_0(B_25, A_26)=k3_xboole_0(A_26, B_25))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.57/1.82  tff(c_64, plain, (![A_26]: (k3_xboole_0(k1_xboole_0, A_26)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_48, c_14])).
% 4.57/1.82  tff(c_297, plain, (![A_26]: (k4_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, A_26))), inference(superposition, [status(thm), theory('equality')], [c_64, c_276])).
% 4.57/1.82  tff(c_313, plain, (![A_26]: (k4_xboole_0(k1_xboole_0, A_26)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_297])).
% 4.57/1.82  tff(c_26, plain, (r1_xboole_0('#skF_3', k3_xboole_0('#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.57/1.82  tff(c_8, plain, (![A_8]: (r2_hidden('#skF_2'(A_8), A_8) | k1_xboole_0=A_8)), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.57/1.82  tff(c_173, plain, (![A_37, B_38]: (~r1_xboole_0(A_37, B_38) | k3_xboole_0(A_37, B_38)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_146])).
% 4.57/1.82  tff(c_180, plain, (k3_xboole_0('#skF_3', k3_xboole_0('#skF_4', '#skF_5'))=k1_xboole_0), inference(resolution, [status(thm)], [c_26, c_173])).
% 4.57/1.82  tff(c_728, plain, (![A_64, B_65, C_66]: (k4_xboole_0(k3_xboole_0(A_64, B_65), C_66)=k3_xboole_0(A_64, k4_xboole_0(B_65, C_66)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.57/1.82  tff(c_805, plain, (![C_66]: (k3_xboole_0('#skF_3', k4_xboole_0(k3_xboole_0('#skF_4', '#skF_5'), C_66))=k4_xboole_0(k1_xboole_0, C_66))), inference(superposition, [status(thm), theory('equality')], [c_180, c_728])).
% 4.57/1.82  tff(c_836, plain, (![C_66]: (k3_xboole_0('#skF_3', k3_xboole_0('#skF_4', k4_xboole_0('#skF_5', C_66)))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_313, c_805])).
% 4.57/1.82  tff(c_615, plain, (![A_56, B_57]: (r2_hidden('#skF_1'(A_56, B_57), k3_xboole_0(A_56, B_57)) | r1_xboole_0(A_56, B_57))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.57/1.82  tff(c_2450, plain, (![B_100, A_101]: (r2_hidden('#skF_1'(B_100, A_101), k3_xboole_0(A_101, B_100)) | r1_xboole_0(B_100, A_101))), inference(superposition, [status(thm), theory('equality')], [c_2, c_615])).
% 4.57/1.82  tff(c_2462, plain, (![C_66]: (r2_hidden('#skF_1'(k3_xboole_0('#skF_4', k4_xboole_0('#skF_5', C_66)), '#skF_3'), k1_xboole_0) | r1_xboole_0(k3_xboole_0('#skF_4', k4_xboole_0('#skF_5', C_66)), '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_836, c_2450])).
% 4.57/1.82  tff(c_2561, plain, (![C_103]: (r1_xboole_0(k3_xboole_0('#skF_4', k4_xboole_0('#skF_5', C_103)), '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_165, c_2462])).
% 4.57/1.82  tff(c_2741, plain, (![B_108]: (r1_xboole_0(k3_xboole_0('#skF_4', k3_xboole_0('#skF_5', B_108)), '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_20, c_2561])).
% 4.57/1.82  tff(c_4081, plain, (![B_131]: (r1_xboole_0(k3_xboole_0('#skF_4', k3_xboole_0(B_131, '#skF_5')), '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_2, c_2741])).
% 4.57/1.82  tff(c_4102, plain, (r1_xboole_0(k3_xboole_0('#skF_4', '#skF_3'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_213, c_4081])).
% 4.57/1.82  tff(c_669, plain, (![A_59, B_60, C_61]: (~r1_xboole_0(A_59, B_60) | ~r2_hidden(C_61, k3_xboole_0(B_60, A_59)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_146])).
% 4.57/1.82  tff(c_702, plain, (![A_59, B_60]: (~r1_xboole_0(A_59, B_60) | k3_xboole_0(B_60, A_59)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_669])).
% 4.57/1.82  tff(c_4131, plain, (k3_xboole_0('#skF_3', k3_xboole_0('#skF_4', '#skF_3'))=k1_xboole_0), inference(resolution, [status(thm)], [c_4102, c_702])).
% 4.57/1.82  tff(c_4309, plain, (k4_xboole_0(k3_xboole_0('#skF_4', '#skF_3'), k1_xboole_0)=k4_xboole_0(k3_xboole_0('#skF_4', '#skF_3'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_4131, c_300])).
% 4.57/1.82  tff(c_4335, plain, (k3_xboole_0('#skF_4', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_532, c_16, c_4309])).
% 4.57/1.82  tff(c_639, plain, (![B_2, A_1]: (r2_hidden('#skF_1'(B_2, A_1), k3_xboole_0(A_1, B_2)) | r1_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_615])).
% 4.57/1.82  tff(c_4357, plain, (r2_hidden('#skF_1'('#skF_3', '#skF_4'), k1_xboole_0) | r1_xboole_0('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_4335, c_639])).
% 4.57/1.82  tff(c_4402, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_165, c_4357])).
% 4.57/1.82  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.57/1.82  
% 4.57/1.82  Inference rules
% 4.57/1.82  ----------------------
% 4.57/1.82  #Ref     : 0
% 4.57/1.82  #Sup     : 1093
% 4.57/1.82  #Fact    : 0
% 4.57/1.82  #Define  : 0
% 4.57/1.82  #Split   : 2
% 4.57/1.82  #Chain   : 0
% 4.57/1.82  #Close   : 0
% 4.57/1.82  
% 4.57/1.82  Ordering : KBO
% 4.57/1.82  
% 4.57/1.82  Simplification rules
% 4.57/1.82  ----------------------
% 4.57/1.82  #Subsume      : 33
% 4.57/1.82  #Demod        : 906
% 4.57/1.82  #Tautology    : 743
% 4.57/1.82  #SimpNegUnit  : 25
% 4.57/1.82  #BackRed      : 3
% 4.57/1.82  
% 4.57/1.82  #Partial instantiations: 0
% 4.57/1.82  #Strategies tried      : 1
% 4.57/1.82  
% 4.57/1.82  Timing (in seconds)
% 4.57/1.82  ----------------------
% 4.57/1.83  Preprocessing        : 0.28
% 4.57/1.83  Parsing              : 0.15
% 4.57/1.83  CNF conversion       : 0.02
% 4.57/1.83  Main loop            : 0.76
% 4.57/1.83  Inferencing          : 0.23
% 4.57/1.83  Reduction            : 0.35
% 4.57/1.83  Demodulation         : 0.29
% 4.57/1.83  BG Simplification    : 0.02
% 4.57/1.83  Subsumption          : 0.11
% 4.57/1.83  Abstraction          : 0.03
% 4.57/1.83  MUC search           : 0.00
% 4.57/1.83  Cooper               : 0.00
% 4.57/1.83  Total                : 1.07
% 4.57/1.83  Index Insertion      : 0.00
% 4.57/1.83  Index Deletion       : 0.00
% 4.57/1.83  Index Matching       : 0.00
% 4.57/1.83  BG Taut test         : 0.00
%------------------------------------------------------------------------------
