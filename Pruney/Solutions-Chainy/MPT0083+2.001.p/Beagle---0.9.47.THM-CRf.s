%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:01 EST 2020

% Result     : Theorem 6.93s
% Output     : CNFRefutation 6.93s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 145 expanded)
%              Number of leaves         :   22 (  59 expanded)
%              Depth                    :   13
%              Number of atoms          :   68 ( 147 expanded)
%              Number of equality atoms :   46 ( 122 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_41,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_66,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_xboole_0(A,B)
       => r1_xboole_0(k3_xboole_0(C,A),k3_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_37,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_45,axiom,(
    ! [A,B,C] : k4_xboole_0(A,k4_xboole_0(B,C)) = k2_xboole_0(k4_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,B)
          & r1_xboole_0(A,C) )
      & ~ ( ~ ( r1_xboole_0(A,B)
              & r1_xboole_0(A,C) )
          & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).

tff(c_16,plain,(
    ! [A_12,B_13] : k4_xboole_0(A_12,k4_xboole_0(A_12,B_13)) = k3_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_10,plain,(
    ! [A_7,B_8] : k2_xboole_0(A_7,k3_xboole_0(A_7,B_8)) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_30,plain,(
    r1_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_250,plain,(
    ! [A_32,B_33] :
      ( k3_xboole_0(A_32,B_33) = k1_xboole_0
      | ~ r1_xboole_0(A_32,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_254,plain,(
    k3_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_30,c_250])).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_519,plain,(
    ! [A_53,B_54] : k2_xboole_0(k3_xboole_0(A_53,B_54),k4_xboole_0(A_53,B_54)) = A_53 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1779,plain,(
    ! [A_90,B_91] : k2_xboole_0(k3_xboole_0(A_90,B_91),k4_xboole_0(B_91,A_90)) = B_91 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_519])).

tff(c_1853,plain,(
    k2_xboole_0(k1_xboole_0,k4_xboole_0('#skF_2','#skF_1')) = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_254,c_1779])).

tff(c_113,plain,(
    ! [B_28,A_29] : k2_xboole_0(B_28,A_29) = k2_xboole_0(A_29,B_28) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_12,plain,(
    ! [A_9] : k3_xboole_0(A_9,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_39,plain,(
    ! [A_23,B_24] : k2_xboole_0(A_23,k3_xboole_0(A_23,B_24)) = A_23 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_48,plain,(
    ! [A_9] : k2_xboole_0(A_9,k1_xboole_0) = A_9 ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_39])).

tff(c_129,plain,(
    ! [A_29] : k2_xboole_0(k1_xboole_0,A_29) = A_29 ),
    inference(superposition,[status(thm),theory(equality)],[c_113,c_48])).

tff(c_1899,plain,(
    k4_xboole_0('#skF_2','#skF_1') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_1853,c_129])).

tff(c_20,plain,(
    ! [A_16,B_17,C_18] : k2_xboole_0(k4_xboole_0(A_16,B_17),k3_xboole_0(A_16,C_18)) = k4_xboole_0(A_16,k4_xboole_0(B_17,C_18)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1930,plain,(
    ! [C_18] : k4_xboole_0('#skF_2',k4_xboole_0('#skF_1',C_18)) = k2_xboole_0('#skF_2',k3_xboole_0('#skF_2',C_18)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1899,c_20])).

tff(c_1949,plain,(
    ! [C_92] : k4_xboole_0('#skF_2',k4_xboole_0('#skF_1',C_92)) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_1930])).

tff(c_1999,plain,(
    ! [B_13] : k4_xboole_0('#skF_2',k3_xboole_0('#skF_1',B_13)) = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_1949])).

tff(c_14,plain,(
    ! [A_10,B_11] : k4_xboole_0(A_10,k3_xboole_0(A_10,B_11)) = k4_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_322,plain,(
    ! [A_38,B_39] : k4_xboole_0(A_38,k3_xboole_0(A_38,B_39)) = k4_xboole_0(A_38,B_39) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2399,plain,(
    ! [B_97,A_98] : k4_xboole_0(B_97,k3_xboole_0(A_98,B_97)) = k4_xboole_0(B_97,A_98) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_322])).

tff(c_555,plain,(
    ! [A_3,B_4] : k2_xboole_0(k3_xboole_0(A_3,B_4),k4_xboole_0(B_4,A_3)) = B_4 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_519])).

tff(c_2417,plain,(
    ! [A_98,B_97] : k2_xboole_0(k3_xboole_0(k3_xboole_0(A_98,B_97),B_97),k4_xboole_0(B_97,A_98)) = B_97 ),
    inference(superposition,[status(thm),theory(equality)],[c_2399,c_555])).

tff(c_2525,plain,(
    ! [B_97,A_98] : k4_xboole_0(B_97,k4_xboole_0(A_98,B_97)) = B_97 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_20,c_2,c_4,c_2417])).

tff(c_60,plain,(
    ! [B_26,A_27] : k3_xboole_0(B_26,A_27) = k3_xboole_0(A_27,B_26) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_75,plain,(
    ! [A_27,B_26] : k2_xboole_0(A_27,k3_xboole_0(B_26,A_27)) = A_27 ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_10])).

tff(c_701,plain,(
    ! [A_59] : k2_xboole_0(k1_xboole_0,k4_xboole_0(A_59,k1_xboole_0)) = A_59 ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_519])).

tff(c_735,plain,(
    ! [A_60] : k4_xboole_0(A_60,k1_xboole_0) = A_60 ),
    inference(superposition,[status(thm),theory(equality)],[c_701,c_129])).

tff(c_748,plain,(
    ! [A_60] : k4_xboole_0(A_60,A_60) = k3_xboole_0(A_60,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_735,c_16])).

tff(c_759,plain,(
    ! [A_60] : k4_xboole_0(A_60,A_60) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_748])).

tff(c_2554,plain,(
    ! [B_99,A_100] : k4_xboole_0(B_99,k4_xboole_0(A_100,B_99)) = B_99 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_20,c_2,c_4,c_2417])).

tff(c_2613,plain,(
    ! [B_99,A_100] : k3_xboole_0(B_99,k4_xboole_0(A_100,B_99)) = k4_xboole_0(B_99,B_99) ),
    inference(superposition,[status(thm),theory(equality)],[c_2554,c_16])).

tff(c_3065,plain,(
    ! [B_106,A_107] : k3_xboole_0(B_106,k4_xboole_0(A_107,B_106)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_759,c_2613])).

tff(c_3136,plain,(
    ! [A_98,B_97] : k3_xboole_0(k4_xboole_0(A_98,B_97),B_97) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2525,c_3065])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( r1_xboole_0(A_5,B_6)
      | k3_xboole_0(A_5,B_6) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_399,plain,(
    ! [A_43,C_44,B_45] :
      ( r1_xboole_0(A_43,C_44)
      | ~ r1_xboole_0(A_43,k2_xboole_0(B_45,C_44)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_4907,plain,(
    ! [A_131,C_132,B_133] :
      ( r1_xboole_0(A_131,C_132)
      | k3_xboole_0(A_131,k2_xboole_0(B_133,C_132)) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_399])).

tff(c_5858,plain,(
    ! [A_153,B_154,C_155] : r1_xboole_0(k4_xboole_0(A_153,k2_xboole_0(B_154,C_155)),C_155) ),
    inference(superposition,[status(thm),theory(equality)],[c_3136,c_4907])).

tff(c_6261,plain,(
    ! [A_162,A_163,B_164] : r1_xboole_0(k4_xboole_0(A_162,A_163),k3_xboole_0(B_164,A_163)) ),
    inference(superposition,[status(thm),theory(equality)],[c_75,c_5858])).

tff(c_10237,plain,(
    ! [B_230,B_231,A_232] : r1_xboole_0(B_230,k3_xboole_0(B_231,k4_xboole_0(A_232,B_230))) ),
    inference(superposition,[status(thm),theory(equality)],[c_2525,c_6261])).

tff(c_10285,plain,(
    ! [B_13,B_231] : r1_xboole_0(k3_xboole_0('#skF_1',B_13),k3_xboole_0(B_231,'#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1999,c_10237])).

tff(c_28,plain,(
    ~ r1_xboole_0(k3_xboole_0('#skF_3','#skF_1'),k3_xboole_0('#skF_3','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_31,plain,(
    ~ r1_xboole_0(k3_xboole_0('#skF_1','#skF_3'),k3_xboole_0('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_28])).

tff(c_12081,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10285,c_31])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:26:35 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.93/2.50  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.93/2.51  
% 6.93/2.51  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.93/2.51  %$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 6.93/2.51  
% 6.93/2.51  %Foreground sorts:
% 6.93/2.51  
% 6.93/2.51  
% 6.93/2.51  %Background operators:
% 6.93/2.51  
% 6.93/2.51  
% 6.93/2.51  %Foreground operators:
% 6.93/2.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.93/2.51  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.93/2.51  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.93/2.51  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 6.93/2.51  tff('#skF_2', type, '#skF_2': $i).
% 6.93/2.51  tff('#skF_3', type, '#skF_3': $i).
% 6.93/2.51  tff('#skF_1', type, '#skF_1': $i).
% 6.93/2.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.93/2.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.93/2.51  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.93/2.51  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.93/2.51  
% 6.93/2.52  tff(f_41, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 6.93/2.52  tff(f_35, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_xboole_1)).
% 6.93/2.52  tff(f_66, negated_conjecture, ~(![A, B, C]: (r1_xboole_0(A, B) => r1_xboole_0(k3_xboole_0(C, A), k3_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t76_xboole_1)).
% 6.93/2.52  tff(f_33, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 6.93/2.52  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 6.93/2.52  tff(f_43, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_xboole_1)).
% 6.93/2.52  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 6.93/2.52  tff(f_37, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 6.93/2.52  tff(f_45, axiom, (![A, B, C]: (k4_xboole_0(A, k4_xboole_0(B, C)) = k2_xboole_0(k4_xboole_0(A, B), k3_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_xboole_1)).
% 6.93/2.52  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 6.93/2.52  tff(f_61, axiom, (![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_xboole_1)).
% 6.93/2.52  tff(c_16, plain, (![A_12, B_13]: (k4_xboole_0(A_12, k4_xboole_0(A_12, B_13))=k3_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.93/2.52  tff(c_10, plain, (![A_7, B_8]: (k2_xboole_0(A_7, k3_xboole_0(A_7, B_8))=A_7)), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.93/2.52  tff(c_30, plain, (r1_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_66])).
% 6.93/2.52  tff(c_250, plain, (![A_32, B_33]: (k3_xboole_0(A_32, B_33)=k1_xboole_0 | ~r1_xboole_0(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.93/2.52  tff(c_254, plain, (k3_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_30, c_250])).
% 6.93/2.52  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(B_4, A_3)=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 6.93/2.52  tff(c_519, plain, (![A_53, B_54]: (k2_xboole_0(k3_xboole_0(A_53, B_54), k4_xboole_0(A_53, B_54))=A_53)), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.93/2.52  tff(c_1779, plain, (![A_90, B_91]: (k2_xboole_0(k3_xboole_0(A_90, B_91), k4_xboole_0(B_91, A_90))=B_91)), inference(superposition, [status(thm), theory('equality')], [c_4, c_519])).
% 6.93/2.52  tff(c_1853, plain, (k2_xboole_0(k1_xboole_0, k4_xboole_0('#skF_2', '#skF_1'))='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_254, c_1779])).
% 6.93/2.52  tff(c_113, plain, (![B_28, A_29]: (k2_xboole_0(B_28, A_29)=k2_xboole_0(A_29, B_28))), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.93/2.52  tff(c_12, plain, (![A_9]: (k3_xboole_0(A_9, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 6.93/2.52  tff(c_39, plain, (![A_23, B_24]: (k2_xboole_0(A_23, k3_xboole_0(A_23, B_24))=A_23)), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.93/2.52  tff(c_48, plain, (![A_9]: (k2_xboole_0(A_9, k1_xboole_0)=A_9)), inference(superposition, [status(thm), theory('equality')], [c_12, c_39])).
% 6.93/2.52  tff(c_129, plain, (![A_29]: (k2_xboole_0(k1_xboole_0, A_29)=A_29)), inference(superposition, [status(thm), theory('equality')], [c_113, c_48])).
% 6.93/2.52  tff(c_1899, plain, (k4_xboole_0('#skF_2', '#skF_1')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_1853, c_129])).
% 6.93/2.52  tff(c_20, plain, (![A_16, B_17, C_18]: (k2_xboole_0(k4_xboole_0(A_16, B_17), k3_xboole_0(A_16, C_18))=k4_xboole_0(A_16, k4_xboole_0(B_17, C_18)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.93/2.52  tff(c_1930, plain, (![C_18]: (k4_xboole_0('#skF_2', k4_xboole_0('#skF_1', C_18))=k2_xboole_0('#skF_2', k3_xboole_0('#skF_2', C_18)))), inference(superposition, [status(thm), theory('equality')], [c_1899, c_20])).
% 6.93/2.52  tff(c_1949, plain, (![C_92]: (k4_xboole_0('#skF_2', k4_xboole_0('#skF_1', C_92))='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_1930])).
% 6.93/2.52  tff(c_1999, plain, (![B_13]: (k4_xboole_0('#skF_2', k3_xboole_0('#skF_1', B_13))='#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_16, c_1949])).
% 6.93/2.52  tff(c_14, plain, (![A_10, B_11]: (k4_xboole_0(A_10, k3_xboole_0(A_10, B_11))=k4_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.93/2.52  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.93/2.52  tff(c_322, plain, (![A_38, B_39]: (k4_xboole_0(A_38, k3_xboole_0(A_38, B_39))=k4_xboole_0(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.93/2.52  tff(c_2399, plain, (![B_97, A_98]: (k4_xboole_0(B_97, k3_xboole_0(A_98, B_97))=k4_xboole_0(B_97, A_98))), inference(superposition, [status(thm), theory('equality')], [c_4, c_322])).
% 6.93/2.52  tff(c_555, plain, (![A_3, B_4]: (k2_xboole_0(k3_xboole_0(A_3, B_4), k4_xboole_0(B_4, A_3))=B_4)), inference(superposition, [status(thm), theory('equality')], [c_4, c_519])).
% 6.93/2.52  tff(c_2417, plain, (![A_98, B_97]: (k2_xboole_0(k3_xboole_0(k3_xboole_0(A_98, B_97), B_97), k4_xboole_0(B_97, A_98))=B_97)), inference(superposition, [status(thm), theory('equality')], [c_2399, c_555])).
% 6.93/2.52  tff(c_2525, plain, (![B_97, A_98]: (k4_xboole_0(B_97, k4_xboole_0(A_98, B_97))=B_97)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_20, c_2, c_4, c_2417])).
% 6.93/2.52  tff(c_60, plain, (![B_26, A_27]: (k3_xboole_0(B_26, A_27)=k3_xboole_0(A_27, B_26))), inference(cnfTransformation, [status(thm)], [f_29])).
% 6.93/2.52  tff(c_75, plain, (![A_27, B_26]: (k2_xboole_0(A_27, k3_xboole_0(B_26, A_27))=A_27)), inference(superposition, [status(thm), theory('equality')], [c_60, c_10])).
% 6.93/2.52  tff(c_701, plain, (![A_59]: (k2_xboole_0(k1_xboole_0, k4_xboole_0(A_59, k1_xboole_0))=A_59)), inference(superposition, [status(thm), theory('equality')], [c_12, c_519])).
% 6.93/2.52  tff(c_735, plain, (![A_60]: (k4_xboole_0(A_60, k1_xboole_0)=A_60)), inference(superposition, [status(thm), theory('equality')], [c_701, c_129])).
% 6.93/2.52  tff(c_748, plain, (![A_60]: (k4_xboole_0(A_60, A_60)=k3_xboole_0(A_60, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_735, c_16])).
% 6.93/2.52  tff(c_759, plain, (![A_60]: (k4_xboole_0(A_60, A_60)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_748])).
% 6.93/2.52  tff(c_2554, plain, (![B_99, A_100]: (k4_xboole_0(B_99, k4_xboole_0(A_100, B_99))=B_99)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_20, c_2, c_4, c_2417])).
% 6.93/2.52  tff(c_2613, plain, (![B_99, A_100]: (k3_xboole_0(B_99, k4_xboole_0(A_100, B_99))=k4_xboole_0(B_99, B_99))), inference(superposition, [status(thm), theory('equality')], [c_2554, c_16])).
% 6.93/2.52  tff(c_3065, plain, (![B_106, A_107]: (k3_xboole_0(B_106, k4_xboole_0(A_107, B_106))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_759, c_2613])).
% 6.93/2.52  tff(c_3136, plain, (![A_98, B_97]: (k3_xboole_0(k4_xboole_0(A_98, B_97), B_97)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2525, c_3065])).
% 6.93/2.52  tff(c_8, plain, (![A_5, B_6]: (r1_xboole_0(A_5, B_6) | k3_xboole_0(A_5, B_6)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.93/2.52  tff(c_399, plain, (![A_43, C_44, B_45]: (r1_xboole_0(A_43, C_44) | ~r1_xboole_0(A_43, k2_xboole_0(B_45, C_44)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 6.93/2.52  tff(c_4907, plain, (![A_131, C_132, B_133]: (r1_xboole_0(A_131, C_132) | k3_xboole_0(A_131, k2_xboole_0(B_133, C_132))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_399])).
% 6.93/2.52  tff(c_5858, plain, (![A_153, B_154, C_155]: (r1_xboole_0(k4_xboole_0(A_153, k2_xboole_0(B_154, C_155)), C_155))), inference(superposition, [status(thm), theory('equality')], [c_3136, c_4907])).
% 6.93/2.52  tff(c_6261, plain, (![A_162, A_163, B_164]: (r1_xboole_0(k4_xboole_0(A_162, A_163), k3_xboole_0(B_164, A_163)))), inference(superposition, [status(thm), theory('equality')], [c_75, c_5858])).
% 6.93/2.52  tff(c_10237, plain, (![B_230, B_231, A_232]: (r1_xboole_0(B_230, k3_xboole_0(B_231, k4_xboole_0(A_232, B_230))))), inference(superposition, [status(thm), theory('equality')], [c_2525, c_6261])).
% 6.93/2.52  tff(c_10285, plain, (![B_13, B_231]: (r1_xboole_0(k3_xboole_0('#skF_1', B_13), k3_xboole_0(B_231, '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_1999, c_10237])).
% 6.93/2.52  tff(c_28, plain, (~r1_xboole_0(k3_xboole_0('#skF_3', '#skF_1'), k3_xboole_0('#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_66])).
% 6.93/2.52  tff(c_31, plain, (~r1_xboole_0(k3_xboole_0('#skF_1', '#skF_3'), k3_xboole_0('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_28])).
% 6.93/2.53  tff(c_12081, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10285, c_31])).
% 6.93/2.53  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.93/2.53  
% 6.93/2.53  Inference rules
% 6.93/2.53  ----------------------
% 6.93/2.53  #Ref     : 0
% 6.93/2.53  #Sup     : 2998
% 6.93/2.53  #Fact    : 0
% 6.93/2.53  #Define  : 0
% 6.93/2.53  #Split   : 0
% 6.93/2.53  #Chain   : 0
% 6.93/2.53  #Close   : 0
% 6.93/2.53  
% 6.93/2.53  Ordering : KBO
% 6.93/2.53  
% 6.93/2.53  Simplification rules
% 6.93/2.53  ----------------------
% 6.93/2.53  #Subsume      : 81
% 6.93/2.53  #Demod        : 2835
% 6.93/2.53  #Tautology    : 2239
% 6.93/2.53  #SimpNegUnit  : 0
% 6.93/2.53  #BackRed      : 4
% 6.93/2.53  
% 6.93/2.53  #Partial instantiations: 0
% 6.93/2.53  #Strategies tried      : 1
% 6.93/2.53  
% 6.93/2.53  Timing (in seconds)
% 6.93/2.53  ----------------------
% 6.93/2.53  Preprocessing        : 0.30
% 6.93/2.53  Parsing              : 0.17
% 6.93/2.53  CNF conversion       : 0.02
% 6.93/2.53  Main loop            : 1.41
% 6.93/2.53  Inferencing          : 0.37
% 6.93/2.53  Reduction            : 0.70
% 6.93/2.53  Demodulation         : 0.59
% 6.93/2.53  BG Simplification    : 0.04
% 6.93/2.53  Subsumption          : 0.23
% 6.93/2.53  Abstraction          : 0.05
% 6.93/2.53  MUC search           : 0.00
% 6.93/2.53  Cooper               : 0.00
% 6.93/2.53  Total                : 1.74
% 6.93/2.53  Index Insertion      : 0.00
% 6.93/2.53  Index Deletion       : 0.00
% 6.93/2.53  Index Matching       : 0.00
% 6.93/2.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------
