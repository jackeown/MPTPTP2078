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
% DateTime   : Thu Dec  3 09:51:16 EST 2020

% Result     : Theorem 6.64s
% Output     : CNFRefutation 6.64s
% Verified   : 
% Statistics : Number of formulae       :   69 (  99 expanded)
%              Number of leaves         :   30 (  46 expanded)
%              Depth                    :   10
%              Number of atoms          :   75 ( 116 expanded)
%              Number of equality atoms :   42 (  71 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(f_70,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r2_hidden(A,B)
          & r2_hidden(C,B) )
       => k2_xboole_0(k2_tarski(A,C),B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_zfmisc_1)).

tff(f_35,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_45,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_41,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_49,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_57,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_47,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(c_40,plain,(
    r2_hidden('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_42,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_10,plain,(
    ! [A_5] : k2_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_18,plain,(
    ! [A_11] : k4_xboole_0(A_11,k1_xboole_0) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_14,plain,(
    ! [A_8] : r1_tarski(k1_xboole_0,A_8) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_106,plain,(
    ! [A_38,B_39] :
      ( k3_xboole_0(A_38,B_39) = A_38
      | ~ r1_tarski(A_38,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_113,plain,(
    ! [A_8] : k3_xboole_0(k1_xboole_0,A_8) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14,c_106])).

tff(c_327,plain,(
    ! [A_54,B_55] : k5_xboole_0(A_54,k3_xboole_0(A_54,B_55)) = k4_xboole_0(A_54,B_55) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_364,plain,(
    ! [A_58] : k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,A_58) ),
    inference(superposition,[status(thm),theory(equality)],[c_113,c_327])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_114,plain,(
    ! [B_2] : k3_xboole_0(B_2,B_2) = B_2 ),
    inference(resolution,[status(thm)],[c_6,c_106])).

tff(c_336,plain,(
    ! [B_2] : k5_xboole_0(B_2,B_2) = k4_xboole_0(B_2,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_114,c_327])).

tff(c_370,plain,(
    ! [A_58] : k4_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,A_58) ),
    inference(superposition,[status(thm),theory(equality)],[c_364,c_336])).

tff(c_383,plain,(
    ! [A_58] : k4_xboole_0(k1_xboole_0,A_58) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_370])).

tff(c_22,plain,(
    ! [B_15,A_14] : k2_tarski(B_15,A_14) = k2_tarski(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_141,plain,(
    ! [A_42,B_43] : k3_tarski(k2_tarski(A_42,B_43)) = k2_xboole_0(A_42,B_43) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_156,plain,(
    ! [B_44,A_45] : k3_tarski(k2_tarski(B_44,A_45)) = k2_xboole_0(A_45,B_44) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_141])).

tff(c_30,plain,(
    ! [A_25,B_26] : k3_tarski(k2_tarski(A_25,B_26)) = k2_xboole_0(A_25,B_26) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_180,plain,(
    ! [B_46,A_47] : k2_xboole_0(B_46,A_47) = k2_xboole_0(A_47,B_46) ),
    inference(superposition,[status(thm),theory(equality)],[c_156,c_30])).

tff(c_256,plain,(
    ! [A_50] : k2_xboole_0(k1_xboole_0,A_50) = A_50 ),
    inference(superposition,[status(thm),theory(equality)],[c_180,c_10])).

tff(c_20,plain,(
    ! [A_12,B_13] : k4_xboole_0(k2_xboole_0(A_12,B_13),B_13) = k4_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_262,plain,(
    ! [A_50] : k4_xboole_0(k1_xboole_0,A_50) = k4_xboole_0(A_50,A_50) ),
    inference(superposition,[status(thm),theory(equality)],[c_256,c_20])).

tff(c_399,plain,(
    ! [A_50] : k4_xboole_0(A_50,A_50) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_383,c_262])).

tff(c_430,plain,(
    ! [B_2] : k5_xboole_0(B_2,B_2) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_399,c_336])).

tff(c_578,plain,(
    ! [A_78,B_79,C_80] :
      ( r1_tarski(k2_tarski(A_78,B_79),C_80)
      | ~ r2_hidden(B_79,C_80)
      | ~ r2_hidden(A_78,C_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_12,plain,(
    ! [A_6,B_7] :
      ( k3_xboole_0(A_6,B_7) = A_6
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2086,plain,(
    ! [A_117,B_118,C_119] :
      ( k3_xboole_0(k2_tarski(A_117,B_118),C_119) = k2_tarski(A_117,B_118)
      | ~ r2_hidden(B_118,C_119)
      | ~ r2_hidden(A_117,C_119) ) ),
    inference(resolution,[status(thm)],[c_578,c_12])).

tff(c_3833,plain,(
    ! [A_139,B_140,C_141] :
      ( k3_xboole_0(k2_tarski(A_139,B_140),C_141) = k2_tarski(B_140,A_139)
      | ~ r2_hidden(A_139,C_141)
      | ~ r2_hidden(B_140,C_141) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_2086])).

tff(c_8,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k3_xboole_0(A_3,B_4)) = k4_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_4503,plain,(
    ! [A_149,B_150,C_151] :
      ( k5_xboole_0(k2_tarski(A_149,B_150),k2_tarski(B_150,A_149)) = k4_xboole_0(k2_tarski(A_149,B_150),C_151)
      | ~ r2_hidden(A_149,C_151)
      | ~ r2_hidden(B_150,C_151) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3833,c_8])).

tff(c_16,plain,(
    ! [A_9,B_10] : k2_xboole_0(A_9,k4_xboole_0(B_10,A_9)) = k2_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_5253,plain,(
    ! [C_163,A_164,B_165] :
      ( k2_xboole_0(C_163,k5_xboole_0(k2_tarski(A_164,B_165),k2_tarski(B_165,A_164))) = k2_xboole_0(C_163,k2_tarski(A_164,B_165))
      | ~ r2_hidden(A_164,C_163)
      | ~ r2_hidden(B_165,C_163) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4503,c_16])).

tff(c_5435,plain,(
    ! [C_163,A_14,B_15] :
      ( k2_xboole_0(C_163,k5_xboole_0(k2_tarski(A_14,B_15),k2_tarski(A_14,B_15))) = k2_xboole_0(C_163,k2_tarski(B_15,A_14))
      | ~ r2_hidden(B_15,C_163)
      | ~ r2_hidden(A_14,C_163) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_5253])).

tff(c_8319,plain,(
    ! [C_202,B_203,A_204] :
      ( k2_xboole_0(C_202,k2_tarski(B_203,A_204)) = C_202
      | ~ r2_hidden(B_203,C_202)
      | ~ r2_hidden(A_204,C_202) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_430,c_5435])).

tff(c_162,plain,(
    ! [B_44,A_45] : k2_xboole_0(B_44,A_45) = k2_xboole_0(A_45,B_44) ),
    inference(superposition,[status(thm),theory(equality)],[c_156,c_30])).

tff(c_38,plain,(
    k2_xboole_0(k2_tarski('#skF_1','#skF_3'),'#skF_2') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_179,plain,(
    k2_xboole_0('#skF_2',k2_tarski('#skF_1','#skF_3')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_162,c_38])).

tff(c_8457,plain,
    ( ~ r2_hidden('#skF_1','#skF_2')
    | ~ r2_hidden('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_8319,c_179])).

tff(c_8548,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_42,c_8457])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n006.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:04:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.64/2.77  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.64/2.78  
% 6.64/2.78  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.64/2.79  %$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 6.64/2.79  
% 6.64/2.79  %Foreground sorts:
% 6.64/2.79  
% 6.64/2.79  
% 6.64/2.79  %Background operators:
% 6.64/2.79  
% 6.64/2.79  
% 6.64/2.79  %Foreground operators:
% 6.64/2.79  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.64/2.79  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.64/2.79  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.64/2.79  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.64/2.79  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 6.64/2.79  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 6.64/2.79  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.64/2.79  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.64/2.79  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.64/2.79  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.64/2.79  tff('#skF_2', type, '#skF_2': $i).
% 6.64/2.79  tff('#skF_3', type, '#skF_3': $i).
% 6.64/2.79  tff('#skF_1', type, '#skF_1': $i).
% 6.64/2.79  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.64/2.79  tff(k3_tarski, type, k3_tarski: $i > $i).
% 6.64/2.79  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.64/2.79  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.64/2.79  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.64/2.79  
% 6.64/2.82  tff(f_70, negated_conjecture, ~(![A, B, C]: ((r2_hidden(A, B) & r2_hidden(C, B)) => (k2_xboole_0(k2_tarski(A, C), B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_zfmisc_1)).
% 6.64/2.82  tff(f_35, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 6.64/2.82  tff(f_45, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 6.64/2.82  tff(f_41, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 6.64/2.82  tff(f_39, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 6.64/2.82  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 6.64/2.82  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 6.64/2.82  tff(f_49, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 6.64/2.82  tff(f_57, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 6.64/2.82  tff(f_47, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_xboole_1)).
% 6.64/2.82  tff(f_63, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 6.64/2.82  tff(f_43, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 6.64/2.82  tff(c_40, plain, (r2_hidden('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_70])).
% 6.64/2.82  tff(c_42, plain, (r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_70])).
% 6.64/2.82  tff(c_10, plain, (![A_5]: (k2_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.64/2.82  tff(c_18, plain, (![A_11]: (k4_xboole_0(A_11, k1_xboole_0)=A_11)), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.64/2.82  tff(c_14, plain, (![A_8]: (r1_tarski(k1_xboole_0, A_8))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.64/2.82  tff(c_106, plain, (![A_38, B_39]: (k3_xboole_0(A_38, B_39)=A_38 | ~r1_tarski(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.64/2.82  tff(c_113, plain, (![A_8]: (k3_xboole_0(k1_xboole_0, A_8)=k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_106])).
% 6.64/2.82  tff(c_327, plain, (![A_54, B_55]: (k5_xboole_0(A_54, k3_xboole_0(A_54, B_55))=k4_xboole_0(A_54, B_55))), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.64/2.82  tff(c_364, plain, (![A_58]: (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, A_58))), inference(superposition, [status(thm), theory('equality')], [c_113, c_327])).
% 6.64/2.82  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.64/2.82  tff(c_114, plain, (![B_2]: (k3_xboole_0(B_2, B_2)=B_2)), inference(resolution, [status(thm)], [c_6, c_106])).
% 6.64/2.82  tff(c_336, plain, (![B_2]: (k5_xboole_0(B_2, B_2)=k4_xboole_0(B_2, B_2))), inference(superposition, [status(thm), theory('equality')], [c_114, c_327])).
% 6.64/2.82  tff(c_370, plain, (![A_58]: (k4_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, A_58))), inference(superposition, [status(thm), theory('equality')], [c_364, c_336])).
% 6.64/2.82  tff(c_383, plain, (![A_58]: (k4_xboole_0(k1_xboole_0, A_58)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_370])).
% 6.64/2.82  tff(c_22, plain, (![B_15, A_14]: (k2_tarski(B_15, A_14)=k2_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.64/2.82  tff(c_141, plain, (![A_42, B_43]: (k3_tarski(k2_tarski(A_42, B_43))=k2_xboole_0(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.64/2.82  tff(c_156, plain, (![B_44, A_45]: (k3_tarski(k2_tarski(B_44, A_45))=k2_xboole_0(A_45, B_44))), inference(superposition, [status(thm), theory('equality')], [c_22, c_141])).
% 6.64/2.82  tff(c_30, plain, (![A_25, B_26]: (k3_tarski(k2_tarski(A_25, B_26))=k2_xboole_0(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.64/2.82  tff(c_180, plain, (![B_46, A_47]: (k2_xboole_0(B_46, A_47)=k2_xboole_0(A_47, B_46))), inference(superposition, [status(thm), theory('equality')], [c_156, c_30])).
% 6.64/2.82  tff(c_256, plain, (![A_50]: (k2_xboole_0(k1_xboole_0, A_50)=A_50)), inference(superposition, [status(thm), theory('equality')], [c_180, c_10])).
% 6.64/2.82  tff(c_20, plain, (![A_12, B_13]: (k4_xboole_0(k2_xboole_0(A_12, B_13), B_13)=k4_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.64/2.82  tff(c_262, plain, (![A_50]: (k4_xboole_0(k1_xboole_0, A_50)=k4_xboole_0(A_50, A_50))), inference(superposition, [status(thm), theory('equality')], [c_256, c_20])).
% 6.64/2.82  tff(c_399, plain, (![A_50]: (k4_xboole_0(A_50, A_50)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_383, c_262])).
% 6.64/2.82  tff(c_430, plain, (![B_2]: (k5_xboole_0(B_2, B_2)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_399, c_336])).
% 6.64/2.82  tff(c_578, plain, (![A_78, B_79, C_80]: (r1_tarski(k2_tarski(A_78, B_79), C_80) | ~r2_hidden(B_79, C_80) | ~r2_hidden(A_78, C_80))), inference(cnfTransformation, [status(thm)], [f_63])).
% 6.64/2.82  tff(c_12, plain, (![A_6, B_7]: (k3_xboole_0(A_6, B_7)=A_6 | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.64/2.82  tff(c_2086, plain, (![A_117, B_118, C_119]: (k3_xboole_0(k2_tarski(A_117, B_118), C_119)=k2_tarski(A_117, B_118) | ~r2_hidden(B_118, C_119) | ~r2_hidden(A_117, C_119))), inference(resolution, [status(thm)], [c_578, c_12])).
% 6.64/2.82  tff(c_3833, plain, (![A_139, B_140, C_141]: (k3_xboole_0(k2_tarski(A_139, B_140), C_141)=k2_tarski(B_140, A_139) | ~r2_hidden(A_139, C_141) | ~r2_hidden(B_140, C_141))), inference(superposition, [status(thm), theory('equality')], [c_22, c_2086])).
% 6.64/2.82  tff(c_8, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k3_xboole_0(A_3, B_4))=k4_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.64/2.82  tff(c_4503, plain, (![A_149, B_150, C_151]: (k5_xboole_0(k2_tarski(A_149, B_150), k2_tarski(B_150, A_149))=k4_xboole_0(k2_tarski(A_149, B_150), C_151) | ~r2_hidden(A_149, C_151) | ~r2_hidden(B_150, C_151))), inference(superposition, [status(thm), theory('equality')], [c_3833, c_8])).
% 6.64/2.82  tff(c_16, plain, (![A_9, B_10]: (k2_xboole_0(A_9, k4_xboole_0(B_10, A_9))=k2_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.64/2.82  tff(c_5253, plain, (![C_163, A_164, B_165]: (k2_xboole_0(C_163, k5_xboole_0(k2_tarski(A_164, B_165), k2_tarski(B_165, A_164)))=k2_xboole_0(C_163, k2_tarski(A_164, B_165)) | ~r2_hidden(A_164, C_163) | ~r2_hidden(B_165, C_163))), inference(superposition, [status(thm), theory('equality')], [c_4503, c_16])).
% 6.64/2.82  tff(c_5435, plain, (![C_163, A_14, B_15]: (k2_xboole_0(C_163, k5_xboole_0(k2_tarski(A_14, B_15), k2_tarski(A_14, B_15)))=k2_xboole_0(C_163, k2_tarski(B_15, A_14)) | ~r2_hidden(B_15, C_163) | ~r2_hidden(A_14, C_163))), inference(superposition, [status(thm), theory('equality')], [c_22, c_5253])).
% 6.64/2.82  tff(c_8319, plain, (![C_202, B_203, A_204]: (k2_xboole_0(C_202, k2_tarski(B_203, A_204))=C_202 | ~r2_hidden(B_203, C_202) | ~r2_hidden(A_204, C_202))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_430, c_5435])).
% 6.64/2.82  tff(c_162, plain, (![B_44, A_45]: (k2_xboole_0(B_44, A_45)=k2_xboole_0(A_45, B_44))), inference(superposition, [status(thm), theory('equality')], [c_156, c_30])).
% 6.64/2.82  tff(c_38, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_3'), '#skF_2')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_70])).
% 6.64/2.82  tff(c_179, plain, (k2_xboole_0('#skF_2', k2_tarski('#skF_1', '#skF_3'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_162, c_38])).
% 6.64/2.82  tff(c_8457, plain, (~r2_hidden('#skF_1', '#skF_2') | ~r2_hidden('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_8319, c_179])).
% 6.64/2.82  tff(c_8548, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_42, c_8457])).
% 6.64/2.82  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.64/2.82  
% 6.64/2.82  Inference rules
% 6.64/2.82  ----------------------
% 6.64/2.82  #Ref     : 0
% 6.64/2.82  #Sup     : 2108
% 6.64/2.82  #Fact    : 0
% 6.64/2.82  #Define  : 0
% 6.64/2.82  #Split   : 0
% 6.64/2.82  #Chain   : 0
% 6.64/2.82  #Close   : 0
% 6.64/2.82  
% 6.64/2.82  Ordering : KBO
% 6.64/2.82  
% 6.64/2.82  Simplification rules
% 6.64/2.82  ----------------------
% 6.64/2.82  #Subsume      : 192
% 6.64/2.82  #Demod        : 4134
% 6.64/2.82  #Tautology    : 1410
% 6.64/2.82  #SimpNegUnit  : 0
% 6.64/2.82  #BackRed      : 4
% 6.64/2.82  
% 6.64/2.82  #Partial instantiations: 0
% 6.64/2.82  #Strategies tried      : 1
% 6.64/2.82  
% 6.64/2.82  Timing (in seconds)
% 6.64/2.82  ----------------------
% 7.00/2.82  Preprocessing        : 0.30
% 7.00/2.82  Parsing              : 0.16
% 7.00/2.82  CNF conversion       : 0.02
% 7.00/2.82  Main loop            : 1.72
% 7.00/2.82  Inferencing          : 0.38
% 7.00/2.82  Reduction            : 1.05
% 7.00/2.82  Demodulation         : 0.95
% 7.00/2.82  BG Simplification    : 0.04
% 7.00/2.82  Subsumption          : 0.19
% 7.00/2.82  Abstraction          : 0.09
% 7.00/2.82  MUC search           : 0.00
% 7.00/2.82  Cooper               : 0.00
% 7.00/2.82  Total                : 2.08
% 7.00/2.82  Index Insertion      : 0.00
% 7.00/2.82  Index Deletion       : 0.00
% 7.00/2.82  Index Matching       : 0.00
% 7.00/2.82  BG Taut test         : 0.00
%------------------------------------------------------------------------------
