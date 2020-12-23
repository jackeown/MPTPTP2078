%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:15 EST 2020

% Result     : Theorem 5.22s
% Output     : CNFRefutation 5.31s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 156 expanded)
%              Number of leaves         :   31 (  65 expanded)
%              Depth                    :   14
%              Number of atoms          :   79 ( 178 expanded)
%              Number of equality atoms :   46 (  96 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r1_xboole_0 > r1_tarski > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > o_0_0_xboole_0 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_37,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_39,axiom,(
    ? [A] : v1_xboole_0(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_xboole_0)).

tff(f_69,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_boole)).

tff(f_65,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_75,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_57,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_84,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(A,k4_xboole_0(B,C))
       => ( r1_tarski(A,B)
          & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_43,axiom,(
    ! [A,B,C] : k3_xboole_0(k3_xboole_0(A,B),C) = k3_xboole_0(A,k3_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_xboole_0(A,k4_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_xboole_1)).

tff(c_12,plain,(
    ! [A_5] : k3_xboole_0(A_5,A_5) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_118,plain,(
    ! [A_46,B_47] : r1_tarski(k3_xboole_0(A_46,B_47),A_46) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_121,plain,(
    ! [A_5] : r1_tarski(A_5,A_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_118])).

tff(c_14,plain,(
    v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_68,plain,(
    ! [A_40] :
      ( k1_xboole_0 = A_40
      | ~ v1_xboole_0(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_72,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_14,c_68])).

tff(c_34,plain,(
    ! [A_29] : k5_xboole_0(A_29,k1_xboole_0) = A_29 ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_84,plain,(
    ! [A_29] : k5_xboole_0(A_29,'#skF_1') = A_29 ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_34])).

tff(c_40,plain,(
    ! [A_34] : k5_xboole_0(A_34,A_34) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_74,plain,(
    ! [A_34] : k5_xboole_0(A_34,A_34) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_40])).

tff(c_3517,plain,(
    ! [A_162,B_163] : k5_xboole_0(A_162,k3_xboole_0(A_162,B_163)) = k4_xboole_0(A_162,B_163) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_3544,plain,(
    ! [A_5] : k5_xboole_0(A_5,A_5) = k4_xboole_0(A_5,A_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_3517])).

tff(c_3551,plain,(
    ! [A_164] : k4_xboole_0(A_164,A_164) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_3544])).

tff(c_28,plain,(
    ! [A_21,B_22] : r1_tarski(k4_xboole_0(A_21,B_22),A_21) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_3564,plain,(
    ! [A_165] : r1_tarski('#skF_1',A_165) ),
    inference(superposition,[status(thm),theory(equality)],[c_3551,c_28])).

tff(c_26,plain,(
    ! [A_19,B_20] :
      ( k3_xboole_0(A_19,B_20) = A_19
      | ~ r1_tarski(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_3568,plain,(
    ! [A_165] : k3_xboole_0('#skF_1',A_165) = '#skF_1' ),
    inference(resolution,[status(thm)],[c_3564,c_26])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_30,plain,(
    ! [A_23,B_24,C_25] : k4_xboole_0(k3_xboole_0(A_23,B_24),C_25) = k3_xboole_0(A_23,k4_xboole_0(B_24,C_25)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_20,plain,(
    ! [A_12,B_13] : r1_tarski(k3_xboole_0(A_12,B_13),A_12) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_3432,plain,(
    ! [A_155,B_156] :
      ( k3_xboole_0(A_155,B_156) = A_155
      | ~ r1_tarski(A_155,B_156) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_4112,plain,(
    ! [A_194,B_195] : k3_xboole_0(k3_xboole_0(A_194,B_195),A_194) = k3_xboole_0(A_194,B_195) ),
    inference(resolution,[status(thm)],[c_20,c_3432])).

tff(c_16,plain,(
    ! [A_7,B_8] : k5_xboole_0(A_7,k3_xboole_0(A_7,B_8)) = k4_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_4128,plain,(
    ! [A_194,B_195] : k5_xboole_0(k3_xboole_0(A_194,B_195),k3_xboole_0(A_194,B_195)) = k4_xboole_0(k3_xboole_0(A_194,B_195),A_194) ),
    inference(superposition,[status(thm),theory(equality)],[c_4112,c_16])).

tff(c_4211,plain,(
    ! [A_197,B_198] : k3_xboole_0(A_197,k4_xboole_0(B_198,A_197)) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_74,c_4128])).

tff(c_4225,plain,(
    ! [A_197,B_198] : k4_xboole_0(A_197,k4_xboole_0(B_198,A_197)) = k5_xboole_0(A_197,'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_4211,c_16])).

tff(c_4273,plain,(
    ! [A_199,B_200] : k4_xboole_0(A_199,k4_xboole_0(B_200,A_199)) = A_199 ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_4225])).

tff(c_4190,plain,(
    ! [A_194,B_195] : k3_xboole_0(A_194,k4_xboole_0(B_195,A_194)) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_74,c_4128])).

tff(c_4282,plain,(
    ! [B_200,A_199] : k3_xboole_0(k4_xboole_0(B_200,A_199),A_199) = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_4273,c_4190])).

tff(c_46,plain,(
    r1_tarski('#skF_2',k4_xboole_0('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_3457,plain,(
    k3_xboole_0('#skF_2',k4_xboole_0('#skF_3','#skF_4')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_46,c_3432])).

tff(c_4558,plain,(
    ! [A_208,B_209,C_210] : k3_xboole_0(k3_xboole_0(A_208,B_209),C_210) = k3_xboole_0(A_208,k3_xboole_0(B_209,C_210)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_5983,plain,(
    ! [C_239] : k3_xboole_0('#skF_2',k3_xboole_0(k4_xboole_0('#skF_3','#skF_4'),C_239)) = k3_xboole_0('#skF_2',C_239) ),
    inference(superposition,[status(thm),theory(equality)],[c_3457,c_4558])).

tff(c_6044,plain,(
    k3_xboole_0('#skF_2','#skF_1') = k3_xboole_0('#skF_2','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_4282,c_5983])).

tff(c_6084,plain,(
    k3_xboole_0('#skF_4','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3568,c_2,c_2,c_6044])).

tff(c_6122,plain,(
    k5_xboole_0('#skF_4','#skF_1') = k4_xboole_0('#skF_4','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_6084,c_16])).

tff(c_6142,plain,(
    k4_xboole_0('#skF_4','#skF_2') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_6122])).

tff(c_38,plain,(
    ! [A_31,C_33,B_32] :
      ( r1_xboole_0(A_31,k4_xboole_0(C_33,B_32))
      | ~ r1_tarski(A_31,B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_6602,plain,(
    ! [A_244] :
      ( r1_xboole_0(A_244,'#skF_4')
      | ~ r1_tarski(A_244,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6142,c_38])).

tff(c_44,plain,
    ( ~ r1_xboole_0('#skF_2','#skF_4')
    | ~ r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_192,plain,(
    ~ r1_tarski('#skF_2','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_195,plain,(
    ! [A_59,B_60] :
      ( k3_xboole_0(A_59,B_60) = A_59
      | ~ r1_tarski(A_59,B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_221,plain,(
    k3_xboole_0('#skF_2',k4_xboole_0('#skF_3','#skF_4')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_46,c_195])).

tff(c_3219,plain,(
    ! [A_153,B_154] : k3_xboole_0(k4_xboole_0(A_153,B_154),A_153) = k4_xboole_0(A_153,B_154) ),
    inference(resolution,[status(thm)],[c_28,c_195])).

tff(c_706,plain,(
    ! [A_88,B_89,C_90] : k3_xboole_0(k3_xboole_0(A_88,B_89),C_90) = k3_xboole_0(A_88,k3_xboole_0(B_89,C_90)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_758,plain,(
    ! [C_90] : k3_xboole_0('#skF_2',k3_xboole_0(k4_xboole_0('#skF_3','#skF_4'),C_90)) = k3_xboole_0('#skF_2',C_90) ),
    inference(superposition,[status(thm),theory(equality)],[c_221,c_706])).

tff(c_3230,plain,(
    k3_xboole_0('#skF_2',k4_xboole_0('#skF_3','#skF_4')) = k3_xboole_0('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_3219,c_758])).

tff(c_3348,plain,(
    k3_xboole_0('#skF_3','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_221,c_2,c_3230])).

tff(c_3418,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_3348,c_20])).

tff(c_3429,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_192,c_3418])).

tff(c_3430,plain,(
    ~ r1_xboole_0('#skF_2','#skF_4') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_6605,plain,(
    ~ r1_tarski('#skF_2','#skF_2') ),
    inference(resolution,[status(thm)],[c_6602,c_3430])).

tff(c_6609,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_6605])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.33  % Computer   : n016.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % DateTime   : Tue Dec  1 18:31:49 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.22/2.06  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.22/2.07  
% 5.22/2.07  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.22/2.07  %$ r2_xboole_0 > r1_xboole_0 > r1_tarski > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > o_0_0_xboole_0 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 5.22/2.07  
% 5.22/2.07  %Foreground sorts:
% 5.22/2.07  
% 5.22/2.07  
% 5.22/2.07  %Background operators:
% 5.22/2.07  
% 5.22/2.07  
% 5.22/2.07  %Foreground operators:
% 5.22/2.07  tff(o_0_0_xboole_0, type, o_0_0_xboole_0: $i).
% 5.22/2.07  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.22/2.07  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.22/2.07  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.22/2.07  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.22/2.07  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.22/2.07  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 5.22/2.07  tff('#skF_2', type, '#skF_2': $i).
% 5.22/2.07  tff('#skF_3', type, '#skF_3': $i).
% 5.22/2.07  tff('#skF_1', type, '#skF_1': $i).
% 5.22/2.07  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 5.22/2.07  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.22/2.07  tff('#skF_4', type, '#skF_4': $i).
% 5.22/2.07  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.22/2.07  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.22/2.07  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.22/2.07  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.22/2.07  
% 5.31/2.09  tff(f_37, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 5.31/2.09  tff(f_45, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 5.31/2.09  tff(f_39, axiom, (?[A]: v1_xboole_0(A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc1_xboole_0)).
% 5.31/2.09  tff(f_69, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_boole)).
% 5.31/2.09  tff(f_65, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 5.31/2.09  tff(f_75, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 5.31/2.09  tff(f_41, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 5.31/2.09  tff(f_55, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 5.31/2.09  tff(f_53, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 5.31/2.09  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 5.31/2.09  tff(f_57, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_xboole_1)).
% 5.31/2.09  tff(f_84, negated_conjecture, ~(![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_xboole_1)).
% 5.31/2.09  tff(f_43, axiom, (![A, B, C]: (k3_xboole_0(k3_xboole_0(A, B), C) = k3_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_xboole_1)).
% 5.31/2.09  tff(f_73, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_xboole_0(A, k4_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t85_xboole_1)).
% 5.31/2.09  tff(c_12, plain, (![A_5]: (k3_xboole_0(A_5, A_5)=A_5)), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.31/2.09  tff(c_118, plain, (![A_46, B_47]: (r1_tarski(k3_xboole_0(A_46, B_47), A_46))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.31/2.09  tff(c_121, plain, (![A_5]: (r1_tarski(A_5, A_5))), inference(superposition, [status(thm), theory('equality')], [c_12, c_118])).
% 5.31/2.09  tff(c_14, plain, (v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.31/2.09  tff(c_68, plain, (![A_40]: (k1_xboole_0=A_40 | ~v1_xboole_0(A_40))), inference(cnfTransformation, [status(thm)], [f_69])).
% 5.31/2.09  tff(c_72, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_14, c_68])).
% 5.31/2.09  tff(c_34, plain, (![A_29]: (k5_xboole_0(A_29, k1_xboole_0)=A_29)), inference(cnfTransformation, [status(thm)], [f_65])).
% 5.31/2.09  tff(c_84, plain, (![A_29]: (k5_xboole_0(A_29, '#skF_1')=A_29)), inference(demodulation, [status(thm), theory('equality')], [c_72, c_34])).
% 5.31/2.09  tff(c_40, plain, (![A_34]: (k5_xboole_0(A_34, A_34)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_75])).
% 5.31/2.09  tff(c_74, plain, (![A_34]: (k5_xboole_0(A_34, A_34)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_40])).
% 5.31/2.09  tff(c_3517, plain, (![A_162, B_163]: (k5_xboole_0(A_162, k3_xboole_0(A_162, B_163))=k4_xboole_0(A_162, B_163))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.31/2.09  tff(c_3544, plain, (![A_5]: (k5_xboole_0(A_5, A_5)=k4_xboole_0(A_5, A_5))), inference(superposition, [status(thm), theory('equality')], [c_12, c_3517])).
% 5.31/2.09  tff(c_3551, plain, (![A_164]: (k4_xboole_0(A_164, A_164)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_3544])).
% 5.31/2.09  tff(c_28, plain, (![A_21, B_22]: (r1_tarski(k4_xboole_0(A_21, B_22), A_21))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.31/2.09  tff(c_3564, plain, (![A_165]: (r1_tarski('#skF_1', A_165))), inference(superposition, [status(thm), theory('equality')], [c_3551, c_28])).
% 5.31/2.09  tff(c_26, plain, (![A_19, B_20]: (k3_xboole_0(A_19, B_20)=A_19 | ~r1_tarski(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.31/2.09  tff(c_3568, plain, (![A_165]: (k3_xboole_0('#skF_1', A_165)='#skF_1')), inference(resolution, [status(thm)], [c_3564, c_26])).
% 5.31/2.09  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.31/2.09  tff(c_30, plain, (![A_23, B_24, C_25]: (k4_xboole_0(k3_xboole_0(A_23, B_24), C_25)=k3_xboole_0(A_23, k4_xboole_0(B_24, C_25)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.31/2.09  tff(c_20, plain, (![A_12, B_13]: (r1_tarski(k3_xboole_0(A_12, B_13), A_12))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.31/2.09  tff(c_3432, plain, (![A_155, B_156]: (k3_xboole_0(A_155, B_156)=A_155 | ~r1_tarski(A_155, B_156))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.31/2.09  tff(c_4112, plain, (![A_194, B_195]: (k3_xboole_0(k3_xboole_0(A_194, B_195), A_194)=k3_xboole_0(A_194, B_195))), inference(resolution, [status(thm)], [c_20, c_3432])).
% 5.31/2.09  tff(c_16, plain, (![A_7, B_8]: (k5_xboole_0(A_7, k3_xboole_0(A_7, B_8))=k4_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.31/2.09  tff(c_4128, plain, (![A_194, B_195]: (k5_xboole_0(k3_xboole_0(A_194, B_195), k3_xboole_0(A_194, B_195))=k4_xboole_0(k3_xboole_0(A_194, B_195), A_194))), inference(superposition, [status(thm), theory('equality')], [c_4112, c_16])).
% 5.31/2.09  tff(c_4211, plain, (![A_197, B_198]: (k3_xboole_0(A_197, k4_xboole_0(B_198, A_197))='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_74, c_4128])).
% 5.31/2.09  tff(c_4225, plain, (![A_197, B_198]: (k4_xboole_0(A_197, k4_xboole_0(B_198, A_197))=k5_xboole_0(A_197, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_4211, c_16])).
% 5.31/2.09  tff(c_4273, plain, (![A_199, B_200]: (k4_xboole_0(A_199, k4_xboole_0(B_200, A_199))=A_199)), inference(demodulation, [status(thm), theory('equality')], [c_84, c_4225])).
% 5.31/2.09  tff(c_4190, plain, (![A_194, B_195]: (k3_xboole_0(A_194, k4_xboole_0(B_195, A_194))='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_74, c_4128])).
% 5.31/2.09  tff(c_4282, plain, (![B_200, A_199]: (k3_xboole_0(k4_xboole_0(B_200, A_199), A_199)='#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_4273, c_4190])).
% 5.31/2.09  tff(c_46, plain, (r1_tarski('#skF_2', k4_xboole_0('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_84])).
% 5.31/2.09  tff(c_3457, plain, (k3_xboole_0('#skF_2', k4_xboole_0('#skF_3', '#skF_4'))='#skF_2'), inference(resolution, [status(thm)], [c_46, c_3432])).
% 5.31/2.09  tff(c_4558, plain, (![A_208, B_209, C_210]: (k3_xboole_0(k3_xboole_0(A_208, B_209), C_210)=k3_xboole_0(A_208, k3_xboole_0(B_209, C_210)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.31/2.09  tff(c_5983, plain, (![C_239]: (k3_xboole_0('#skF_2', k3_xboole_0(k4_xboole_0('#skF_3', '#skF_4'), C_239))=k3_xboole_0('#skF_2', C_239))), inference(superposition, [status(thm), theory('equality')], [c_3457, c_4558])).
% 5.31/2.09  tff(c_6044, plain, (k3_xboole_0('#skF_2', '#skF_1')=k3_xboole_0('#skF_2', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_4282, c_5983])).
% 5.31/2.09  tff(c_6084, plain, (k3_xboole_0('#skF_4', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_3568, c_2, c_2, c_6044])).
% 5.31/2.09  tff(c_6122, plain, (k5_xboole_0('#skF_4', '#skF_1')=k4_xboole_0('#skF_4', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_6084, c_16])).
% 5.31/2.09  tff(c_6142, plain, (k4_xboole_0('#skF_4', '#skF_2')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_84, c_6122])).
% 5.31/2.09  tff(c_38, plain, (![A_31, C_33, B_32]: (r1_xboole_0(A_31, k4_xboole_0(C_33, B_32)) | ~r1_tarski(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_73])).
% 5.31/2.09  tff(c_6602, plain, (![A_244]: (r1_xboole_0(A_244, '#skF_4') | ~r1_tarski(A_244, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_6142, c_38])).
% 5.31/2.09  tff(c_44, plain, (~r1_xboole_0('#skF_2', '#skF_4') | ~r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_84])).
% 5.31/2.09  tff(c_192, plain, (~r1_tarski('#skF_2', '#skF_3')), inference(splitLeft, [status(thm)], [c_44])).
% 5.31/2.09  tff(c_195, plain, (![A_59, B_60]: (k3_xboole_0(A_59, B_60)=A_59 | ~r1_tarski(A_59, B_60))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.31/2.09  tff(c_221, plain, (k3_xboole_0('#skF_2', k4_xboole_0('#skF_3', '#skF_4'))='#skF_2'), inference(resolution, [status(thm)], [c_46, c_195])).
% 5.31/2.09  tff(c_3219, plain, (![A_153, B_154]: (k3_xboole_0(k4_xboole_0(A_153, B_154), A_153)=k4_xboole_0(A_153, B_154))), inference(resolution, [status(thm)], [c_28, c_195])).
% 5.31/2.09  tff(c_706, plain, (![A_88, B_89, C_90]: (k3_xboole_0(k3_xboole_0(A_88, B_89), C_90)=k3_xboole_0(A_88, k3_xboole_0(B_89, C_90)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.31/2.09  tff(c_758, plain, (![C_90]: (k3_xboole_0('#skF_2', k3_xboole_0(k4_xboole_0('#skF_3', '#skF_4'), C_90))=k3_xboole_0('#skF_2', C_90))), inference(superposition, [status(thm), theory('equality')], [c_221, c_706])).
% 5.31/2.09  tff(c_3230, plain, (k3_xboole_0('#skF_2', k4_xboole_0('#skF_3', '#skF_4'))=k3_xboole_0('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_3219, c_758])).
% 5.31/2.09  tff(c_3348, plain, (k3_xboole_0('#skF_3', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_221, c_2, c_3230])).
% 5.31/2.09  tff(c_3418, plain, (r1_tarski('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_3348, c_20])).
% 5.31/2.09  tff(c_3429, plain, $false, inference(negUnitSimplification, [status(thm)], [c_192, c_3418])).
% 5.31/2.09  tff(c_3430, plain, (~r1_xboole_0('#skF_2', '#skF_4')), inference(splitRight, [status(thm)], [c_44])).
% 5.31/2.09  tff(c_6605, plain, (~r1_tarski('#skF_2', '#skF_2')), inference(resolution, [status(thm)], [c_6602, c_3430])).
% 5.31/2.09  tff(c_6609, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_121, c_6605])).
% 5.31/2.09  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.31/2.09  
% 5.31/2.09  Inference rules
% 5.31/2.09  ----------------------
% 5.31/2.09  #Ref     : 0
% 5.31/2.09  #Sup     : 1662
% 5.31/2.09  #Fact    : 0
% 5.31/2.09  #Define  : 0
% 5.31/2.09  #Split   : 1
% 5.31/2.09  #Chain   : 0
% 5.31/2.09  #Close   : 0
% 5.31/2.09  
% 5.31/2.09  Ordering : KBO
% 5.31/2.09  
% 5.31/2.09  Simplification rules
% 5.31/2.09  ----------------------
% 5.31/2.09  #Subsume      : 11
% 5.31/2.09  #Demod        : 1282
% 5.31/2.09  #Tautology    : 1154
% 5.31/2.09  #SimpNegUnit  : 1
% 5.31/2.09  #BackRed      : 3
% 5.31/2.09  
% 5.31/2.09  #Partial instantiations: 0
% 5.31/2.09  #Strategies tried      : 1
% 5.31/2.09  
% 5.31/2.09  Timing (in seconds)
% 5.31/2.09  ----------------------
% 5.31/2.09  Preprocessing        : 0.37
% 5.31/2.09  Parsing              : 0.18
% 5.31/2.09  CNF conversion       : 0.03
% 5.31/2.09  Main loop            : 0.95
% 5.31/2.09  Inferencing          : 0.29
% 5.31/2.09  Reduction            : 0.42
% 5.31/2.09  Demodulation         : 0.33
% 5.31/2.09  BG Simplification    : 0.03
% 5.31/2.09  Subsumption          : 0.13
% 5.31/2.09  Abstraction          : 0.04
% 5.31/2.09  MUC search           : 0.00
% 5.31/2.09  Cooper               : 0.00
% 5.31/2.09  Total                : 1.36
% 5.31/2.09  Index Insertion      : 0.00
% 5.31/2.09  Index Deletion       : 0.00
% 5.31/2.09  Index Matching       : 0.00
% 5.31/2.09  BG Taut test         : 0.00
%------------------------------------------------------------------------------
