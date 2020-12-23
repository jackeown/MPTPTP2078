%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:54 EST 2020

% Result     : Theorem 7.90s
% Output     : CNFRefutation 7.90s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 188 expanded)
%              Number of leaves         :   28 (  73 expanded)
%              Depth                    :   13
%              Number of atoms          :  100 ( 239 expanded)
%              Number of equality atoms :   49 ( 129 expanded)
%              Maximal formula depth    :    9 (   3 average)
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

tff(f_67,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_98,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r1_tarski(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,C) )
       => r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_73,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_71,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_79,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_77,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_75,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_69,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_49,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_91,axiom,(
    ! [A] :
      ( ~ ( ~ r1_xboole_0(A,A)
          & A = k1_xboole_0 )
      & ~ ( A != k1_xboole_0
          & r1_xboole_0(A,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).

tff(c_103,plain,(
    ! [A_36,B_37] :
      ( r1_tarski(A_36,B_37)
      | k4_xboole_0(A_36,B_37) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_38,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_111,plain,(
    k4_xboole_0('#skF_3','#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_103,c_38])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_527,plain,(
    ! [A_74,B_75] : k4_xboole_0(k2_xboole_0(A_74,B_75),B_75) = k4_xboole_0(A_74,B_75) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_564,plain,(
    ! [B_2,A_1] : k4_xboole_0(k2_xboole_0(B_2,A_1),B_2) = k4_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_527])).

tff(c_24,plain,(
    ! [A_19] : k4_xboole_0(A_19,k1_xboole_0) = A_19 ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_540,plain,(
    ! [A_74] : k4_xboole_0(A_74,k1_xboole_0) = k2_xboole_0(A_74,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_527,c_24])).

tff(c_574,plain,(
    ! [A_74] : k2_xboole_0(A_74,k1_xboole_0) = A_74 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_540])).

tff(c_32,plain,(
    ! [A_27] : r1_xboole_0(A_27,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_119,plain,(
    ! [A_41,B_42] :
      ( k3_xboole_0(A_41,B_42) = k1_xboole_0
      | ~ r1_xboole_0(A_41,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_130,plain,(
    ! [A_27] : k3_xboole_0(A_27,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_32,c_119])).

tff(c_145,plain,(
    ! [A_44,B_45] : k4_xboole_0(A_44,k4_xboole_0(A_44,B_45)) = k3_xboole_0(A_44,B_45) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_163,plain,(
    ! [A_19] : k4_xboole_0(A_19,A_19) = k3_xboole_0(A_19,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_145])).

tff(c_167,plain,(
    ! [A_19] : k4_xboole_0(A_19,A_19) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_163])).

tff(c_724,plain,(
    ! [A_83,B_84,C_85] : k4_xboole_0(k4_xboole_0(A_83,B_84),C_85) = k4_xboole_0(A_83,k2_xboole_0(B_84,C_85)) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_22,plain,(
    ! [A_17,B_18] : k2_xboole_0(A_17,k4_xboole_0(B_18,A_17)) = k2_xboole_0(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_4281,plain,(
    ! [C_188,A_189,B_190] : k2_xboole_0(C_188,k4_xboole_0(A_189,k2_xboole_0(B_190,C_188))) = k2_xboole_0(C_188,k4_xboole_0(A_189,B_190)) ),
    inference(superposition,[status(thm),theory(equality)],[c_724,c_22])).

tff(c_4475,plain,(
    ! [C_188,B_190] : k2_xboole_0(C_188,k4_xboole_0(k2_xboole_0(B_190,C_188),B_190)) = k2_xboole_0(C_188,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_167,c_4281])).

tff(c_4527,plain,(
    ! [C_188,B_190] : k2_xboole_0(C_188,k4_xboole_0(C_188,B_190)) = C_188 ),
    inference(demodulation,[status(thm),theory(equality)],[c_564,c_574,c_4475])).

tff(c_40,plain,(
    r1_xboole_0('#skF_3','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_131,plain,(
    k3_xboole_0('#skF_3','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_40,c_119])).

tff(c_30,plain,(
    ! [A_25,B_26] : k4_xboole_0(A_25,k4_xboole_0(A_25,B_26)) = k3_xboole_0(A_25,B_26) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_376,plain,(
    ! [A_66,B_67] : k2_xboole_0(A_66,k4_xboole_0(B_67,A_66)) = k2_xboole_0(A_66,B_67) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_388,plain,(
    ! [A_25,B_26] : k2_xboole_0(k4_xboole_0(A_25,B_26),k3_xboole_0(A_25,B_26)) = k2_xboole_0(k4_xboole_0(A_25,B_26),A_25) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_376])).

tff(c_3195,plain,(
    ! [A_164,B_165] : k2_xboole_0(k4_xboole_0(A_164,B_165),k3_xboole_0(A_164,B_165)) = k2_xboole_0(A_164,k4_xboole_0(A_164,B_165)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_388])).

tff(c_3341,plain,(
    k2_xboole_0(k4_xboole_0('#skF_3','#skF_5'),k1_xboole_0) = k2_xboole_0('#skF_3',k4_xboole_0('#skF_3','#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_131,c_3195])).

tff(c_3391,plain,(
    k2_xboole_0('#skF_3',k4_xboole_0('#skF_3','#skF_5')) = k4_xboole_0('#skF_3','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_574,c_3341])).

tff(c_4529,plain,(
    k4_xboole_0('#skF_3','#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4527,c_3391])).

tff(c_28,plain,(
    ! [A_22,B_23,C_24] : k4_xboole_0(k4_xboole_0(A_22,B_23),C_24) = k4_xboole_0(A_22,k2_xboole_0(B_23,C_24)) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_16239,plain,(
    ! [C_315] : k4_xboole_0('#skF_3',k2_xboole_0('#skF_5',C_315)) = k4_xboole_0('#skF_3',C_315) ),
    inference(superposition,[status(thm),theory(equality)],[c_4529,c_28])).

tff(c_217,plain,(
    ! [A_48,B_49,C_50] :
      ( ~ r1_xboole_0(A_48,B_49)
      | ~ r2_hidden(C_50,k3_xboole_0(A_48,B_49)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_226,plain,(
    ! [C_50] :
      ( ~ r1_xboole_0('#skF_3','#skF_5')
      | ~ r2_hidden(C_50,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_131,c_217])).

tff(c_231,plain,(
    ! [C_50] : ~ r2_hidden(C_50,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_226])).

tff(c_385,plain,(
    ! [A_19] : k2_xboole_0(A_19,k1_xboole_0) = k2_xboole_0(A_19,A_19) ),
    inference(superposition,[status(thm),theory(equality)],[c_167,c_376])).

tff(c_594,plain,(
    ! [A_19] : k2_xboole_0(A_19,A_19) = A_19 ),
    inference(demodulation,[status(thm),theory(equality)],[c_574,c_385])).

tff(c_7930,plain,(
    ! [A_229,B_230,C_231] : k4_xboole_0(k4_xboole_0(A_229,B_230),k4_xboole_0(A_229,k2_xboole_0(B_230,C_231))) = k3_xboole_0(k4_xboole_0(A_229,B_230),C_231) ),
    inference(superposition,[status(thm),theory(equality)],[c_724,c_30])).

tff(c_8165,plain,(
    ! [A_229,A_19] : k4_xboole_0(k4_xboole_0(A_229,A_19),k4_xboole_0(A_229,A_19)) = k3_xboole_0(k4_xboole_0(A_229,A_19),A_19) ),
    inference(superposition,[status(thm),theory(equality)],[c_594,c_7930])).

tff(c_8344,plain,(
    ! [A_232,A_233] : k3_xboole_0(k4_xboole_0(A_232,A_233),A_233) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_167,c_8165])).

tff(c_14,plain,(
    ! [A_10,B_11] :
      ( r2_hidden('#skF_2'(A_10,B_11),k3_xboole_0(A_10,B_11))
      | r1_xboole_0(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_8379,plain,(
    ! [A_232,A_233] :
      ( r2_hidden('#skF_2'(k4_xboole_0(A_232,A_233),A_233),k1_xboole_0)
      | r1_xboole_0(k4_xboole_0(A_232,A_233),A_233) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8344,c_14])).

tff(c_8525,plain,(
    ! [A_234,A_235] : r1_xboole_0(k4_xboole_0(A_234,A_235),A_235) ),
    inference(negUnitSimplification,[status(thm)],[c_231,c_8379])).

tff(c_9993,plain,(
    ! [A_248,B_249,C_250] : r1_xboole_0(k4_xboole_0(A_248,k2_xboole_0(B_249,C_250)),C_250) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_8525])).

tff(c_10119,plain,(
    ! [A_248,A_1,B_2] : r1_xboole_0(k4_xboole_0(A_248,k2_xboole_0(A_1,B_2)),A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_9993])).

tff(c_16272,plain,(
    ! [C_315] : r1_xboole_0(k4_xboole_0('#skF_3',C_315),'#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_16239,c_10119])).

tff(c_42,plain,(
    r1_tarski('#skF_3',k2_xboole_0('#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_94,plain,(
    ! [A_34,B_35] :
      ( k4_xboole_0(A_34,B_35) = k1_xboole_0
      | ~ r1_tarski(A_34,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_98,plain,(
    k4_xboole_0('#skF_3',k2_xboole_0('#skF_4','#skF_5')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_42,c_94])).

tff(c_8191,plain,(
    k4_xboole_0(k4_xboole_0('#skF_3','#skF_4'),k1_xboole_0) = k3_xboole_0(k4_xboole_0('#skF_3','#skF_4'),'#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_98,c_7930])).

tff(c_8265,plain,(
    k3_xboole_0(k4_xboole_0('#skF_3','#skF_4'),'#skF_5') = k4_xboole_0('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_8191])).

tff(c_316,plain,(
    ! [A_62,B_63] :
      ( r2_hidden('#skF_1'(A_62,B_63),A_62)
      | r1_xboole_0(A_62,B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_16,plain,(
    ! [A_10,B_11,C_14] :
      ( ~ r1_xboole_0(A_10,B_11)
      | ~ r2_hidden(C_14,k3_xboole_0(A_10,B_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_330,plain,(
    ! [A_10,B_11,B_63] :
      ( ~ r1_xboole_0(A_10,B_11)
      | r1_xboole_0(k3_xboole_0(A_10,B_11),B_63) ) ),
    inference(resolution,[status(thm)],[c_316,c_16])).

tff(c_8300,plain,(
    ! [B_63] :
      ( ~ r1_xboole_0(k4_xboole_0('#skF_3','#skF_4'),'#skF_5')
      | r1_xboole_0(k4_xboole_0('#skF_3','#skF_4'),B_63) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8265,c_330])).

tff(c_14066,plain,(
    ~ r1_xboole_0(k4_xboole_0('#skF_3','#skF_4'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_8300])).

tff(c_16487,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16272,c_14066])).

tff(c_16490,plain,(
    ! [B_316] : r1_xboole_0(k4_xboole_0('#skF_3','#skF_4'),B_316) ),
    inference(splitRight,[status(thm)],[c_8300])).

tff(c_36,plain,(
    ! [A_28] :
      ( ~ r1_xboole_0(A_28,A_28)
      | k1_xboole_0 = A_28 ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_16520,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_16490,c_36])).

tff(c_16544,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_111,c_16520])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:19:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.18/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.90/3.03  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.90/3.03  
% 7.90/3.03  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.90/3.04  %$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 7.90/3.04  
% 7.90/3.04  %Foreground sorts:
% 7.90/3.04  
% 7.90/3.04  
% 7.90/3.04  %Background operators:
% 7.90/3.04  
% 7.90/3.04  
% 7.90/3.04  %Foreground operators:
% 7.90/3.04  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.90/3.04  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.90/3.04  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.90/3.04  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.90/3.04  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.90/3.04  tff('#skF_5', type, '#skF_5': $i).
% 7.90/3.04  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 7.90/3.04  tff('#skF_3', type, '#skF_3': $i).
% 7.90/3.04  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.90/3.04  tff('#skF_4', type, '#skF_4': $i).
% 7.90/3.04  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.90/3.04  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 7.90/3.04  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.90/3.04  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 7.90/3.04  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 7.90/3.04  
% 7.90/3.05  tff(f_67, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 7.90/3.05  tff(f_98, negated_conjecture, ~(![A, B, C]: ((r1_tarski(A, k2_xboole_0(B, C)) & r1_xboole_0(A, C)) => r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_xboole_1)).
% 7.90/3.05  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 7.90/3.05  tff(f_73, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_xboole_1)).
% 7.90/3.05  tff(f_71, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 7.90/3.05  tff(f_79, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 7.90/3.05  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 7.90/3.05  tff(f_77, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 7.90/3.05  tff(f_75, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 7.90/3.05  tff(f_69, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 7.90/3.05  tff(f_63, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 7.90/3.05  tff(f_49, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 7.90/3.05  tff(f_91, axiom, (![A]: (~(~r1_xboole_0(A, A) & (A = k1_xboole_0)) & ~(~(A = k1_xboole_0) & r1_xboole_0(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_xboole_1)).
% 7.90/3.05  tff(c_103, plain, (![A_36, B_37]: (r1_tarski(A_36, B_37) | k4_xboole_0(A_36, B_37)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_67])).
% 7.90/3.05  tff(c_38, plain, (~r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_98])).
% 7.90/3.05  tff(c_111, plain, (k4_xboole_0('#skF_3', '#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_103, c_38])).
% 7.90/3.05  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 7.90/3.05  tff(c_527, plain, (![A_74, B_75]: (k4_xboole_0(k2_xboole_0(A_74, B_75), B_75)=k4_xboole_0(A_74, B_75))), inference(cnfTransformation, [status(thm)], [f_73])).
% 7.90/3.05  tff(c_564, plain, (![B_2, A_1]: (k4_xboole_0(k2_xboole_0(B_2, A_1), B_2)=k4_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_527])).
% 7.90/3.05  tff(c_24, plain, (![A_19]: (k4_xboole_0(A_19, k1_xboole_0)=A_19)), inference(cnfTransformation, [status(thm)], [f_71])).
% 7.90/3.05  tff(c_540, plain, (![A_74]: (k4_xboole_0(A_74, k1_xboole_0)=k2_xboole_0(A_74, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_527, c_24])).
% 7.90/3.05  tff(c_574, plain, (![A_74]: (k2_xboole_0(A_74, k1_xboole_0)=A_74)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_540])).
% 7.90/3.05  tff(c_32, plain, (![A_27]: (r1_xboole_0(A_27, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_79])).
% 7.90/3.05  tff(c_119, plain, (![A_41, B_42]: (k3_xboole_0(A_41, B_42)=k1_xboole_0 | ~r1_xboole_0(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.90/3.05  tff(c_130, plain, (![A_27]: (k3_xboole_0(A_27, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_32, c_119])).
% 7.90/3.05  tff(c_145, plain, (![A_44, B_45]: (k4_xboole_0(A_44, k4_xboole_0(A_44, B_45))=k3_xboole_0(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_77])).
% 7.90/3.05  tff(c_163, plain, (![A_19]: (k4_xboole_0(A_19, A_19)=k3_xboole_0(A_19, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_24, c_145])).
% 7.90/3.05  tff(c_167, plain, (![A_19]: (k4_xboole_0(A_19, A_19)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_130, c_163])).
% 7.90/3.05  tff(c_724, plain, (![A_83, B_84, C_85]: (k4_xboole_0(k4_xboole_0(A_83, B_84), C_85)=k4_xboole_0(A_83, k2_xboole_0(B_84, C_85)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 7.90/3.05  tff(c_22, plain, (![A_17, B_18]: (k2_xboole_0(A_17, k4_xboole_0(B_18, A_17))=k2_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_69])).
% 7.90/3.05  tff(c_4281, plain, (![C_188, A_189, B_190]: (k2_xboole_0(C_188, k4_xboole_0(A_189, k2_xboole_0(B_190, C_188)))=k2_xboole_0(C_188, k4_xboole_0(A_189, B_190)))), inference(superposition, [status(thm), theory('equality')], [c_724, c_22])).
% 7.90/3.05  tff(c_4475, plain, (![C_188, B_190]: (k2_xboole_0(C_188, k4_xboole_0(k2_xboole_0(B_190, C_188), B_190))=k2_xboole_0(C_188, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_167, c_4281])).
% 7.90/3.05  tff(c_4527, plain, (![C_188, B_190]: (k2_xboole_0(C_188, k4_xboole_0(C_188, B_190))=C_188)), inference(demodulation, [status(thm), theory('equality')], [c_564, c_574, c_4475])).
% 7.90/3.05  tff(c_40, plain, (r1_xboole_0('#skF_3', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_98])).
% 7.90/3.05  tff(c_131, plain, (k3_xboole_0('#skF_3', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_40, c_119])).
% 7.90/3.05  tff(c_30, plain, (![A_25, B_26]: (k4_xboole_0(A_25, k4_xboole_0(A_25, B_26))=k3_xboole_0(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_77])).
% 7.90/3.05  tff(c_376, plain, (![A_66, B_67]: (k2_xboole_0(A_66, k4_xboole_0(B_67, A_66))=k2_xboole_0(A_66, B_67))), inference(cnfTransformation, [status(thm)], [f_69])).
% 7.90/3.05  tff(c_388, plain, (![A_25, B_26]: (k2_xboole_0(k4_xboole_0(A_25, B_26), k3_xboole_0(A_25, B_26))=k2_xboole_0(k4_xboole_0(A_25, B_26), A_25))), inference(superposition, [status(thm), theory('equality')], [c_30, c_376])).
% 7.90/3.05  tff(c_3195, plain, (![A_164, B_165]: (k2_xboole_0(k4_xboole_0(A_164, B_165), k3_xboole_0(A_164, B_165))=k2_xboole_0(A_164, k4_xboole_0(A_164, B_165)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_388])).
% 7.90/3.05  tff(c_3341, plain, (k2_xboole_0(k4_xboole_0('#skF_3', '#skF_5'), k1_xboole_0)=k2_xboole_0('#skF_3', k4_xboole_0('#skF_3', '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_131, c_3195])).
% 7.90/3.05  tff(c_3391, plain, (k2_xboole_0('#skF_3', k4_xboole_0('#skF_3', '#skF_5'))=k4_xboole_0('#skF_3', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_574, c_3341])).
% 7.90/3.05  tff(c_4529, plain, (k4_xboole_0('#skF_3', '#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_4527, c_3391])).
% 7.90/3.05  tff(c_28, plain, (![A_22, B_23, C_24]: (k4_xboole_0(k4_xboole_0(A_22, B_23), C_24)=k4_xboole_0(A_22, k2_xboole_0(B_23, C_24)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 7.90/3.05  tff(c_16239, plain, (![C_315]: (k4_xboole_0('#skF_3', k2_xboole_0('#skF_5', C_315))=k4_xboole_0('#skF_3', C_315))), inference(superposition, [status(thm), theory('equality')], [c_4529, c_28])).
% 7.90/3.05  tff(c_217, plain, (![A_48, B_49, C_50]: (~r1_xboole_0(A_48, B_49) | ~r2_hidden(C_50, k3_xboole_0(A_48, B_49)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 7.90/3.05  tff(c_226, plain, (![C_50]: (~r1_xboole_0('#skF_3', '#skF_5') | ~r2_hidden(C_50, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_131, c_217])).
% 7.90/3.05  tff(c_231, plain, (![C_50]: (~r2_hidden(C_50, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_226])).
% 7.90/3.05  tff(c_385, plain, (![A_19]: (k2_xboole_0(A_19, k1_xboole_0)=k2_xboole_0(A_19, A_19))), inference(superposition, [status(thm), theory('equality')], [c_167, c_376])).
% 7.90/3.05  tff(c_594, plain, (![A_19]: (k2_xboole_0(A_19, A_19)=A_19)), inference(demodulation, [status(thm), theory('equality')], [c_574, c_385])).
% 7.90/3.05  tff(c_7930, plain, (![A_229, B_230, C_231]: (k4_xboole_0(k4_xboole_0(A_229, B_230), k4_xboole_0(A_229, k2_xboole_0(B_230, C_231)))=k3_xboole_0(k4_xboole_0(A_229, B_230), C_231))), inference(superposition, [status(thm), theory('equality')], [c_724, c_30])).
% 7.90/3.05  tff(c_8165, plain, (![A_229, A_19]: (k4_xboole_0(k4_xboole_0(A_229, A_19), k4_xboole_0(A_229, A_19))=k3_xboole_0(k4_xboole_0(A_229, A_19), A_19))), inference(superposition, [status(thm), theory('equality')], [c_594, c_7930])).
% 7.90/3.05  tff(c_8344, plain, (![A_232, A_233]: (k3_xboole_0(k4_xboole_0(A_232, A_233), A_233)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_167, c_8165])).
% 7.90/3.05  tff(c_14, plain, (![A_10, B_11]: (r2_hidden('#skF_2'(A_10, B_11), k3_xboole_0(A_10, B_11)) | r1_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_63])).
% 7.90/3.05  tff(c_8379, plain, (![A_232, A_233]: (r2_hidden('#skF_2'(k4_xboole_0(A_232, A_233), A_233), k1_xboole_0) | r1_xboole_0(k4_xboole_0(A_232, A_233), A_233))), inference(superposition, [status(thm), theory('equality')], [c_8344, c_14])).
% 7.90/3.05  tff(c_8525, plain, (![A_234, A_235]: (r1_xboole_0(k4_xboole_0(A_234, A_235), A_235))), inference(negUnitSimplification, [status(thm)], [c_231, c_8379])).
% 7.90/3.05  tff(c_9993, plain, (![A_248, B_249, C_250]: (r1_xboole_0(k4_xboole_0(A_248, k2_xboole_0(B_249, C_250)), C_250))), inference(superposition, [status(thm), theory('equality')], [c_28, c_8525])).
% 7.90/3.05  tff(c_10119, plain, (![A_248, A_1, B_2]: (r1_xboole_0(k4_xboole_0(A_248, k2_xboole_0(A_1, B_2)), A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_9993])).
% 7.90/3.05  tff(c_16272, plain, (![C_315]: (r1_xboole_0(k4_xboole_0('#skF_3', C_315), '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_16239, c_10119])).
% 7.90/3.05  tff(c_42, plain, (r1_tarski('#skF_3', k2_xboole_0('#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_98])).
% 7.90/3.05  tff(c_94, plain, (![A_34, B_35]: (k4_xboole_0(A_34, B_35)=k1_xboole_0 | ~r1_tarski(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_67])).
% 7.90/3.05  tff(c_98, plain, (k4_xboole_0('#skF_3', k2_xboole_0('#skF_4', '#skF_5'))=k1_xboole_0), inference(resolution, [status(thm)], [c_42, c_94])).
% 7.90/3.05  tff(c_8191, plain, (k4_xboole_0(k4_xboole_0('#skF_3', '#skF_4'), k1_xboole_0)=k3_xboole_0(k4_xboole_0('#skF_3', '#skF_4'), '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_98, c_7930])).
% 7.90/3.05  tff(c_8265, plain, (k3_xboole_0(k4_xboole_0('#skF_3', '#skF_4'), '#skF_5')=k4_xboole_0('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_8191])).
% 7.90/3.05  tff(c_316, plain, (![A_62, B_63]: (r2_hidden('#skF_1'(A_62, B_63), A_62) | r1_xboole_0(A_62, B_63))), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.90/3.05  tff(c_16, plain, (![A_10, B_11, C_14]: (~r1_xboole_0(A_10, B_11) | ~r2_hidden(C_14, k3_xboole_0(A_10, B_11)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 7.90/3.05  tff(c_330, plain, (![A_10, B_11, B_63]: (~r1_xboole_0(A_10, B_11) | r1_xboole_0(k3_xboole_0(A_10, B_11), B_63))), inference(resolution, [status(thm)], [c_316, c_16])).
% 7.90/3.05  tff(c_8300, plain, (![B_63]: (~r1_xboole_0(k4_xboole_0('#skF_3', '#skF_4'), '#skF_5') | r1_xboole_0(k4_xboole_0('#skF_3', '#skF_4'), B_63))), inference(superposition, [status(thm), theory('equality')], [c_8265, c_330])).
% 7.90/3.05  tff(c_14066, plain, (~r1_xboole_0(k4_xboole_0('#skF_3', '#skF_4'), '#skF_5')), inference(splitLeft, [status(thm)], [c_8300])).
% 7.90/3.05  tff(c_16487, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16272, c_14066])).
% 7.90/3.05  tff(c_16490, plain, (![B_316]: (r1_xboole_0(k4_xboole_0('#skF_3', '#skF_4'), B_316))), inference(splitRight, [status(thm)], [c_8300])).
% 7.90/3.05  tff(c_36, plain, (![A_28]: (~r1_xboole_0(A_28, A_28) | k1_xboole_0=A_28)), inference(cnfTransformation, [status(thm)], [f_91])).
% 7.90/3.05  tff(c_16520, plain, (k4_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_16490, c_36])).
% 7.90/3.05  tff(c_16544, plain, $false, inference(negUnitSimplification, [status(thm)], [c_111, c_16520])).
% 7.90/3.05  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.90/3.05  
% 7.90/3.05  Inference rules
% 7.90/3.05  ----------------------
% 7.90/3.05  #Ref     : 1
% 7.90/3.05  #Sup     : 4306
% 7.90/3.05  #Fact    : 0
% 7.90/3.05  #Define  : 0
% 7.90/3.05  #Split   : 8
% 7.90/3.05  #Chain   : 0
% 7.90/3.05  #Close   : 0
% 7.90/3.05  
% 7.90/3.05  Ordering : KBO
% 7.90/3.05  
% 7.90/3.05  Simplification rules
% 7.90/3.05  ----------------------
% 7.90/3.05  #Subsume      : 895
% 7.90/3.05  #Demod        : 3647
% 7.90/3.05  #Tautology    : 2135
% 7.90/3.05  #SimpNegUnit  : 115
% 7.90/3.05  #BackRed      : 14
% 7.90/3.05  
% 7.90/3.05  #Partial instantiations: 0
% 7.90/3.05  #Strategies tried      : 1
% 7.90/3.05  
% 7.90/3.05  Timing (in seconds)
% 7.90/3.05  ----------------------
% 7.90/3.05  Preprocessing        : 0.29
% 7.90/3.05  Parsing              : 0.16
% 7.90/3.05  CNF conversion       : 0.02
% 7.90/3.05  Main loop            : 2.01
% 7.90/3.05  Inferencing          : 0.47
% 7.90/3.05  Reduction            : 1.05
% 7.90/3.05  Demodulation         : 0.89
% 7.90/3.05  BG Simplification    : 0.05
% 7.90/3.05  Subsumption          : 0.33
% 7.90/3.06  Abstraction          : 0.08
% 7.90/3.06  MUC search           : 0.00
% 7.90/3.06  Cooper               : 0.00
% 7.90/3.06  Total                : 2.33
% 7.90/3.06  Index Insertion      : 0.00
% 7.90/3.06  Index Deletion       : 0.00
% 7.90/3.06  Index Matching       : 0.00
% 7.90/3.06  BG Taut test         : 0.00
%------------------------------------------------------------------------------
