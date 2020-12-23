%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:38 EST 2020

% Result     : Theorem 16.23s
% Output     : CNFRefutation 16.23s
% Verified   : 
% Statistics : Number of formulae       :  136 ( 289 expanded)
%              Number of leaves         :   31 ( 104 expanded)
%              Depth                    :   11
%              Number of atoms          :  175 ( 505 expanded)
%              Number of equality atoms :   36 (  88 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_8 > #skF_4 > #skF_1

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

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_57,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_59,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_55,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_63,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_73,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_90,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
            & r1_xboole_0(A,B)
            & r1_xboole_0(A,C) )
        & ~ ( ~ ( r1_xboole_0(A,B)
                & r1_xboole_0(A,C) )
            & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).

tff(f_53,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_61,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_71,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

tff(c_14,plain,(
    ! [A_13] : k4_xboole_0(A_13,k1_xboole_0) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_729,plain,(
    ! [A_75,B_76,C_77] : k4_xboole_0(k4_xboole_0(A_75,B_76),C_77) = k4_xboole_0(A_75,k2_xboole_0(B_76,C_77)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_911,plain,(
    ! [A_85,C_86] : k4_xboole_0(A_85,k2_xboole_0(k1_xboole_0,C_86)) = k4_xboole_0(A_85,C_86) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_729])).

tff(c_12,plain,(
    ! [A_12] : k3_xboole_0(A_12,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_144,plain,(
    ! [A_44,B_45] : k4_xboole_0(A_44,k4_xboole_0(A_44,B_45)) = k3_xboole_0(A_44,B_45) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_159,plain,(
    ! [A_13] : k4_xboole_0(A_13,A_13) = k3_xboole_0(A_13,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_144])).

tff(c_162,plain,(
    ! [A_13] : k4_xboole_0(A_13,A_13) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_159])).

tff(c_984,plain,(
    ! [C_87] : k4_xboole_0(k2_xboole_0(k1_xboole_0,C_87),C_87) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_911,c_162])).

tff(c_1000,plain,(
    k2_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_984,c_14])).

tff(c_63,plain,(
    ! [B_34,A_35] : k2_xboole_0(B_34,A_35) = k2_xboole_0(A_35,B_34) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_26,plain,(
    ! [A_25,B_26] : r1_tarski(A_25,k2_xboole_0(A_25,B_26)) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_81,plain,(
    ! [B_34,A_35] : r1_tarski(B_34,k2_xboole_0(A_35,B_34)) ),
    inference(superposition,[status(thm),theory(equality)],[c_63,c_26])).

tff(c_1038,plain,(
    r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1000,c_81])).

tff(c_32,plain,
    ( r1_xboole_0('#skF_3',k2_xboole_0('#skF_4','#skF_5'))
    | r1_xboole_0('#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_117,plain,(
    r1_xboole_0('#skF_6','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_10,plain,(
    ! [A_10] :
      ( r2_hidden('#skF_2'(A_10),A_10)
      | k1_xboole_0 = A_10 ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_126,plain,(
    ! [A_40,B_41,C_42] :
      ( ~ r1_xboole_0(A_40,B_41)
      | ~ r2_hidden(C_42,k3_xboole_0(A_40,B_41)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_223,plain,(
    ! [A_50,B_51] :
      ( ~ r1_xboole_0(A_50,B_51)
      | k3_xboole_0(A_50,B_51) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_10,c_126])).

tff(c_245,plain,(
    k3_xboole_0('#skF_6','#skF_7') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_117,c_223])).

tff(c_20,plain,(
    ! [A_19,B_20] : k4_xboole_0(A_19,k4_xboole_0(A_19,B_20)) = k3_xboole_0(A_19,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_940,plain,(
    ! [A_85,C_86] : k4_xboole_0(A_85,k4_xboole_0(A_85,C_86)) = k3_xboole_0(A_85,k2_xboole_0(k1_xboole_0,C_86)) ),
    inference(superposition,[status(thm),theory(equality)],[c_911,c_20])).

tff(c_978,plain,(
    ! [A_85,C_86] : k3_xboole_0(A_85,k2_xboole_0(k1_xboole_0,C_86)) = k3_xboole_0(A_85,C_86) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_940])).

tff(c_28,plain,
    ( r1_xboole_0('#skF_3',k2_xboole_0('#skF_4','#skF_5'))
    | r1_xboole_0('#skF_6','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_215,plain,(
    r1_xboole_0('#skF_6','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_243,plain,(
    k3_xboole_0('#skF_6','#skF_8') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_215,c_223])).

tff(c_16,plain,(
    ! [A_14,B_15,C_16] : k4_xboole_0(k4_xboole_0(A_14,B_15),C_16) = k4_xboole_0(A_14,k2_xboole_0(B_15,C_16)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_18,plain,(
    ! [A_17,B_18] : k4_xboole_0(A_17,k3_xboole_0(A_17,B_18)) = k4_xboole_0(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_778,plain,(
    ! [A_17,B_18,C_77] : k4_xboole_0(A_17,k2_xboole_0(k3_xboole_0(A_17,B_18),C_77)) = k4_xboole_0(k4_xboole_0(A_17,B_18),C_77) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_729])).

tff(c_1976,plain,(
    ! [A_123,B_124,C_125] : k4_xboole_0(A_123,k2_xboole_0(k3_xboole_0(A_123,B_124),C_125)) = k4_xboole_0(A_123,k2_xboole_0(B_124,C_125)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_778])).

tff(c_2011,plain,(
    ! [A_123,B_124,C_125] : k4_xboole_0(A_123,k4_xboole_0(A_123,k2_xboole_0(B_124,C_125))) = k3_xboole_0(A_123,k2_xboole_0(k3_xboole_0(A_123,B_124),C_125)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1976,c_20])).

tff(c_10442,plain,(
    ! [A_254,B_255,C_256] : k3_xboole_0(A_254,k2_xboole_0(k3_xboole_0(A_254,B_255),C_256)) = k3_xboole_0(A_254,k2_xboole_0(B_255,C_256)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_2011])).

tff(c_10689,plain,(
    ! [C_256] : k3_xboole_0('#skF_6',k2_xboole_0(k1_xboole_0,C_256)) = k3_xboole_0('#skF_6',k2_xboole_0('#skF_8',C_256)) ),
    inference(superposition,[status(thm),theory(equality)],[c_243,c_10442])).

tff(c_10782,plain,(
    ! [C_256] : k3_xboole_0('#skF_6',k2_xboole_0('#skF_8',C_256)) = k3_xboole_0('#skF_6',C_256) ),
    inference(demodulation,[status(thm),theory(equality)],[c_978,c_10689])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_1'(A_5,B_6),k3_xboole_0(A_5,B_6))
      | r1_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_24,plain,(
    ! [A_24] : r1_xboole_0(A_24,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_59,plain,(
    ! [B_32,A_33] :
      ( r1_xboole_0(B_32,A_33)
      | ~ r1_xboole_0(A_33,B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_62,plain,(
    ! [A_24] : r1_xboole_0(k1_xboole_0,A_24) ),
    inference(resolution,[status(thm)],[c_24,c_59])).

tff(c_501,plain,(
    ! [A_58,C_59,B_60] :
      ( r1_xboole_0(A_58,C_59)
      | ~ r1_xboole_0(B_60,C_59)
      | ~ r1_tarski(A_58,B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_552,plain,(
    ! [A_63,A_64] :
      ( r1_xboole_0(A_63,A_64)
      | ~ r1_tarski(A_63,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_62,c_501])).

tff(c_163,plain,(
    ! [A_46] : k4_xboole_0(A_46,A_46) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_159])).

tff(c_168,plain,(
    ! [A_46] : k4_xboole_0(A_46,k1_xboole_0) = k3_xboole_0(A_46,A_46) ),
    inference(superposition,[status(thm),theory(equality)],[c_163,c_20])).

tff(c_184,plain,(
    ! [A_47] : k3_xboole_0(A_47,A_47) = A_47 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_168])).

tff(c_8,plain,(
    ! [A_5,B_6,C_9] :
      ( ~ r1_xboole_0(A_5,B_6)
      | ~ r2_hidden(C_9,k3_xboole_0(A_5,B_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_190,plain,(
    ! [A_47,C_9] :
      ( ~ r1_xboole_0(A_47,A_47)
      | ~ r2_hidden(C_9,A_47) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_184,c_8])).

tff(c_852,plain,(
    ! [C_80,A_81] :
      ( ~ r2_hidden(C_80,A_81)
      | ~ r1_tarski(A_81,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_552,c_190])).

tff(c_32361,plain,(
    ! [A_424,B_425] :
      ( ~ r1_tarski(k3_xboole_0(A_424,B_425),k1_xboole_0)
      | r1_xboole_0(A_424,B_425) ) ),
    inference(resolution,[status(thm)],[c_6,c_852])).

tff(c_53133,plain,(
    ! [C_554] :
      ( ~ r1_tarski(k3_xboole_0('#skF_6',C_554),k1_xboole_0)
      | r1_xboole_0('#skF_6',k2_xboole_0('#skF_8',C_554)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10782,c_32361])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_36,plain,
    ( r1_xboole_0('#skF_3',k2_xboole_0('#skF_4','#skF_5'))
    | ~ r1_xboole_0('#skF_6',k2_xboole_0('#skF_7','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_39,plain,
    ( r1_xboole_0('#skF_3',k2_xboole_0('#skF_4','#skF_5'))
    | ~ r1_xboole_0('#skF_6',k2_xboole_0('#skF_8','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_36])).

tff(c_536,plain,(
    ~ r1_xboole_0('#skF_6',k2_xboole_0('#skF_8','#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_39])).

tff(c_53149,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_6','#skF_7'),k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_53133,c_536])).

tff(c_53175,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1038,c_245,c_53149])).

tff(c_53177,plain,(
    r1_xboole_0('#skF_6',k2_xboole_0('#skF_8','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_39])).

tff(c_38,plain,
    ( ~ r1_xboole_0('#skF_3','#skF_5')
    | ~ r1_xboole_0('#skF_3','#skF_4')
    | ~ r1_xboole_0('#skF_6',k2_xboole_0('#skF_7','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_40,plain,
    ( ~ r1_xboole_0('#skF_3','#skF_5')
    | ~ r1_xboole_0('#skF_3','#skF_4')
    | ~ r1_xboole_0('#skF_6',k2_xboole_0('#skF_8','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_38])).

tff(c_53322,plain,
    ( ~ r1_xboole_0('#skF_3','#skF_5')
    | ~ r1_xboole_0('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_53177,c_40])).

tff(c_53323,plain,(
    ~ r1_xboole_0('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_53322])).

tff(c_53176,plain,(
    r1_xboole_0('#skF_3',k2_xboole_0('#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_39])).

tff(c_4,plain,(
    ! [B_4,A_3] :
      ( r1_xboole_0(B_4,A_3)
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_53187,plain,(
    r1_xboole_0(k2_xboole_0('#skF_4','#skF_5'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_53176,c_4])).

tff(c_22,plain,(
    ! [A_21,C_23,B_22] :
      ( r1_xboole_0(A_21,C_23)
      | ~ r1_xboole_0(B_22,C_23)
      | ~ r1_tarski(A_21,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_54584,plain,(
    ! [A_614] :
      ( r1_xboole_0(A_614,'#skF_3')
      | ~ r1_tarski(A_614,k2_xboole_0('#skF_4','#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_53187,c_22])).

tff(c_54594,plain,(
    r1_xboole_0('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_54584])).

tff(c_54611,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_54594,c_4])).

tff(c_54617,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_53323,c_54611])).

tff(c_54618,plain,(
    ~ r1_xboole_0('#skF_3','#skF_5') ),
    inference(splitRight,[status(thm)],[c_53322])).

tff(c_56704,plain,(
    ! [A_687] :
      ( r1_xboole_0(A_687,'#skF_3')
      | ~ r1_tarski(A_687,k2_xboole_0('#skF_4','#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_53187,c_22])).

tff(c_56713,plain,(
    r1_xboole_0('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_81,c_56704])).

tff(c_56722,plain,(
    r1_xboole_0('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_56713,c_4])).

tff(c_56728,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54618,c_56722])).

tff(c_56730,plain,(
    ~ r1_xboole_0('#skF_6','#skF_8') ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_30,plain,
    ( ~ r1_xboole_0('#skF_3','#skF_5')
    | ~ r1_xboole_0('#skF_3','#skF_4')
    | r1_xboole_0('#skF_6','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_56937,plain,
    ( ~ r1_xboole_0('#skF_3','#skF_5')
    | ~ r1_xboole_0('#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_56730,c_30])).

tff(c_56938,plain,(
    ~ r1_xboole_0('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_56937])).

tff(c_56729,plain,(
    r1_xboole_0('#skF_3',k2_xboole_0('#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_56733,plain,(
    r1_xboole_0(k2_xboole_0('#skF_4','#skF_5'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_56729,c_4])).

tff(c_57017,plain,(
    ! [A_696,C_697,B_698] :
      ( r1_xboole_0(A_696,C_697)
      | ~ r1_xboole_0(B_698,C_697)
      | ~ r1_tarski(A_696,B_698) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_58124,plain,(
    ! [A_745] :
      ( r1_xboole_0(A_745,'#skF_3')
      | ~ r1_tarski(A_745,k2_xboole_0('#skF_4','#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_56733,c_57017])).

tff(c_58134,plain,(
    r1_xboole_0('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_58124])).

tff(c_58151,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_58134,c_4])).

tff(c_58157,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56938,c_58151])).

tff(c_58158,plain,(
    ~ r1_xboole_0('#skF_3','#skF_5') ),
    inference(splitRight,[status(thm)],[c_56937])).

tff(c_58175,plain,(
    ! [A_746,C_747,B_748] :
      ( r1_xboole_0(A_746,C_747)
      | ~ r1_xboole_0(B_748,C_747)
      | ~ r1_tarski(A_746,B_748) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_59183,plain,(
    ! [A_789] :
      ( r1_xboole_0(A_789,'#skF_3')
      | ~ r1_tarski(A_789,k2_xboole_0('#skF_4','#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_56733,c_58175])).

tff(c_59192,plain,(
    r1_xboole_0('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_81,c_59183])).

tff(c_59201,plain,(
    r1_xboole_0('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_59192,c_4])).

tff(c_59207,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58158,c_59201])).

tff(c_59209,plain,(
    ~ r1_xboole_0('#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_34,plain,
    ( ~ r1_xboole_0('#skF_3','#skF_5')
    | ~ r1_xboole_0('#skF_3','#skF_4')
    | r1_xboole_0('#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_59458,plain,
    ( ~ r1_xboole_0('#skF_3','#skF_5')
    | ~ r1_xboole_0('#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_59209,c_34])).

tff(c_59459,plain,(
    ~ r1_xboole_0('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_59458])).

tff(c_59208,plain,(
    r1_xboole_0('#skF_3',k2_xboole_0('#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_59212,plain,(
    r1_xboole_0(k2_xboole_0('#skF_4','#skF_5'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_59208,c_4])).

tff(c_59578,plain,(
    ! [A_811,C_812,B_813] :
      ( r1_xboole_0(A_811,C_812)
      | ~ r1_xboole_0(B_813,C_812)
      | ~ r1_tarski(A_811,B_813) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_59700,plain,(
    ! [A_828] :
      ( r1_xboole_0(A_828,'#skF_3')
      | ~ r1_tarski(A_828,k2_xboole_0('#skF_4','#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_59212,c_59578])).

tff(c_59710,plain,(
    r1_xboole_0('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_59700])).

tff(c_59727,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_59710,c_4])).

tff(c_59733,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_59459,c_59727])).

tff(c_59734,plain,(
    ~ r1_xboole_0('#skF_3','#skF_5') ),
    inference(splitRight,[status(thm)],[c_59458])).

tff(c_59863,plain,(
    ! [A_833,C_834,B_835] :
      ( r1_xboole_0(A_833,C_834)
      | ~ r1_xboole_0(B_835,C_834)
      | ~ r1_tarski(A_833,B_835) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_60405,plain,(
    ! [A_863] :
      ( r1_xboole_0(A_863,'#skF_3')
      | ~ r1_tarski(A_863,k2_xboole_0('#skF_4','#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_59212,c_59863])).

tff(c_60414,plain,(
    r1_xboole_0('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_81,c_60405])).

tff(c_60423,plain,(
    r1_xboole_0('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_60414,c_4])).

tff(c_60429,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_59734,c_60423])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:02:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 16.23/8.96  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 16.23/8.97  
% 16.23/8.97  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 16.23/8.97  %$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_8 > #skF_4 > #skF_1
% 16.23/8.97  
% 16.23/8.97  %Foreground sorts:
% 16.23/8.97  
% 16.23/8.97  
% 16.23/8.97  %Background operators:
% 16.23/8.97  
% 16.23/8.97  
% 16.23/8.97  %Foreground operators:
% 16.23/8.97  tff('#skF_2', type, '#skF_2': $i > $i).
% 16.23/8.97  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 16.23/8.97  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 16.23/8.97  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 16.23/8.97  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 16.23/8.97  tff('#skF_7', type, '#skF_7': $i).
% 16.23/8.97  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 16.23/8.97  tff('#skF_5', type, '#skF_5': $i).
% 16.23/8.97  tff('#skF_6', type, '#skF_6': $i).
% 16.23/8.97  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 16.23/8.97  tff('#skF_3', type, '#skF_3': $i).
% 16.23/8.97  tff('#skF_8', type, '#skF_8': $i).
% 16.23/8.97  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 16.23/8.97  tff('#skF_4', type, '#skF_4': $i).
% 16.23/8.97  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 16.23/8.97  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 16.23/8.97  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 16.23/8.97  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 16.23/8.97  
% 16.23/9.00  tff(f_57, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 16.23/9.00  tff(f_59, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 16.23/9.00  tff(f_55, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 16.23/9.00  tff(f_63, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 16.23/9.00  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 16.23/9.00  tff(f_73, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 16.23/9.00  tff(f_90, negated_conjecture, ~(![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_xboole_1)).
% 16.23/9.00  tff(f_53, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 16.23/9.00  tff(f_45, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 16.23/9.00  tff(f_61, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 16.23/9.00  tff(f_71, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 16.23/9.00  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 16.23/9.00  tff(f_69, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_xboole_1)).
% 16.23/9.00  tff(c_14, plain, (![A_13]: (k4_xboole_0(A_13, k1_xboole_0)=A_13)), inference(cnfTransformation, [status(thm)], [f_57])).
% 16.23/9.00  tff(c_729, plain, (![A_75, B_76, C_77]: (k4_xboole_0(k4_xboole_0(A_75, B_76), C_77)=k4_xboole_0(A_75, k2_xboole_0(B_76, C_77)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 16.23/9.00  tff(c_911, plain, (![A_85, C_86]: (k4_xboole_0(A_85, k2_xboole_0(k1_xboole_0, C_86))=k4_xboole_0(A_85, C_86))), inference(superposition, [status(thm), theory('equality')], [c_14, c_729])).
% 16.23/9.00  tff(c_12, plain, (![A_12]: (k3_xboole_0(A_12, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_55])).
% 16.23/9.00  tff(c_144, plain, (![A_44, B_45]: (k4_xboole_0(A_44, k4_xboole_0(A_44, B_45))=k3_xboole_0(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_63])).
% 16.23/9.00  tff(c_159, plain, (![A_13]: (k4_xboole_0(A_13, A_13)=k3_xboole_0(A_13, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_14, c_144])).
% 16.23/9.00  tff(c_162, plain, (![A_13]: (k4_xboole_0(A_13, A_13)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_159])).
% 16.23/9.00  tff(c_984, plain, (![C_87]: (k4_xboole_0(k2_xboole_0(k1_xboole_0, C_87), C_87)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_911, c_162])).
% 16.23/9.00  tff(c_1000, plain, (k2_xboole_0(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_984, c_14])).
% 16.23/9.00  tff(c_63, plain, (![B_34, A_35]: (k2_xboole_0(B_34, A_35)=k2_xboole_0(A_35, B_34))), inference(cnfTransformation, [status(thm)], [f_27])).
% 16.23/9.00  tff(c_26, plain, (![A_25, B_26]: (r1_tarski(A_25, k2_xboole_0(A_25, B_26)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 16.23/9.00  tff(c_81, plain, (![B_34, A_35]: (r1_tarski(B_34, k2_xboole_0(A_35, B_34)))), inference(superposition, [status(thm), theory('equality')], [c_63, c_26])).
% 16.23/9.00  tff(c_1038, plain, (r1_tarski(k1_xboole_0, k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1000, c_81])).
% 16.23/9.00  tff(c_32, plain, (r1_xboole_0('#skF_3', k2_xboole_0('#skF_4', '#skF_5')) | r1_xboole_0('#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_90])).
% 16.23/9.00  tff(c_117, plain, (r1_xboole_0('#skF_6', '#skF_7')), inference(splitLeft, [status(thm)], [c_32])).
% 16.23/9.00  tff(c_10, plain, (![A_10]: (r2_hidden('#skF_2'(A_10), A_10) | k1_xboole_0=A_10)), inference(cnfTransformation, [status(thm)], [f_53])).
% 16.23/9.00  tff(c_126, plain, (![A_40, B_41, C_42]: (~r1_xboole_0(A_40, B_41) | ~r2_hidden(C_42, k3_xboole_0(A_40, B_41)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 16.23/9.00  tff(c_223, plain, (![A_50, B_51]: (~r1_xboole_0(A_50, B_51) | k3_xboole_0(A_50, B_51)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_126])).
% 16.23/9.00  tff(c_245, plain, (k3_xboole_0('#skF_6', '#skF_7')=k1_xboole_0), inference(resolution, [status(thm)], [c_117, c_223])).
% 16.23/9.00  tff(c_20, plain, (![A_19, B_20]: (k4_xboole_0(A_19, k4_xboole_0(A_19, B_20))=k3_xboole_0(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_63])).
% 16.23/9.00  tff(c_940, plain, (![A_85, C_86]: (k4_xboole_0(A_85, k4_xboole_0(A_85, C_86))=k3_xboole_0(A_85, k2_xboole_0(k1_xboole_0, C_86)))), inference(superposition, [status(thm), theory('equality')], [c_911, c_20])).
% 16.23/9.00  tff(c_978, plain, (![A_85, C_86]: (k3_xboole_0(A_85, k2_xboole_0(k1_xboole_0, C_86))=k3_xboole_0(A_85, C_86))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_940])).
% 16.23/9.00  tff(c_28, plain, (r1_xboole_0('#skF_3', k2_xboole_0('#skF_4', '#skF_5')) | r1_xboole_0('#skF_6', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_90])).
% 16.23/9.00  tff(c_215, plain, (r1_xboole_0('#skF_6', '#skF_8')), inference(splitLeft, [status(thm)], [c_28])).
% 16.23/9.00  tff(c_243, plain, (k3_xboole_0('#skF_6', '#skF_8')=k1_xboole_0), inference(resolution, [status(thm)], [c_215, c_223])).
% 16.23/9.00  tff(c_16, plain, (![A_14, B_15, C_16]: (k4_xboole_0(k4_xboole_0(A_14, B_15), C_16)=k4_xboole_0(A_14, k2_xboole_0(B_15, C_16)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 16.23/9.00  tff(c_18, plain, (![A_17, B_18]: (k4_xboole_0(A_17, k3_xboole_0(A_17, B_18))=k4_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_61])).
% 16.23/9.00  tff(c_778, plain, (![A_17, B_18, C_77]: (k4_xboole_0(A_17, k2_xboole_0(k3_xboole_0(A_17, B_18), C_77))=k4_xboole_0(k4_xboole_0(A_17, B_18), C_77))), inference(superposition, [status(thm), theory('equality')], [c_18, c_729])).
% 16.23/9.00  tff(c_1976, plain, (![A_123, B_124, C_125]: (k4_xboole_0(A_123, k2_xboole_0(k3_xboole_0(A_123, B_124), C_125))=k4_xboole_0(A_123, k2_xboole_0(B_124, C_125)))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_778])).
% 16.23/9.00  tff(c_2011, plain, (![A_123, B_124, C_125]: (k4_xboole_0(A_123, k4_xboole_0(A_123, k2_xboole_0(B_124, C_125)))=k3_xboole_0(A_123, k2_xboole_0(k3_xboole_0(A_123, B_124), C_125)))), inference(superposition, [status(thm), theory('equality')], [c_1976, c_20])).
% 16.23/9.00  tff(c_10442, plain, (![A_254, B_255, C_256]: (k3_xboole_0(A_254, k2_xboole_0(k3_xboole_0(A_254, B_255), C_256))=k3_xboole_0(A_254, k2_xboole_0(B_255, C_256)))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_2011])).
% 16.23/9.00  tff(c_10689, plain, (![C_256]: (k3_xboole_0('#skF_6', k2_xboole_0(k1_xboole_0, C_256))=k3_xboole_0('#skF_6', k2_xboole_0('#skF_8', C_256)))), inference(superposition, [status(thm), theory('equality')], [c_243, c_10442])).
% 16.23/9.00  tff(c_10782, plain, (![C_256]: (k3_xboole_0('#skF_6', k2_xboole_0('#skF_8', C_256))=k3_xboole_0('#skF_6', C_256))), inference(demodulation, [status(thm), theory('equality')], [c_978, c_10689])).
% 16.23/9.00  tff(c_6, plain, (![A_5, B_6]: (r2_hidden('#skF_1'(A_5, B_6), k3_xboole_0(A_5, B_6)) | r1_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_45])).
% 16.23/9.00  tff(c_24, plain, (![A_24]: (r1_xboole_0(A_24, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_71])).
% 16.23/9.00  tff(c_59, plain, (![B_32, A_33]: (r1_xboole_0(B_32, A_33) | ~r1_xboole_0(A_33, B_32))), inference(cnfTransformation, [status(thm)], [f_31])).
% 16.23/9.00  tff(c_62, plain, (![A_24]: (r1_xboole_0(k1_xboole_0, A_24))), inference(resolution, [status(thm)], [c_24, c_59])).
% 16.23/9.00  tff(c_501, plain, (![A_58, C_59, B_60]: (r1_xboole_0(A_58, C_59) | ~r1_xboole_0(B_60, C_59) | ~r1_tarski(A_58, B_60))), inference(cnfTransformation, [status(thm)], [f_69])).
% 16.23/9.00  tff(c_552, plain, (![A_63, A_64]: (r1_xboole_0(A_63, A_64) | ~r1_tarski(A_63, k1_xboole_0))), inference(resolution, [status(thm)], [c_62, c_501])).
% 16.23/9.00  tff(c_163, plain, (![A_46]: (k4_xboole_0(A_46, A_46)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_159])).
% 16.23/9.00  tff(c_168, plain, (![A_46]: (k4_xboole_0(A_46, k1_xboole_0)=k3_xboole_0(A_46, A_46))), inference(superposition, [status(thm), theory('equality')], [c_163, c_20])).
% 16.23/9.00  tff(c_184, plain, (![A_47]: (k3_xboole_0(A_47, A_47)=A_47)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_168])).
% 16.23/9.00  tff(c_8, plain, (![A_5, B_6, C_9]: (~r1_xboole_0(A_5, B_6) | ~r2_hidden(C_9, k3_xboole_0(A_5, B_6)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 16.23/9.00  tff(c_190, plain, (![A_47, C_9]: (~r1_xboole_0(A_47, A_47) | ~r2_hidden(C_9, A_47))), inference(superposition, [status(thm), theory('equality')], [c_184, c_8])).
% 16.23/9.00  tff(c_852, plain, (![C_80, A_81]: (~r2_hidden(C_80, A_81) | ~r1_tarski(A_81, k1_xboole_0))), inference(resolution, [status(thm)], [c_552, c_190])).
% 16.23/9.00  tff(c_32361, plain, (![A_424, B_425]: (~r1_tarski(k3_xboole_0(A_424, B_425), k1_xboole_0) | r1_xboole_0(A_424, B_425))), inference(resolution, [status(thm)], [c_6, c_852])).
% 16.23/9.00  tff(c_53133, plain, (![C_554]: (~r1_tarski(k3_xboole_0('#skF_6', C_554), k1_xboole_0) | r1_xboole_0('#skF_6', k2_xboole_0('#skF_8', C_554)))), inference(superposition, [status(thm), theory('equality')], [c_10782, c_32361])).
% 16.23/9.00  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 16.23/9.00  tff(c_36, plain, (r1_xboole_0('#skF_3', k2_xboole_0('#skF_4', '#skF_5')) | ~r1_xboole_0('#skF_6', k2_xboole_0('#skF_7', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_90])).
% 16.23/9.00  tff(c_39, plain, (r1_xboole_0('#skF_3', k2_xboole_0('#skF_4', '#skF_5')) | ~r1_xboole_0('#skF_6', k2_xboole_0('#skF_8', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_36])).
% 16.23/9.00  tff(c_536, plain, (~r1_xboole_0('#skF_6', k2_xboole_0('#skF_8', '#skF_7'))), inference(splitLeft, [status(thm)], [c_39])).
% 16.23/9.00  tff(c_53149, plain, (~r1_tarski(k3_xboole_0('#skF_6', '#skF_7'), k1_xboole_0)), inference(resolution, [status(thm)], [c_53133, c_536])).
% 16.23/9.00  tff(c_53175, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1038, c_245, c_53149])).
% 16.23/9.00  tff(c_53177, plain, (r1_xboole_0('#skF_6', k2_xboole_0('#skF_8', '#skF_7'))), inference(splitRight, [status(thm)], [c_39])).
% 16.23/9.00  tff(c_38, plain, (~r1_xboole_0('#skF_3', '#skF_5') | ~r1_xboole_0('#skF_3', '#skF_4') | ~r1_xboole_0('#skF_6', k2_xboole_0('#skF_7', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_90])).
% 16.23/9.00  tff(c_40, plain, (~r1_xboole_0('#skF_3', '#skF_5') | ~r1_xboole_0('#skF_3', '#skF_4') | ~r1_xboole_0('#skF_6', k2_xboole_0('#skF_8', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_38])).
% 16.23/9.00  tff(c_53322, plain, (~r1_xboole_0('#skF_3', '#skF_5') | ~r1_xboole_0('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_53177, c_40])).
% 16.23/9.00  tff(c_53323, plain, (~r1_xboole_0('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_53322])).
% 16.23/9.00  tff(c_53176, plain, (r1_xboole_0('#skF_3', k2_xboole_0('#skF_4', '#skF_5'))), inference(splitRight, [status(thm)], [c_39])).
% 16.23/9.00  tff(c_4, plain, (![B_4, A_3]: (r1_xboole_0(B_4, A_3) | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 16.23/9.00  tff(c_53187, plain, (r1_xboole_0(k2_xboole_0('#skF_4', '#skF_5'), '#skF_3')), inference(resolution, [status(thm)], [c_53176, c_4])).
% 16.23/9.00  tff(c_22, plain, (![A_21, C_23, B_22]: (r1_xboole_0(A_21, C_23) | ~r1_xboole_0(B_22, C_23) | ~r1_tarski(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_69])).
% 16.23/9.00  tff(c_54584, plain, (![A_614]: (r1_xboole_0(A_614, '#skF_3') | ~r1_tarski(A_614, k2_xboole_0('#skF_4', '#skF_5')))), inference(resolution, [status(thm)], [c_53187, c_22])).
% 16.23/9.00  tff(c_54594, plain, (r1_xboole_0('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_26, c_54584])).
% 16.23/9.00  tff(c_54611, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_54594, c_4])).
% 16.23/9.00  tff(c_54617, plain, $false, inference(negUnitSimplification, [status(thm)], [c_53323, c_54611])).
% 16.23/9.00  tff(c_54618, plain, (~r1_xboole_0('#skF_3', '#skF_5')), inference(splitRight, [status(thm)], [c_53322])).
% 16.23/9.00  tff(c_56704, plain, (![A_687]: (r1_xboole_0(A_687, '#skF_3') | ~r1_tarski(A_687, k2_xboole_0('#skF_4', '#skF_5')))), inference(resolution, [status(thm)], [c_53187, c_22])).
% 16.23/9.00  tff(c_56713, plain, (r1_xboole_0('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_81, c_56704])).
% 16.23/9.00  tff(c_56722, plain, (r1_xboole_0('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_56713, c_4])).
% 16.23/9.00  tff(c_56728, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54618, c_56722])).
% 16.23/9.00  tff(c_56730, plain, (~r1_xboole_0('#skF_6', '#skF_8')), inference(splitRight, [status(thm)], [c_28])).
% 16.23/9.00  tff(c_30, plain, (~r1_xboole_0('#skF_3', '#skF_5') | ~r1_xboole_0('#skF_3', '#skF_4') | r1_xboole_0('#skF_6', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_90])).
% 16.23/9.00  tff(c_56937, plain, (~r1_xboole_0('#skF_3', '#skF_5') | ~r1_xboole_0('#skF_3', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_56730, c_30])).
% 16.23/9.00  tff(c_56938, plain, (~r1_xboole_0('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_56937])).
% 16.23/9.00  tff(c_56729, plain, (r1_xboole_0('#skF_3', k2_xboole_0('#skF_4', '#skF_5'))), inference(splitRight, [status(thm)], [c_28])).
% 16.23/9.00  tff(c_56733, plain, (r1_xboole_0(k2_xboole_0('#skF_4', '#skF_5'), '#skF_3')), inference(resolution, [status(thm)], [c_56729, c_4])).
% 16.23/9.00  tff(c_57017, plain, (![A_696, C_697, B_698]: (r1_xboole_0(A_696, C_697) | ~r1_xboole_0(B_698, C_697) | ~r1_tarski(A_696, B_698))), inference(cnfTransformation, [status(thm)], [f_69])).
% 16.23/9.00  tff(c_58124, plain, (![A_745]: (r1_xboole_0(A_745, '#skF_3') | ~r1_tarski(A_745, k2_xboole_0('#skF_4', '#skF_5')))), inference(resolution, [status(thm)], [c_56733, c_57017])).
% 16.23/9.00  tff(c_58134, plain, (r1_xboole_0('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_26, c_58124])).
% 16.23/9.00  tff(c_58151, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_58134, c_4])).
% 16.23/9.00  tff(c_58157, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56938, c_58151])).
% 16.23/9.00  tff(c_58158, plain, (~r1_xboole_0('#skF_3', '#skF_5')), inference(splitRight, [status(thm)], [c_56937])).
% 16.23/9.00  tff(c_58175, plain, (![A_746, C_747, B_748]: (r1_xboole_0(A_746, C_747) | ~r1_xboole_0(B_748, C_747) | ~r1_tarski(A_746, B_748))), inference(cnfTransformation, [status(thm)], [f_69])).
% 16.23/9.00  tff(c_59183, plain, (![A_789]: (r1_xboole_0(A_789, '#skF_3') | ~r1_tarski(A_789, k2_xboole_0('#skF_4', '#skF_5')))), inference(resolution, [status(thm)], [c_56733, c_58175])).
% 16.23/9.00  tff(c_59192, plain, (r1_xboole_0('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_81, c_59183])).
% 16.23/9.00  tff(c_59201, plain, (r1_xboole_0('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_59192, c_4])).
% 16.23/9.00  tff(c_59207, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58158, c_59201])).
% 16.23/9.00  tff(c_59209, plain, (~r1_xboole_0('#skF_6', '#skF_7')), inference(splitRight, [status(thm)], [c_32])).
% 16.23/9.00  tff(c_34, plain, (~r1_xboole_0('#skF_3', '#skF_5') | ~r1_xboole_0('#skF_3', '#skF_4') | r1_xboole_0('#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_90])).
% 16.23/9.00  tff(c_59458, plain, (~r1_xboole_0('#skF_3', '#skF_5') | ~r1_xboole_0('#skF_3', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_59209, c_34])).
% 16.23/9.00  tff(c_59459, plain, (~r1_xboole_0('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_59458])).
% 16.23/9.00  tff(c_59208, plain, (r1_xboole_0('#skF_3', k2_xboole_0('#skF_4', '#skF_5'))), inference(splitRight, [status(thm)], [c_32])).
% 16.23/9.00  tff(c_59212, plain, (r1_xboole_0(k2_xboole_0('#skF_4', '#skF_5'), '#skF_3')), inference(resolution, [status(thm)], [c_59208, c_4])).
% 16.23/9.00  tff(c_59578, plain, (![A_811, C_812, B_813]: (r1_xboole_0(A_811, C_812) | ~r1_xboole_0(B_813, C_812) | ~r1_tarski(A_811, B_813))), inference(cnfTransformation, [status(thm)], [f_69])).
% 16.23/9.00  tff(c_59700, plain, (![A_828]: (r1_xboole_0(A_828, '#skF_3') | ~r1_tarski(A_828, k2_xboole_0('#skF_4', '#skF_5')))), inference(resolution, [status(thm)], [c_59212, c_59578])).
% 16.23/9.00  tff(c_59710, plain, (r1_xboole_0('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_26, c_59700])).
% 16.23/9.00  tff(c_59727, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_59710, c_4])).
% 16.23/9.00  tff(c_59733, plain, $false, inference(negUnitSimplification, [status(thm)], [c_59459, c_59727])).
% 16.23/9.00  tff(c_59734, plain, (~r1_xboole_0('#skF_3', '#skF_5')), inference(splitRight, [status(thm)], [c_59458])).
% 16.23/9.00  tff(c_59863, plain, (![A_833, C_834, B_835]: (r1_xboole_0(A_833, C_834) | ~r1_xboole_0(B_835, C_834) | ~r1_tarski(A_833, B_835))), inference(cnfTransformation, [status(thm)], [f_69])).
% 16.23/9.00  tff(c_60405, plain, (![A_863]: (r1_xboole_0(A_863, '#skF_3') | ~r1_tarski(A_863, k2_xboole_0('#skF_4', '#skF_5')))), inference(resolution, [status(thm)], [c_59212, c_59863])).
% 16.23/9.00  tff(c_60414, plain, (r1_xboole_0('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_81, c_60405])).
% 16.23/9.00  tff(c_60423, plain, (r1_xboole_0('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_60414, c_4])).
% 16.23/9.00  tff(c_60429, plain, $false, inference(negUnitSimplification, [status(thm)], [c_59734, c_60423])).
% 16.23/9.00  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 16.23/9.00  
% 16.23/9.00  Inference rules
% 16.23/9.00  ----------------------
% 16.23/9.00  #Ref     : 0
% 16.23/9.00  #Sup     : 14366
% 16.23/9.00  #Fact    : 0
% 16.23/9.00  #Define  : 0
% 16.23/9.00  #Split   : 33
% 16.23/9.00  #Chain   : 0
% 16.23/9.00  #Close   : 0
% 16.23/9.00  
% 16.23/9.00  Ordering : KBO
% 16.23/9.00  
% 16.23/9.00  Simplification rules
% 16.23/9.00  ----------------------
% 16.23/9.00  #Subsume      : 1068
% 16.23/9.00  #Demod        : 16583
% 16.23/9.00  #Tautology    : 8967
% 16.23/9.00  #SimpNegUnit  : 205
% 16.23/9.00  #BackRed      : 0
% 16.23/9.00  
% 16.23/9.00  #Partial instantiations: 0
% 16.23/9.00  #Strategies tried      : 1
% 16.23/9.00  
% 16.23/9.00  Timing (in seconds)
% 16.23/9.00  ----------------------
% 16.23/9.00  Preprocessing        : 0.39
% 16.23/9.00  Parsing              : 0.22
% 16.23/9.00  CNF conversion       : 0.03
% 16.23/9.00  Main loop            : 7.83
% 16.23/9.00  Inferencing          : 1.20
% 16.23/9.00  Reduction            : 4.82
% 16.23/9.00  Demodulation         : 4.32
% 16.23/9.00  BG Simplification    : 0.12
% 16.23/9.00  Subsumption          : 1.33
% 16.23/9.00  Abstraction          : 0.22
% 16.23/9.00  MUC search           : 0.00
% 16.23/9.00  Cooper               : 0.00
% 16.23/9.00  Total                : 8.27
% 16.23/9.00  Index Insertion      : 0.00
% 16.23/9.00  Index Deletion       : 0.00
% 16.23/9.00  Index Matching       : 0.00
% 16.23/9.00  BG Taut test         : 0.00
%------------------------------------------------------------------------------
