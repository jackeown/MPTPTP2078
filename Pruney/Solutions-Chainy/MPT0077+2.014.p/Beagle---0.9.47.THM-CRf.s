%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:37 EST 2020

% Result     : Theorem 41.56s
% Output     : CNFRefutation 41.99s
% Verified   : 
% Statistics : Number of formulae       :  287 (1102 expanded)
%              Number of leaves         :   32 ( 377 expanded)
%              Depth                    :   20
%              Number of atoms          :  345 (1579 expanded)
%              Number of equality atoms :  177 ( 813 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_90,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
            & r1_xboole_0(A,B)
            & r1_xboole_0(A,C) )
        & ~ ( ~ ( r1_xboole_0(A,B)
                & r1_xboole_0(A,C) )
            & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_73,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_51,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_65,axiom,(
    ! [A,B,C] : k4_xboole_0(A,k4_xboole_0(B,C)) = k2_xboole_0(k4_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_53,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_57,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_61,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

tff(c_109161,plain,(
    ! [A_1646,B_1647] :
      ( r1_xboole_0(A_1646,B_1647)
      | k3_xboole_0(A_1646,B_1647) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    ! [B_6,A_5] :
      ( r1_xboole_0(B_6,A_5)
      | ~ r1_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_109201,plain,(
    ! [B_1650,A_1651] :
      ( r1_xboole_0(B_1650,A_1651)
      | k3_xboole_0(A_1651,B_1650) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_109161,c_8])).

tff(c_194,plain,(
    ! [A_45,B_46] :
      ( r1_xboole_0(A_45,B_46)
      | k3_xboole_0(A_45,B_46) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_208,plain,(
    ! [B_49,A_50] :
      ( r1_xboole_0(B_49,A_50)
      | k3_xboole_0(A_50,B_49) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_194,c_8])).

tff(c_40,plain,
    ( ~ r1_xboole_0('#skF_2','#skF_4')
    | ~ r1_xboole_0('#skF_2','#skF_3')
    | r1_xboole_0('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_173,plain,(
    ~ r1_xboole_0('#skF_2','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_218,plain,(
    k3_xboole_0('#skF_3','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_208,c_173])).

tff(c_79,plain,(
    ! [B_39,A_40] : k2_xboole_0(B_39,A_40) = k2_xboole_0(A_40,B_39) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_32,plain,(
    ! [A_29,B_30] : r1_tarski(A_29,k2_xboole_0(A_29,B_30)) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_94,plain,(
    ! [A_40,B_39] : r1_tarski(A_40,k2_xboole_0(B_39,A_40)) ),
    inference(superposition,[status(thm),theory(equality)],[c_79,c_32])).

tff(c_201,plain,(
    ! [B_46,A_45] :
      ( r1_xboole_0(B_46,A_45)
      | k3_xboole_0(A_45,B_46) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_194,c_8])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_42,plain,
    ( r1_xboole_0('#skF_2',k2_xboole_0('#skF_3','#skF_4'))
    | ~ r1_xboole_0('#skF_5',k2_xboole_0('#skF_6','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_46,plain,
    ( r1_xboole_0('#skF_2',k2_xboole_0('#skF_4','#skF_3'))
    | ~ r1_xboole_0('#skF_5',k2_xboole_0('#skF_6','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_42])).

tff(c_790,plain,(
    ~ r1_xboole_0('#skF_5',k2_xboole_0('#skF_6','#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_843,plain,(
    k3_xboole_0(k2_xboole_0('#skF_6','#skF_7'),'#skF_5') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_201,c_790])).

tff(c_34,plain,
    ( r1_xboole_0('#skF_2',k2_xboole_0('#skF_3','#skF_4'))
    | r1_xboole_0('#skF_5','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_47,plain,
    ( r1_xboole_0('#skF_2',k2_xboole_0('#skF_4','#skF_3'))
    | r1_xboole_0('#skF_5','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_34])).

tff(c_698,plain,(
    r1_xboole_0('#skF_5','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_47])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( k3_xboole_0(A_3,B_4) = k1_xboole_0
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_704,plain,(
    k3_xboole_0('#skF_5','#skF_7') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_698,c_4])).

tff(c_26,plain,(
    ! [A_21,B_22] : k2_xboole_0(k3_xboole_0(A_21,B_22),k4_xboole_0(A_21,B_22)) = A_21 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_720,plain,(
    k2_xboole_0(k1_xboole_0,k4_xboole_0('#skF_5','#skF_7')) = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_704,c_26])).

tff(c_14,plain,(
    ! [A_12] : k2_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_101,plain,(
    ! [A_40] : k2_xboole_0(k1_xboole_0,A_40) = A_40 ),
    inference(superposition,[status(thm),theory(equality)],[c_79,c_14])).

tff(c_1027,plain,(
    k4_xboole_0('#skF_5','#skF_7') = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_720,c_101])).

tff(c_38,plain,
    ( r1_xboole_0('#skF_2',k2_xboole_0('#skF_3','#skF_4'))
    | r1_xboole_0('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_45,plain,
    ( r1_xboole_0('#skF_2',k2_xboole_0('#skF_4','#skF_3'))
    | r1_xboole_0('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_38])).

tff(c_763,plain,(
    r1_xboole_0('#skF_5','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_45])).

tff(c_769,plain,(
    k3_xboole_0('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_763,c_4])).

tff(c_1197,plain,(
    ! [A_97,B_98,C_99] : k2_xboole_0(k4_xboole_0(A_97,B_98),k3_xboole_0(A_97,C_99)) = k4_xboole_0(A_97,k4_xboole_0(B_98,C_99)) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1239,plain,(
    ! [B_98] : k4_xboole_0('#skF_5',k4_xboole_0(B_98,'#skF_6')) = k2_xboole_0(k4_xboole_0('#skF_5',B_98),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_769,c_1197])).

tff(c_1277,plain,(
    ! [B_98] : k4_xboole_0('#skF_5',k4_xboole_0(B_98,'#skF_6')) = k4_xboole_0('#skF_5',B_98) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_1239])).

tff(c_22,plain,(
    ! [A_17,B_18] : k4_xboole_0(k2_xboole_0(A_17,B_18),B_18) = k4_xboole_0(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_5127,plain,(
    ! [B_185] : k4_xboole_0('#skF_5',k4_xboole_0(B_185,'#skF_6')) = k4_xboole_0('#skF_5',B_185) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_1239])).

tff(c_5233,plain,(
    ! [A_17] : k4_xboole_0('#skF_5',k4_xboole_0(A_17,'#skF_6')) = k4_xboole_0('#skF_5',k2_xboole_0(A_17,'#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_5127])).

tff(c_16526,plain,(
    ! [A_311] : k4_xboole_0('#skF_5',k2_xboole_0(A_311,'#skF_6')) = k4_xboole_0('#skF_5',A_311) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1277,c_5233])).

tff(c_845,plain,(
    ! [A_76,B_77,C_78] :
      ( ~ r1_xboole_0(A_76,B_77)
      | ~ r2_hidden(C_78,k3_xboole_0(A_76,B_77)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_854,plain,(
    ! [C_78] :
      ( ~ r1_xboole_0('#skF_5','#skF_6')
      | ~ r2_hidden(C_78,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_769,c_845])).

tff(c_870,plain,(
    ! [C_78] : ~ r2_hidden(C_78,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_763,c_854])).

tff(c_16,plain,(
    ! [A_13] : k3_xboole_0(A_13,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_20,plain,(
    ! [A_16] : k4_xboole_0(A_16,k1_xboole_0) = A_16 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_431,plain,(
    ! [A_67,B_68] : k4_xboole_0(A_67,k4_xboole_0(A_67,B_68)) = k3_xboole_0(A_67,B_68) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_475,plain,(
    ! [A_16] : k4_xboole_0(A_16,A_16) = k3_xboole_0(A_16,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_431])).

tff(c_480,plain,(
    ! [A_16] : k4_xboole_0(A_16,A_16) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_475])).

tff(c_253,plain,(
    ! [A_57,B_58] : k4_xboole_0(k2_xboole_0(A_57,B_58),B_58) = k4_xboole_0(A_57,B_58) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_275,plain,(
    ! [A_40] : k4_xboole_0(k1_xboole_0,A_40) = k4_xboole_0(A_40,A_40) ),
    inference(superposition,[status(thm),theory(equality)],[c_101,c_253])).

tff(c_537,plain,(
    ! [A_40] : k4_xboole_0(k1_xboole_0,A_40) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_480,c_275])).

tff(c_1272,plain,(
    ! [A_16,C_99] : k4_xboole_0(A_16,k4_xboole_0(k1_xboole_0,C_99)) = k2_xboole_0(A_16,k3_xboole_0(A_16,C_99)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_1197])).

tff(c_1284,plain,(
    ! [A_16,C_99] : k2_xboole_0(A_16,k3_xboole_0(A_16,C_99)) = A_16 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_537,c_1272])).

tff(c_1458,plain,(
    ! [A_105,B_106] : k4_xboole_0(k2_xboole_0(A_105,B_106),A_105) = k4_xboole_0(B_106,A_105) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_253])).

tff(c_1496,plain,(
    ! [A_16,C_99] : k4_xboole_0(k3_xboole_0(A_16,C_99),A_16) = k4_xboole_0(A_16,A_16) ),
    inference(superposition,[status(thm),theory(equality)],[c_1284,c_1458])).

tff(c_1536,plain,(
    ! [A_16,C_99] : k4_xboole_0(k3_xboole_0(A_16,C_99),A_16) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_480,c_1496])).

tff(c_24,plain,(
    ! [A_19,B_20] : k4_xboole_0(A_19,k4_xboole_0(A_19,B_20)) = k3_xboole_0(A_19,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_481,plain,(
    ! [A_69,B_70] : k2_xboole_0(A_69,k4_xboole_0(B_70,A_69)) = k2_xboole_0(A_69,B_70) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_509,plain,(
    ! [A_19,B_20] : k2_xboole_0(k4_xboole_0(A_19,B_20),k3_xboole_0(A_19,B_20)) = k2_xboole_0(k4_xboole_0(A_19,B_20),A_19) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_481])).

tff(c_4286,plain,(
    ! [A_175,B_176] : k2_xboole_0(k4_xboole_0(A_175,B_176),k3_xboole_0(A_175,B_176)) = k2_xboole_0(A_175,k4_xboole_0(A_175,B_176)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_509])).

tff(c_28,plain,(
    ! [A_23,B_24,C_25] : k2_xboole_0(k4_xboole_0(A_23,B_24),k3_xboole_0(A_23,C_25)) = k4_xboole_0(A_23,k4_xboole_0(B_24,C_25)) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_4304,plain,(
    ! [A_175,B_176] : k4_xboole_0(A_175,k4_xboole_0(B_176,B_176)) = k2_xboole_0(A_175,k4_xboole_0(A_175,B_176)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4286,c_28])).

tff(c_4449,plain,(
    ! [A_175,B_176] : k2_xboole_0(A_175,k4_xboole_0(A_175,B_176)) = A_175 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_480,c_4304])).

tff(c_539,plain,(
    ! [A_71] : k4_xboole_0(A_71,A_71) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_475])).

tff(c_547,plain,(
    ! [A_71] : k4_xboole_0(A_71,k1_xboole_0) = k3_xboole_0(A_71,A_71) ),
    inference(superposition,[status(thm),theory(equality)],[c_539,c_24])).

tff(c_580,plain,(
    ! [A_71] : k3_xboole_0(A_71,A_71) = A_71 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_547])).

tff(c_6476,plain,(
    ! [A_195,C_196,B_197] : k2_xboole_0(k3_xboole_0(A_195,C_196),k4_xboole_0(A_195,B_197)) = k4_xboole_0(A_195,k4_xboole_0(B_197,C_196)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1197])).

tff(c_6661,plain,(
    ! [A_71,B_197] : k4_xboole_0(A_71,k4_xboole_0(B_197,A_71)) = k2_xboole_0(A_71,k4_xboole_0(A_71,B_197)) ),
    inference(superposition,[status(thm),theory(equality)],[c_580,c_6476])).

tff(c_6931,plain,(
    ! [A_200,B_201] : k4_xboole_0(A_200,k4_xboole_0(B_201,A_200)) = A_200 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4449,c_6661])).

tff(c_272,plain,(
    ! [A_21,B_22] : k4_xboole_0(k3_xboole_0(A_21,B_22),k4_xboole_0(A_21,B_22)) = k4_xboole_0(A_21,k4_xboole_0(A_21,B_22)) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_253])).

tff(c_3799,plain,(
    ! [A_21,B_22] : k4_xboole_0(k3_xboole_0(A_21,B_22),k4_xboole_0(A_21,B_22)) = k3_xboole_0(A_21,B_22) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_272])).

tff(c_6987,plain,(
    ! [A_200,B_201] : k4_xboole_0(k3_xboole_0(A_200,k4_xboole_0(B_201,A_200)),A_200) = k3_xboole_0(A_200,k4_xboole_0(B_201,A_200)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6931,c_3799])).

tff(c_7258,plain,(
    ! [A_202,B_203] : k3_xboole_0(A_202,k4_xboole_0(B_203,A_202)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1536,c_6987])).

tff(c_10,plain,(
    ! [A_7,B_8] :
      ( r2_hidden('#skF_1'(A_7,B_8),k3_xboole_0(A_7,B_8))
      | r1_xboole_0(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_7357,plain,(
    ! [A_202,B_203] :
      ( r2_hidden('#skF_1'(A_202,k4_xboole_0(B_203,A_202)),k1_xboole_0)
      | r1_xboole_0(A_202,k4_xboole_0(B_203,A_202)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7258,c_10])).

tff(c_7497,plain,(
    ! [A_202,B_203] : r1_xboole_0(A_202,k4_xboole_0(B_203,A_202)) ),
    inference(negUnitSimplification,[status(thm)],[c_870,c_7357])).

tff(c_16864,plain,(
    ! [A_314] : r1_xboole_0(k2_xboole_0(A_314,'#skF_6'),k4_xboole_0('#skF_5',A_314)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16526,c_7497])).

tff(c_16923,plain,(
    r1_xboole_0(k2_xboole_0('#skF_7','#skF_6'),'#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1027,c_16864])).

tff(c_16972,plain,(
    r1_xboole_0(k2_xboole_0('#skF_6','#skF_7'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_16923])).

tff(c_16983,plain,(
    k3_xboole_0(k2_xboole_0('#skF_6','#skF_7'),'#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_16972,c_4])).

tff(c_16990,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_843,c_16983])).

tff(c_16991,plain,(
    r1_xboole_0('#skF_2',k2_xboole_0('#skF_4','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_17052,plain,(
    r1_xboole_0(k2_xboole_0('#skF_4','#skF_3'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_16991,c_8])).

tff(c_17254,plain,(
    ! [A_320,C_321,B_322] :
      ( r1_xboole_0(A_320,C_321)
      | ~ r1_xboole_0(B_322,C_321)
      | ~ r1_tarski(A_320,B_322) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_19599,plain,(
    ! [A_387] :
      ( r1_xboole_0(A_387,'#skF_2')
      | ~ r1_tarski(A_387,k2_xboole_0('#skF_4','#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_17052,c_17254])).

tff(c_19636,plain,(
    r1_xboole_0('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_94,c_19599])).

tff(c_19646,plain,(
    k3_xboole_0('#skF_3','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_19636,c_4])).

tff(c_19653,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_218,c_19646])).

tff(c_19654,plain,(
    r1_xboole_0('#skF_2',k2_xboole_0('#skF_4','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_45])).

tff(c_19703,plain,(
    r1_xboole_0(k2_xboole_0('#skF_4','#skF_3'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_19654,c_8])).

tff(c_19845,plain,(
    ! [A_397,C_398,B_399] :
      ( r1_xboole_0(A_397,C_398)
      | ~ r1_xboole_0(B_399,C_398)
      | ~ r1_tarski(A_397,B_399) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_21371,plain,(
    ! [A_448] :
      ( r1_xboole_0(A_448,'#skF_2')
      | ~ r1_tarski(A_448,k2_xboole_0('#skF_4','#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_19703,c_19845])).

tff(c_21414,plain,(
    r1_xboole_0('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_94,c_21371])).

tff(c_21424,plain,(
    k3_xboole_0('#skF_3','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_21414,c_4])).

tff(c_21431,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_218,c_21424])).

tff(c_21432,plain,(
    r1_xboole_0('#skF_2',k2_xboole_0('#skF_4','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_47])).

tff(c_21475,plain,(
    r1_xboole_0(k2_xboole_0('#skF_4','#skF_3'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_21432,c_8])).

tff(c_21580,plain,(
    ! [A_459,C_460,B_461] :
      ( r1_xboole_0(A_459,C_460)
      | ~ r1_xboole_0(B_461,C_460)
      | ~ r1_tarski(A_459,B_461) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_22845,plain,(
    ! [A_500] :
      ( r1_xboole_0(A_500,'#skF_2')
      | ~ r1_tarski(A_500,k2_xboole_0('#skF_4','#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_21475,c_21580])).

tff(c_22888,plain,(
    r1_xboole_0('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_94,c_22845])).

tff(c_22898,plain,(
    k3_xboole_0('#skF_3','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_22888,c_4])).

tff(c_22905,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_218,c_22898])).

tff(c_22907,plain,(
    r1_xboole_0('#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_22956,plain,(
    ! [A_505,B_506] :
      ( r1_xboole_0(A_505,B_506)
      | k3_xboole_0(A_505,B_506) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_23029,plain,(
    ! [B_511,A_512] :
      ( r1_xboole_0(B_511,A_512)
      | k3_xboole_0(A_512,B_511) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_22956,c_8])).

tff(c_22906,plain,
    ( ~ r1_xboole_0('#skF_2','#skF_4')
    | r1_xboole_0('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_22917,plain,(
    ~ r1_xboole_0('#skF_2','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_22906])).

tff(c_23039,plain,(
    k3_xboole_0('#skF_4','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_23029,c_22917])).

tff(c_22967,plain,(
    ! [B_506,A_505] :
      ( r1_xboole_0(B_506,A_505)
      | k3_xboole_0(A_505,B_506) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_22956,c_8])).

tff(c_23293,plain,(
    ~ r1_xboole_0('#skF_5',k2_xboole_0('#skF_6','#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_23300,plain,(
    k3_xboole_0(k2_xboole_0('#skF_6','#skF_7'),'#skF_5') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_22967,c_23293])).

tff(c_23138,plain,(
    r1_xboole_0('#skF_5','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_45])).

tff(c_23144,plain,(
    k3_xboole_0('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_23138,c_4])).

tff(c_23187,plain,(
    ! [A_517,B_518] : k2_xboole_0(k3_xboole_0(A_517,B_518),k4_xboole_0(A_517,B_518)) = A_517 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_23211,plain,(
    k2_xboole_0(k1_xboole_0,k4_xboole_0('#skF_5','#skF_6')) = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_23144,c_23187])).

tff(c_23466,plain,(
    k4_xboole_0('#skF_5','#skF_6') = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_23211,c_101])).

tff(c_23041,plain,(
    r1_xboole_0('#skF_5','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_47])).

tff(c_23047,plain,(
    k3_xboole_0('#skF_5','#skF_7') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_23041,c_4])).

tff(c_23953,plain,(
    ! [A_552,B_553,C_554] : k2_xboole_0(k4_xboole_0(A_552,B_553),k3_xboole_0(A_552,C_554)) = k4_xboole_0(A_552,k4_xboole_0(B_553,C_554)) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_24007,plain,(
    ! [B_553] : k4_xboole_0('#skF_5',k4_xboole_0(B_553,'#skF_7')) = k2_xboole_0(k4_xboole_0('#skF_5',B_553),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_23047,c_23953])).

tff(c_24046,plain,(
    ! [B_553] : k4_xboole_0('#skF_5',k4_xboole_0(B_553,'#skF_7')) = k4_xboole_0('#skF_5',B_553) ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_2,c_24007])).

tff(c_39495,plain,(
    ! [B_754] : k4_xboole_0('#skF_5',k4_xboole_0(B_754,'#skF_7')) = k4_xboole_0('#skF_5',B_754) ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_2,c_24007])).

tff(c_39688,plain,(
    ! [A_17] : k4_xboole_0('#skF_5',k4_xboole_0(A_17,'#skF_7')) = k4_xboole_0('#skF_5',k2_xboole_0(A_17,'#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_39495])).

tff(c_95007,plain,(
    ! [A_1298] : k4_xboole_0('#skF_5',k2_xboole_0(A_1298,'#skF_7')) = k4_xboole_0('#skF_5',A_1298) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24046,c_39688])).

tff(c_22939,plain,(
    ! [A_503,B_504] :
      ( k3_xboole_0(A_503,B_504) = k1_xboole_0
      | ~ r1_xboole_0(A_503,B_504) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_22947,plain,(
    k3_xboole_0('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_22907,c_22939])).

tff(c_23547,plain,(
    ! [A_526,B_527,C_528] :
      ( ~ r1_xboole_0(A_526,B_527)
      | ~ r2_hidden(C_528,k3_xboole_0(A_526,B_527)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_23571,plain,(
    ! [C_528] :
      ( ~ r1_xboole_0('#skF_2','#skF_3')
      | ~ r2_hidden(C_528,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22947,c_23547])).

tff(c_23586,plain,(
    ! [C_528] : ~ r2_hidden(C_528,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22907,c_23571])).

tff(c_22968,plain,(
    ! [A_507,B_508] : k4_xboole_0(A_507,k4_xboole_0(A_507,B_508)) = k3_xboole_0(A_507,B_508) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_22983,plain,(
    ! [A_16] : k4_xboole_0(A_16,A_16) = k3_xboole_0(A_16,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_22968])).

tff(c_22986,plain,(
    ! [A_16] : k4_xboole_0(A_16,A_16) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_22983])).

tff(c_23057,plain,(
    ! [A_513,B_514] : k4_xboole_0(k2_xboole_0(A_513,B_514),B_514) = k4_xboole_0(A_513,B_514) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_23073,plain,(
    ! [A_40] : k4_xboole_0(k1_xboole_0,A_40) = k4_xboole_0(A_40,A_40) ),
    inference(superposition,[status(thm),theory(equality)],[c_101,c_23057])).

tff(c_23090,plain,(
    ! [A_40] : k4_xboole_0(k1_xboole_0,A_40) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22986,c_23073])).

tff(c_24037,plain,(
    ! [A_16,C_554] : k4_xboole_0(A_16,k4_xboole_0(k1_xboole_0,C_554)) = k2_xboole_0(A_16,k3_xboole_0(A_16,C_554)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_23953])).

tff(c_24052,plain,(
    ! [A_16,C_554] : k2_xboole_0(A_16,k3_xboole_0(A_16,C_554)) = A_16 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_23090,c_24037])).

tff(c_24313,plain,(
    ! [B_566,A_567] : k4_xboole_0(k2_xboole_0(B_566,A_567),B_566) = k4_xboole_0(A_567,B_566) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_23057])).

tff(c_24345,plain,(
    ! [A_16,C_554] : k4_xboole_0(k3_xboole_0(A_16,C_554),A_16) = k4_xboole_0(A_16,A_16) ),
    inference(superposition,[status(thm),theory(equality)],[c_24052,c_24313])).

tff(c_24383,plain,(
    ! [A_16,C_554] : k4_xboole_0(k3_xboole_0(A_16,C_554),A_16) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22986,c_24345])).

tff(c_23362,plain,(
    ! [A_523,B_524] : k2_xboole_0(A_523,k4_xboole_0(B_524,A_523)) = k2_xboole_0(A_523,B_524) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_23396,plain,(
    ! [A_19,B_20] : k2_xboole_0(k4_xboole_0(A_19,B_20),k3_xboole_0(A_19,B_20)) = k2_xboole_0(k4_xboole_0(A_19,B_20),A_19) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_23362])).

tff(c_27281,plain,(
    ! [A_626,B_627] : k2_xboole_0(k4_xboole_0(A_626,B_627),k3_xboole_0(A_626,B_627)) = k2_xboole_0(A_626,k4_xboole_0(A_626,B_627)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_23396])).

tff(c_27299,plain,(
    ! [A_626,B_627] : k4_xboole_0(A_626,k4_xboole_0(B_627,B_627)) = k2_xboole_0(A_626,k4_xboole_0(A_626,B_627)) ),
    inference(superposition,[status(thm),theory(equality)],[c_27281,c_28])).

tff(c_27479,plain,(
    ! [A_626,B_627] : k2_xboole_0(A_626,k4_xboole_0(A_626,B_627)) = A_626 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_22986,c_27299])).

tff(c_22987,plain,(
    ! [A_509] : k4_xboole_0(A_509,A_509) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_22983])).

tff(c_22992,plain,(
    ! [A_509] : k4_xboole_0(A_509,k1_xboole_0) = k3_xboole_0(A_509,A_509) ),
    inference(superposition,[status(thm),theory(equality)],[c_22987,c_24])).

tff(c_23004,plain,(
    ! [A_509] : k3_xboole_0(A_509,A_509) = A_509 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_22992])).

tff(c_28069,plain,(
    ! [A_635,C_636,B_637] : k2_xboole_0(k3_xboole_0(A_635,C_636),k4_xboole_0(A_635,B_637)) = k4_xboole_0(A_635,k4_xboole_0(B_637,C_636)) ),
    inference(superposition,[status(thm),theory(equality)],[c_23953,c_2])).

tff(c_28252,plain,(
    ! [A_509,B_637] : k4_xboole_0(A_509,k4_xboole_0(B_637,A_509)) = k2_xboole_0(A_509,k4_xboole_0(A_509,B_637)) ),
    inference(superposition,[status(thm),theory(equality)],[c_23004,c_28069])).

tff(c_28496,plain,(
    ! [A_640,B_641] : k4_xboole_0(A_640,k4_xboole_0(B_641,A_640)) = A_640 ),
    inference(demodulation,[status(thm),theory(equality)],[c_27479,c_28252])).

tff(c_23193,plain,(
    ! [A_517,B_518] : k4_xboole_0(k3_xboole_0(A_517,B_518),k4_xboole_0(A_517,B_518)) = k4_xboole_0(A_517,k4_xboole_0(A_517,B_518)) ),
    inference(superposition,[status(thm),theory(equality)],[c_23187,c_22])).

tff(c_23246,plain,(
    ! [A_517,B_518] : k4_xboole_0(k3_xboole_0(A_517,B_518),k4_xboole_0(A_517,B_518)) = k3_xboole_0(A_517,B_518) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_23193])).

tff(c_28564,plain,(
    ! [A_640,B_641] : k4_xboole_0(k3_xboole_0(A_640,k4_xboole_0(B_641,A_640)),A_640) = k3_xboole_0(A_640,k4_xboole_0(B_641,A_640)) ),
    inference(superposition,[status(thm),theory(equality)],[c_28496,c_23246])).

tff(c_28787,plain,(
    ! [A_642,B_643] : k3_xboole_0(A_642,k4_xboole_0(B_643,A_642)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24383,c_28564])).

tff(c_28877,plain,(
    ! [A_642,B_643] :
      ( r2_hidden('#skF_1'(A_642,k4_xboole_0(B_643,A_642)),k1_xboole_0)
      | r1_xboole_0(A_642,k4_xboole_0(B_643,A_642)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28787,c_10])).

tff(c_29005,plain,(
    ! [A_642,B_643] : r1_xboole_0(A_642,k4_xboole_0(B_643,A_642)) ),
    inference(negUnitSimplification,[status(thm)],[c_23586,c_28877])).

tff(c_95489,plain,(
    ! [A_1299] : r1_xboole_0(k2_xboole_0(A_1299,'#skF_7'),k4_xboole_0('#skF_5',A_1299)) ),
    inference(superposition,[status(thm),theory(equality)],[c_95007,c_29005])).

tff(c_95583,plain,(
    r1_xboole_0(k2_xboole_0('#skF_6','#skF_7'),'#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_23466,c_95489])).

tff(c_95635,plain,(
    k3_xboole_0(k2_xboole_0('#skF_6','#skF_7'),'#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_95583,c_4])).

tff(c_95648,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_23300,c_95635])).

tff(c_95649,plain,(
    r1_xboole_0('#skF_2',k2_xboole_0('#skF_4','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_95657,plain,(
    r1_xboole_0(k2_xboole_0('#skF_4','#skF_3'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_95649,c_8])).

tff(c_96075,plain,(
    ! [A_1309,C_1310,B_1311] :
      ( r1_xboole_0(A_1309,C_1310)
      | ~ r1_xboole_0(B_1311,C_1310)
      | ~ r1_tarski(A_1309,B_1311) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_101821,plain,(
    ! [A_1433] :
      ( r1_xboole_0(A_1433,'#skF_2')
      | ~ r1_tarski(A_1433,k2_xboole_0('#skF_4','#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_95657,c_96075])).

tff(c_101854,plain,(
    r1_xboole_0('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_101821])).

tff(c_101859,plain,(
    k3_xboole_0('#skF_4','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_101854,c_4])).

tff(c_101866,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_23039,c_101859])).

tff(c_101867,plain,(
    r1_xboole_0('#skF_2',k2_xboole_0('#skF_4','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_45])).

tff(c_101908,plain,(
    r1_xboole_0(k2_xboole_0('#skF_4','#skF_3'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_101867,c_8])).

tff(c_102340,plain,(
    ! [A_1448,C_1449,B_1450] :
      ( r1_xboole_0(A_1448,C_1449)
      | ~ r1_xboole_0(B_1450,C_1449)
      | ~ r1_tarski(A_1448,B_1450) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_104999,plain,(
    ! [A_1529] :
      ( r1_xboole_0(A_1529,'#skF_2')
      | ~ r1_tarski(A_1529,k2_xboole_0('#skF_4','#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_101908,c_102340])).

tff(c_105032,plain,(
    r1_xboole_0('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_104999])).

tff(c_105037,plain,(
    k3_xboole_0('#skF_4','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_105032,c_4])).

tff(c_105044,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_23039,c_105037])).

tff(c_105045,plain,(
    r1_xboole_0('#skF_2',k2_xboole_0('#skF_4','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_47])).

tff(c_105061,plain,(
    r1_xboole_0(k2_xboole_0('#skF_4','#skF_3'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_105045,c_8])).

tff(c_105514,plain,(
    ! [A_1551,C_1552,B_1553] :
      ( r1_xboole_0(A_1551,C_1552)
      | ~ r1_xboole_0(B_1553,C_1552)
      | ~ r1_tarski(A_1551,B_1553) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_109015,plain,(
    ! [A_1643] :
      ( r1_xboole_0(A_1643,'#skF_2')
      | ~ r1_tarski(A_1643,k2_xboole_0('#skF_4','#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_105061,c_105514])).

tff(c_109065,plain,(
    r1_xboole_0('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_109015])).

tff(c_109070,plain,(
    k3_xboole_0('#skF_4','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_109065,c_4])).

tff(c_109077,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_23039,c_109070])).

tff(c_109079,plain,(
    r1_xboole_0('#skF_2','#skF_4') ),
    inference(splitRight,[status(thm)],[c_22906])).

tff(c_44,plain,
    ( ~ r1_xboole_0('#skF_2','#skF_4')
    | ~ r1_xboole_0('#skF_2','#skF_3')
    | ~ r1_xboole_0('#skF_5',k2_xboole_0('#skF_6','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_109195,plain,(
    ~ r1_xboole_0('#skF_5',k2_xboole_0('#skF_6','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22907,c_109079,c_44])).

tff(c_109210,plain,(
    k3_xboole_0(k2_xboole_0('#skF_6','#skF_7'),'#skF_5') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_109201,c_109195])).

tff(c_109078,plain,(
    r1_xboole_0('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_22906])).

tff(c_109094,plain,(
    ! [A_1644,B_1645] :
      ( k3_xboole_0(A_1644,B_1645) = k1_xboole_0
      | ~ r1_xboole_0(A_1644,B_1645) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_109116,plain,(
    k3_xboole_0('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_109078,c_109094])).

tff(c_109643,plain,(
    ! [A_1673,B_1674] : k2_xboole_0(k3_xboole_0(A_1673,B_1674),k4_xboole_0(A_1673,B_1674)) = A_1673 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_109703,plain,(
    k2_xboole_0(k1_xboole_0,k4_xboole_0('#skF_5','#skF_6')) = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_109116,c_109643])).

tff(c_110411,plain,(
    k4_xboole_0('#skF_5','#skF_6') = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_109703,c_101])).

tff(c_109213,plain,(
    ! [A_1652,B_1653] : k4_xboole_0(A_1652,k4_xboole_0(A_1652,B_1653)) = k3_xboole_0(A_1652,B_1653) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_109228,plain,(
    ! [A_16] : k4_xboole_0(A_16,A_16) = k3_xboole_0(A_16,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_109213])).

tff(c_109231,plain,(
    ! [A_16] : k4_xboole_0(A_16,A_16) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_109228])).

tff(c_109457,plain,(
    ! [A_1665,B_1666] : k4_xboole_0(k2_xboole_0(A_1665,B_1666),B_1666) = k4_xboole_0(A_1665,B_1666) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_109488,plain,(
    ! [A_40] : k4_xboole_0(k1_xboole_0,A_40) = k4_xboole_0(A_40,A_40) ),
    inference(superposition,[status(thm),theory(equality)],[c_101,c_109457])).

tff(c_109508,plain,(
    ! [A_40] : k4_xboole_0(k1_xboole_0,A_40) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_109231,c_109488])).

tff(c_110103,plain,(
    ! [A_1696,B_1697,C_1698] : k2_xboole_0(k4_xboole_0(A_1696,B_1697),k3_xboole_0(A_1696,C_1698)) = k4_xboole_0(A_1696,k4_xboole_0(B_1697,C_1698)) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_110187,plain,(
    ! [A_16,C_1698] : k4_xboole_0(A_16,k4_xboole_0(k1_xboole_0,C_1698)) = k2_xboole_0(A_16,k3_xboole_0(A_16,C_1698)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_110103])).

tff(c_110203,plain,(
    ! [A_16,C_1698] : k2_xboole_0(A_16,k3_xboole_0(A_16,C_1698)) = A_16 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_109508,c_110187])).

tff(c_110726,plain,(
    ! [A_1711,B_1712] : k4_xboole_0(k2_xboole_0(A_1711,B_1712),A_1711) = k4_xboole_0(B_1712,A_1711) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_109457])).

tff(c_110770,plain,(
    ! [A_16,C_1698] : k4_xboole_0(k3_xboole_0(A_16,C_1698),A_16) = k4_xboole_0(A_16,A_16) ),
    inference(superposition,[status(thm),theory(equality)],[c_110203,c_110726])).

tff(c_110812,plain,(
    ! [A_16,C_1698] : k4_xboole_0(k3_xboole_0(A_16,C_1698),A_16) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_109231,c_110770])).

tff(c_109494,plain,(
    ! [A_1,B_2] : k4_xboole_0(k2_xboole_0(A_1,B_2),A_1) = k4_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_109457])).

tff(c_18,plain,(
    ! [A_14,B_15] : k2_xboole_0(A_14,k4_xboole_0(B_15,A_14)) = k2_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_110786,plain,(
    ! [B_15,A_14] : k4_xboole_0(k4_xboole_0(B_15,A_14),A_14) = k4_xboole_0(k2_xboole_0(A_14,B_15),A_14) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_110726])).

tff(c_124829,plain,(
    ! [B_1885,A_1886] : k4_xboole_0(k4_xboole_0(B_1885,A_1886),A_1886) = k4_xboole_0(B_1885,A_1886) ),
    inference(demodulation,[status(thm),theory(equality)],[c_109494,c_110786])).

tff(c_109649,plain,(
    ! [A_1673,B_1674] : k4_xboole_0(k3_xboole_0(A_1673,B_1674),k4_xboole_0(A_1673,B_1674)) = k4_xboole_0(A_1673,k4_xboole_0(A_1673,B_1674)) ),
    inference(superposition,[status(thm),theory(equality)],[c_109643,c_22])).

tff(c_109714,plain,(
    ! [A_1673,B_1674] : k4_xboole_0(k3_xboole_0(A_1673,B_1674),k4_xboole_0(A_1673,B_1674)) = k3_xboole_0(A_1673,B_1674) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_109649])).

tff(c_124898,plain,(
    ! [B_1885,A_1886] : k4_xboole_0(k3_xboole_0(k4_xboole_0(B_1885,A_1886),A_1886),k4_xboole_0(B_1885,A_1886)) = k3_xboole_0(k4_xboole_0(B_1885,A_1886),A_1886) ),
    inference(superposition,[status(thm),theory(equality)],[c_124829,c_109714])).

tff(c_125161,plain,(
    ! [B_1887,A_1888] : k3_xboole_0(k4_xboole_0(B_1887,A_1888),A_1888) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_110812,c_124898])).

tff(c_109211,plain,(
    ! [B_1650,A_1651] :
      ( k3_xboole_0(B_1650,A_1651) = k1_xboole_0
      | k3_xboole_0(A_1651,B_1650) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_109201,c_4])).

tff(c_125405,plain,(
    ! [A_1888,B_1887] : k3_xboole_0(A_1888,k4_xboole_0(B_1887,A_1888)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_125161,c_109211])).

tff(c_109485,plain,(
    ! [A_14,B_15] : k4_xboole_0(k2_xboole_0(A_14,B_15),k4_xboole_0(B_15,A_14)) = k4_xboole_0(A_14,k4_xboole_0(B_15,A_14)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_109457])).

tff(c_109469,plain,(
    ! [B_1666,A_1665] : k2_xboole_0(B_1666,k4_xboole_0(A_1665,B_1666)) = k2_xboole_0(B_1666,k2_xboole_0(A_1665,B_1666)) ),
    inference(superposition,[status(thm),theory(equality)],[c_109457,c_18])).

tff(c_109504,plain,(
    ! [B_1666,A_1665] : k2_xboole_0(B_1666,k2_xboole_0(A_1665,B_1666)) = k2_xboole_0(B_1666,A_1665) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_109469])).

tff(c_115496,plain,(
    ! [A_1801,B_1802] : k4_xboole_0(k2_xboole_0(A_1801,B_1802),k4_xboole_0(A_1801,B_1802)) = k3_xboole_0(k2_xboole_0(A_1801,B_1802),B_1802) ),
    inference(superposition,[status(thm),theory(equality)],[c_109457,c_24])).

tff(c_115657,plain,(
    ! [A_17,B_18] : k4_xboole_0(k2_xboole_0(k2_xboole_0(A_17,B_18),B_18),k4_xboole_0(A_17,B_18)) = k3_xboole_0(k2_xboole_0(k2_xboole_0(A_17,B_18),B_18),B_18) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_115496])).

tff(c_146504,plain,(
    ! [B_2174,A_2175] : k4_xboole_0(B_2174,k4_xboole_0(A_2175,B_2174)) = k3_xboole_0(k2_xboole_0(B_2174,A_2175),B_2174) ),
    inference(demodulation,[status(thm),theory(equality)],[c_109485,c_109504,c_109504,c_2,c_2,c_115657])).

tff(c_109232,plain,(
    ! [A_1654,B_1655] : k2_xboole_0(A_1654,k4_xboole_0(B_1655,A_1654)) = k2_xboole_0(A_1654,B_1655) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_109251,plain,(
    ! [A_19,B_20] : k2_xboole_0(k4_xboole_0(A_19,B_20),k3_xboole_0(A_19,B_20)) = k2_xboole_0(k4_xboole_0(A_19,B_20),A_19) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_109232])).

tff(c_113883,plain,(
    ! [A_1778,B_1779] : k2_xboole_0(k4_xboole_0(A_1778,B_1779),k3_xboole_0(A_1778,B_1779)) = k2_xboole_0(A_1778,k4_xboole_0(A_1778,B_1779)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_109251])).

tff(c_113898,plain,(
    ! [A_1778,B_1779] : k4_xboole_0(A_1778,k4_xboole_0(B_1779,B_1779)) = k2_xboole_0(A_1778,k4_xboole_0(A_1778,B_1779)) ),
    inference(superposition,[status(thm),theory(equality)],[c_113883,c_28])).

tff(c_114060,plain,(
    ! [A_1778,B_1779] : k2_xboole_0(A_1778,k4_xboole_0(A_1778,B_1779)) = A_1778 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_109231,c_113898])).

tff(c_109263,plain,(
    ! [A_19,B_20] : k2_xboole_0(k4_xboole_0(A_19,B_20),k3_xboole_0(A_19,B_20)) = k2_xboole_0(A_19,k4_xboole_0(A_19,B_20)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_109251])).

tff(c_114110,plain,(
    ! [A_19,B_20] : k2_xboole_0(k4_xboole_0(A_19,B_20),k3_xboole_0(A_19,B_20)) = A_19 ),
    inference(demodulation,[status(thm),theory(equality)],[c_114060,c_109263])).

tff(c_146828,plain,(
    ! [B_2174,A_2175] : k2_xboole_0(k3_xboole_0(k2_xboole_0(B_2174,A_2175),B_2174),k3_xboole_0(B_2174,k4_xboole_0(A_2175,B_2174))) = B_2174 ),
    inference(superposition,[status(thm),theory(equality)],[c_146504,c_114110])).

tff(c_147419,plain,(
    ! [B_2176,A_2177] : k3_xboole_0(k2_xboole_0(B_2176,A_2177),B_2176) = B_2176 ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_2,c_125405,c_146828])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( r1_xboole_0(A_3,B_4)
      | k3_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_109788,plain,(
    ! [A_1679,C_1680,B_1681] :
      ( r1_xboole_0(A_1679,C_1680)
      | ~ r1_xboole_0(B_1681,C_1680)
      | ~ r1_tarski(A_1679,B_1681) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_112621,plain,(
    ! [A_1756,B_1757,A_1758] :
      ( r1_xboole_0(A_1756,B_1757)
      | ~ r1_tarski(A_1756,A_1758)
      | k3_xboole_0(A_1758,B_1757) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_6,c_109788])).

tff(c_112645,plain,(
    ! [A_40,B_1757,B_39] :
      ( r1_xboole_0(A_40,B_1757)
      | k3_xboole_0(k2_xboole_0(B_39,A_40),B_1757) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_94,c_112621])).

tff(c_147762,plain,(
    ! [A_2179,B_2180] :
      ( r1_xboole_0(A_2179,B_2180)
      | k1_xboole_0 != B_2180 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_147419,c_112645])).

tff(c_149135,plain,(
    ! [A_2187,B_2188] :
      ( k3_xboole_0(A_2187,B_2188) = k1_xboole_0
      | k1_xboole_0 != B_2188 ) ),
    inference(resolution,[status(thm)],[c_147762,c_4])).

tff(c_149765,plain,(
    ! [A_2187,B_2188] :
      ( k2_xboole_0(k1_xboole_0,k4_xboole_0(A_2187,B_2188)) = A_2187
      | k1_xboole_0 != B_2188 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_149135,c_26])).

tff(c_151418,plain,(
    ! [A_2187] : k4_xboole_0(A_2187,k1_xboole_0) = A_2187 ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_149765])).

tff(c_36,plain,
    ( ~ r1_xboole_0('#skF_2','#skF_4')
    | ~ r1_xboole_0('#skF_2','#skF_3')
    | r1_xboole_0('#skF_5','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_109129,plain,(
    r1_xboole_0('#skF_5','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22907,c_109079,c_36])).

tff(c_109135,plain,(
    k3_xboole_0('#skF_5','#skF_7') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_109129,c_4])).

tff(c_110109,plain,(
    ! [A_1696,B_1697,C_1698] : k4_xboole_0(k4_xboole_0(A_1696,k4_xboole_0(B_1697,C_1698)),k3_xboole_0(A_1696,C_1698)) = k4_xboole_0(k4_xboole_0(A_1696,B_1697),k3_xboole_0(A_1696,C_1698)) ),
    inference(superposition,[status(thm),theory(equality)],[c_110103,c_22])).

tff(c_118795,plain,(
    ! [A_1837,B_1838,C_1839] : k4_xboole_0(k4_xboole_0(A_1837,k4_xboole_0(B_1838,C_1839)),k3_xboole_0(A_1837,C_1839)) = k4_xboole_0(k4_xboole_0(A_1837,B_1838),k3_xboole_0(A_1837,C_1839)) ),
    inference(superposition,[status(thm),theory(equality)],[c_110103,c_22])).

tff(c_119073,plain,(
    ! [A_1837,B_2,A_1] : k4_xboole_0(k4_xboole_0(A_1837,k4_xboole_0(B_2,A_1)),k3_xboole_0(A_1837,A_1)) = k4_xboole_0(k4_xboole_0(A_1837,k2_xboole_0(A_1,B_2)),k3_xboole_0(A_1837,A_1)) ),
    inference(superposition,[status(thm),theory(equality)],[c_109494,c_118795])).

tff(c_203598,plain,(
    ! [A_2591,A_2592,B_2593] : k4_xboole_0(k4_xboole_0(A_2591,k2_xboole_0(A_2592,B_2593)),k3_xboole_0(A_2591,A_2592)) = k4_xboole_0(k4_xboole_0(A_2591,B_2593),k3_xboole_0(A_2591,A_2592)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_110109,c_119073])).

tff(c_204319,plain,(
    ! [B_2593] : k4_xboole_0(k4_xboole_0('#skF_5',k2_xboole_0('#skF_7',B_2593)),k1_xboole_0) = k4_xboole_0(k4_xboole_0('#skF_5',B_2593),k3_xboole_0('#skF_5','#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_109135,c_203598])).

tff(c_204488,plain,(
    ! [B_2594] : k4_xboole_0('#skF_5',k2_xboole_0('#skF_7',B_2594)) = k4_xboole_0('#skF_5',B_2594) ),
    inference(demodulation,[status(thm),theory(equality)],[c_151418,c_151418,c_109135,c_204319])).

tff(c_109592,plain,(
    ! [A_1669,B_1670,C_1671] :
      ( ~ r1_xboole_0(A_1669,B_1670)
      | ~ r2_hidden(C_1671,k3_xboole_0(A_1669,B_1670)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_109613,plain,(
    ! [C_1671] :
      ( ~ r1_xboole_0('#skF_5','#skF_7')
      | ~ r2_hidden(C_1671,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_109135,c_109592])).

tff(c_109635,plain,(
    ! [C_1671] : ~ r2_hidden(C_1671,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_109129,c_109613])).

tff(c_125225,plain,(
    ! [B_1887,A_1888] :
      ( r2_hidden('#skF_1'(k4_xboole_0(B_1887,A_1888),A_1888),k1_xboole_0)
      | r1_xboole_0(k4_xboole_0(B_1887,A_1888),A_1888) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_125161,c_10])).

tff(c_125473,plain,(
    ! [B_1889,A_1890] : r1_xboole_0(k4_xboole_0(B_1889,A_1890),A_1890) ),
    inference(negUnitSimplification,[status(thm)],[c_109635,c_125225])).

tff(c_125619,plain,(
    ! [A_1890,B_1889] : r1_xboole_0(A_1890,k4_xboole_0(B_1889,A_1890)) ),
    inference(resolution,[status(thm)],[c_125473,c_8])).

tff(c_205070,plain,(
    ! [B_2595] : r1_xboole_0(k2_xboole_0('#skF_7',B_2595),k4_xboole_0('#skF_5',B_2595)) ),
    inference(superposition,[status(thm),theory(equality)],[c_204488,c_125619])).

tff(c_205165,plain,(
    r1_xboole_0(k2_xboole_0('#skF_7','#skF_6'),'#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_110411,c_205070])).

tff(c_205211,plain,(
    r1_xboole_0(k2_xboole_0('#skF_6','#skF_7'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_205165])).

tff(c_205221,plain,(
    k3_xboole_0(k2_xboole_0('#skF_6','#skF_7'),'#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_205211,c_4])).

tff(c_205234,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_109210,c_205221])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n003.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 18:50:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 41.56/32.61  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 41.70/32.65  
% 41.70/32.65  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 41.70/32.65  %$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 41.70/32.65  
% 41.70/32.65  %Foreground sorts:
% 41.70/32.65  
% 41.70/32.65  
% 41.70/32.65  %Background operators:
% 41.70/32.65  
% 41.70/32.65  
% 41.70/32.65  %Foreground operators:
% 41.70/32.65  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 41.70/32.65  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 41.70/32.65  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 41.70/32.65  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 41.70/32.65  tff('#skF_7', type, '#skF_7': $i).
% 41.70/32.65  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 41.70/32.65  tff('#skF_5', type, '#skF_5': $i).
% 41.70/32.65  tff('#skF_6', type, '#skF_6': $i).
% 41.70/32.65  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 41.70/32.65  tff('#skF_2', type, '#skF_2': $i).
% 41.70/32.65  tff('#skF_3', type, '#skF_3': $i).
% 41.70/32.65  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 41.70/32.65  tff('#skF_4', type, '#skF_4': $i).
% 41.70/32.65  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 41.70/32.65  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 41.70/32.65  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 41.70/32.65  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 41.70/32.65  
% 41.99/32.69  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 41.99/32.69  tff(f_35, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 41.99/32.69  tff(f_90, negated_conjecture, ~(![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_xboole_1)).
% 41.99/32.69  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 41.99/32.69  tff(f_73, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 41.99/32.69  tff(f_63, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_xboole_1)).
% 41.99/32.69  tff(f_51, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 41.99/32.69  tff(f_65, axiom, (![A, B, C]: (k4_xboole_0(A, k4_xboole_0(B, C)) = k2_xboole_0(k4_xboole_0(A, B), k3_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_xboole_1)).
% 41.99/32.69  tff(f_59, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_xboole_1)).
% 41.99/32.69  tff(f_49, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 41.99/32.69  tff(f_53, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 41.99/32.69  tff(f_57, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 41.99/32.69  tff(f_61, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 41.99/32.69  tff(f_55, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 41.99/32.69  tff(f_71, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_xboole_1)).
% 41.99/32.69  tff(c_109161, plain, (![A_1646, B_1647]: (r1_xboole_0(A_1646, B_1647) | k3_xboole_0(A_1646, B_1647)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 41.99/32.69  tff(c_8, plain, (![B_6, A_5]: (r1_xboole_0(B_6, A_5) | ~r1_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 41.99/32.69  tff(c_109201, plain, (![B_1650, A_1651]: (r1_xboole_0(B_1650, A_1651) | k3_xboole_0(A_1651, B_1650)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_109161, c_8])).
% 41.99/32.69  tff(c_194, plain, (![A_45, B_46]: (r1_xboole_0(A_45, B_46) | k3_xboole_0(A_45, B_46)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 41.99/32.69  tff(c_208, plain, (![B_49, A_50]: (r1_xboole_0(B_49, A_50) | k3_xboole_0(A_50, B_49)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_194, c_8])).
% 41.99/32.69  tff(c_40, plain, (~r1_xboole_0('#skF_2', '#skF_4') | ~r1_xboole_0('#skF_2', '#skF_3') | r1_xboole_0('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_90])).
% 41.99/32.69  tff(c_173, plain, (~r1_xboole_0('#skF_2', '#skF_3')), inference(splitLeft, [status(thm)], [c_40])).
% 41.99/32.69  tff(c_218, plain, (k3_xboole_0('#skF_3', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_208, c_173])).
% 41.99/32.69  tff(c_79, plain, (![B_39, A_40]: (k2_xboole_0(B_39, A_40)=k2_xboole_0(A_40, B_39))), inference(cnfTransformation, [status(thm)], [f_27])).
% 41.99/32.69  tff(c_32, plain, (![A_29, B_30]: (r1_tarski(A_29, k2_xboole_0(A_29, B_30)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 41.99/32.69  tff(c_94, plain, (![A_40, B_39]: (r1_tarski(A_40, k2_xboole_0(B_39, A_40)))), inference(superposition, [status(thm), theory('equality')], [c_79, c_32])).
% 41.99/32.69  tff(c_201, plain, (![B_46, A_45]: (r1_xboole_0(B_46, A_45) | k3_xboole_0(A_45, B_46)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_194, c_8])).
% 41.99/32.69  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 41.99/32.69  tff(c_42, plain, (r1_xboole_0('#skF_2', k2_xboole_0('#skF_3', '#skF_4')) | ~r1_xboole_0('#skF_5', k2_xboole_0('#skF_6', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_90])).
% 41.99/32.69  tff(c_46, plain, (r1_xboole_0('#skF_2', k2_xboole_0('#skF_4', '#skF_3')) | ~r1_xboole_0('#skF_5', k2_xboole_0('#skF_6', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_42])).
% 41.99/32.69  tff(c_790, plain, (~r1_xboole_0('#skF_5', k2_xboole_0('#skF_6', '#skF_7'))), inference(splitLeft, [status(thm)], [c_46])).
% 41.99/32.69  tff(c_843, plain, (k3_xboole_0(k2_xboole_0('#skF_6', '#skF_7'), '#skF_5')!=k1_xboole_0), inference(resolution, [status(thm)], [c_201, c_790])).
% 41.99/32.69  tff(c_34, plain, (r1_xboole_0('#skF_2', k2_xboole_0('#skF_3', '#skF_4')) | r1_xboole_0('#skF_5', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_90])).
% 41.99/32.69  tff(c_47, plain, (r1_xboole_0('#skF_2', k2_xboole_0('#skF_4', '#skF_3')) | r1_xboole_0('#skF_5', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_34])).
% 41.99/32.69  tff(c_698, plain, (r1_xboole_0('#skF_5', '#skF_7')), inference(splitLeft, [status(thm)], [c_47])).
% 41.99/32.69  tff(c_4, plain, (![A_3, B_4]: (k3_xboole_0(A_3, B_4)=k1_xboole_0 | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 41.99/32.69  tff(c_704, plain, (k3_xboole_0('#skF_5', '#skF_7')=k1_xboole_0), inference(resolution, [status(thm)], [c_698, c_4])).
% 41.99/32.69  tff(c_26, plain, (![A_21, B_22]: (k2_xboole_0(k3_xboole_0(A_21, B_22), k4_xboole_0(A_21, B_22))=A_21)), inference(cnfTransformation, [status(thm)], [f_63])).
% 41.99/32.69  tff(c_720, plain, (k2_xboole_0(k1_xboole_0, k4_xboole_0('#skF_5', '#skF_7'))='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_704, c_26])).
% 41.99/32.69  tff(c_14, plain, (![A_12]: (k2_xboole_0(A_12, k1_xboole_0)=A_12)), inference(cnfTransformation, [status(thm)], [f_51])).
% 41.99/32.69  tff(c_101, plain, (![A_40]: (k2_xboole_0(k1_xboole_0, A_40)=A_40)), inference(superposition, [status(thm), theory('equality')], [c_79, c_14])).
% 41.99/32.69  tff(c_1027, plain, (k4_xboole_0('#skF_5', '#skF_7')='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_720, c_101])).
% 41.99/32.69  tff(c_38, plain, (r1_xboole_0('#skF_2', k2_xboole_0('#skF_3', '#skF_4')) | r1_xboole_0('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_90])).
% 41.99/32.69  tff(c_45, plain, (r1_xboole_0('#skF_2', k2_xboole_0('#skF_4', '#skF_3')) | r1_xboole_0('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_38])).
% 41.99/32.69  tff(c_763, plain, (r1_xboole_0('#skF_5', '#skF_6')), inference(splitLeft, [status(thm)], [c_45])).
% 41.99/32.69  tff(c_769, plain, (k3_xboole_0('#skF_5', '#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_763, c_4])).
% 41.99/32.69  tff(c_1197, plain, (![A_97, B_98, C_99]: (k2_xboole_0(k4_xboole_0(A_97, B_98), k3_xboole_0(A_97, C_99))=k4_xboole_0(A_97, k4_xboole_0(B_98, C_99)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 41.99/32.69  tff(c_1239, plain, (![B_98]: (k4_xboole_0('#skF_5', k4_xboole_0(B_98, '#skF_6'))=k2_xboole_0(k4_xboole_0('#skF_5', B_98), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_769, c_1197])).
% 41.99/32.69  tff(c_1277, plain, (![B_98]: (k4_xboole_0('#skF_5', k4_xboole_0(B_98, '#skF_6'))=k4_xboole_0('#skF_5', B_98))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_1239])).
% 41.99/32.69  tff(c_22, plain, (![A_17, B_18]: (k4_xboole_0(k2_xboole_0(A_17, B_18), B_18)=k4_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_59])).
% 41.99/32.69  tff(c_5127, plain, (![B_185]: (k4_xboole_0('#skF_5', k4_xboole_0(B_185, '#skF_6'))=k4_xboole_0('#skF_5', B_185))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_1239])).
% 41.99/32.69  tff(c_5233, plain, (![A_17]: (k4_xboole_0('#skF_5', k4_xboole_0(A_17, '#skF_6'))=k4_xboole_0('#skF_5', k2_xboole_0(A_17, '#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_22, c_5127])).
% 41.99/32.69  tff(c_16526, plain, (![A_311]: (k4_xboole_0('#skF_5', k2_xboole_0(A_311, '#skF_6'))=k4_xboole_0('#skF_5', A_311))), inference(demodulation, [status(thm), theory('equality')], [c_1277, c_5233])).
% 41.99/32.69  tff(c_845, plain, (![A_76, B_77, C_78]: (~r1_xboole_0(A_76, B_77) | ~r2_hidden(C_78, k3_xboole_0(A_76, B_77)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 41.99/32.69  tff(c_854, plain, (![C_78]: (~r1_xboole_0('#skF_5', '#skF_6') | ~r2_hidden(C_78, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_769, c_845])).
% 41.99/32.69  tff(c_870, plain, (![C_78]: (~r2_hidden(C_78, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_763, c_854])).
% 41.99/32.69  tff(c_16, plain, (![A_13]: (k3_xboole_0(A_13, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_53])).
% 41.99/32.69  tff(c_20, plain, (![A_16]: (k4_xboole_0(A_16, k1_xboole_0)=A_16)), inference(cnfTransformation, [status(thm)], [f_57])).
% 41.99/32.69  tff(c_431, plain, (![A_67, B_68]: (k4_xboole_0(A_67, k4_xboole_0(A_67, B_68))=k3_xboole_0(A_67, B_68))), inference(cnfTransformation, [status(thm)], [f_61])).
% 41.99/32.69  tff(c_475, plain, (![A_16]: (k4_xboole_0(A_16, A_16)=k3_xboole_0(A_16, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_20, c_431])).
% 41.99/32.69  tff(c_480, plain, (![A_16]: (k4_xboole_0(A_16, A_16)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_475])).
% 41.99/32.69  tff(c_253, plain, (![A_57, B_58]: (k4_xboole_0(k2_xboole_0(A_57, B_58), B_58)=k4_xboole_0(A_57, B_58))), inference(cnfTransformation, [status(thm)], [f_59])).
% 41.99/32.69  tff(c_275, plain, (![A_40]: (k4_xboole_0(k1_xboole_0, A_40)=k4_xboole_0(A_40, A_40))), inference(superposition, [status(thm), theory('equality')], [c_101, c_253])).
% 41.99/32.69  tff(c_537, plain, (![A_40]: (k4_xboole_0(k1_xboole_0, A_40)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_480, c_275])).
% 41.99/32.69  tff(c_1272, plain, (![A_16, C_99]: (k4_xboole_0(A_16, k4_xboole_0(k1_xboole_0, C_99))=k2_xboole_0(A_16, k3_xboole_0(A_16, C_99)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_1197])).
% 41.99/32.69  tff(c_1284, plain, (![A_16, C_99]: (k2_xboole_0(A_16, k3_xboole_0(A_16, C_99))=A_16)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_537, c_1272])).
% 41.99/32.69  tff(c_1458, plain, (![A_105, B_106]: (k4_xboole_0(k2_xboole_0(A_105, B_106), A_105)=k4_xboole_0(B_106, A_105))), inference(superposition, [status(thm), theory('equality')], [c_2, c_253])).
% 41.99/32.69  tff(c_1496, plain, (![A_16, C_99]: (k4_xboole_0(k3_xboole_0(A_16, C_99), A_16)=k4_xboole_0(A_16, A_16))), inference(superposition, [status(thm), theory('equality')], [c_1284, c_1458])).
% 41.99/32.69  tff(c_1536, plain, (![A_16, C_99]: (k4_xboole_0(k3_xboole_0(A_16, C_99), A_16)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_480, c_1496])).
% 41.99/32.69  tff(c_24, plain, (![A_19, B_20]: (k4_xboole_0(A_19, k4_xboole_0(A_19, B_20))=k3_xboole_0(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_61])).
% 41.99/32.69  tff(c_481, plain, (![A_69, B_70]: (k2_xboole_0(A_69, k4_xboole_0(B_70, A_69))=k2_xboole_0(A_69, B_70))), inference(cnfTransformation, [status(thm)], [f_55])).
% 41.99/32.69  tff(c_509, plain, (![A_19, B_20]: (k2_xboole_0(k4_xboole_0(A_19, B_20), k3_xboole_0(A_19, B_20))=k2_xboole_0(k4_xboole_0(A_19, B_20), A_19))), inference(superposition, [status(thm), theory('equality')], [c_24, c_481])).
% 41.99/32.69  tff(c_4286, plain, (![A_175, B_176]: (k2_xboole_0(k4_xboole_0(A_175, B_176), k3_xboole_0(A_175, B_176))=k2_xboole_0(A_175, k4_xboole_0(A_175, B_176)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_509])).
% 41.99/32.69  tff(c_28, plain, (![A_23, B_24, C_25]: (k2_xboole_0(k4_xboole_0(A_23, B_24), k3_xboole_0(A_23, C_25))=k4_xboole_0(A_23, k4_xboole_0(B_24, C_25)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 41.99/32.69  tff(c_4304, plain, (![A_175, B_176]: (k4_xboole_0(A_175, k4_xboole_0(B_176, B_176))=k2_xboole_0(A_175, k4_xboole_0(A_175, B_176)))), inference(superposition, [status(thm), theory('equality')], [c_4286, c_28])).
% 41.99/32.69  tff(c_4449, plain, (![A_175, B_176]: (k2_xboole_0(A_175, k4_xboole_0(A_175, B_176))=A_175)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_480, c_4304])).
% 41.99/32.69  tff(c_539, plain, (![A_71]: (k4_xboole_0(A_71, A_71)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_475])).
% 41.99/32.69  tff(c_547, plain, (![A_71]: (k4_xboole_0(A_71, k1_xboole_0)=k3_xboole_0(A_71, A_71))), inference(superposition, [status(thm), theory('equality')], [c_539, c_24])).
% 41.99/32.69  tff(c_580, plain, (![A_71]: (k3_xboole_0(A_71, A_71)=A_71)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_547])).
% 41.99/32.69  tff(c_6476, plain, (![A_195, C_196, B_197]: (k2_xboole_0(k3_xboole_0(A_195, C_196), k4_xboole_0(A_195, B_197))=k4_xboole_0(A_195, k4_xboole_0(B_197, C_196)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1197])).
% 41.99/32.69  tff(c_6661, plain, (![A_71, B_197]: (k4_xboole_0(A_71, k4_xboole_0(B_197, A_71))=k2_xboole_0(A_71, k4_xboole_0(A_71, B_197)))), inference(superposition, [status(thm), theory('equality')], [c_580, c_6476])).
% 41.99/32.69  tff(c_6931, plain, (![A_200, B_201]: (k4_xboole_0(A_200, k4_xboole_0(B_201, A_200))=A_200)), inference(demodulation, [status(thm), theory('equality')], [c_4449, c_6661])).
% 41.99/32.69  tff(c_272, plain, (![A_21, B_22]: (k4_xboole_0(k3_xboole_0(A_21, B_22), k4_xboole_0(A_21, B_22))=k4_xboole_0(A_21, k4_xboole_0(A_21, B_22)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_253])).
% 41.99/32.69  tff(c_3799, plain, (![A_21, B_22]: (k4_xboole_0(k3_xboole_0(A_21, B_22), k4_xboole_0(A_21, B_22))=k3_xboole_0(A_21, B_22))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_272])).
% 41.99/32.69  tff(c_6987, plain, (![A_200, B_201]: (k4_xboole_0(k3_xboole_0(A_200, k4_xboole_0(B_201, A_200)), A_200)=k3_xboole_0(A_200, k4_xboole_0(B_201, A_200)))), inference(superposition, [status(thm), theory('equality')], [c_6931, c_3799])).
% 41.99/32.69  tff(c_7258, plain, (![A_202, B_203]: (k3_xboole_0(A_202, k4_xboole_0(B_203, A_202))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1536, c_6987])).
% 41.99/32.69  tff(c_10, plain, (![A_7, B_8]: (r2_hidden('#skF_1'(A_7, B_8), k3_xboole_0(A_7, B_8)) | r1_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_49])).
% 41.99/32.69  tff(c_7357, plain, (![A_202, B_203]: (r2_hidden('#skF_1'(A_202, k4_xboole_0(B_203, A_202)), k1_xboole_0) | r1_xboole_0(A_202, k4_xboole_0(B_203, A_202)))), inference(superposition, [status(thm), theory('equality')], [c_7258, c_10])).
% 41.99/32.69  tff(c_7497, plain, (![A_202, B_203]: (r1_xboole_0(A_202, k4_xboole_0(B_203, A_202)))), inference(negUnitSimplification, [status(thm)], [c_870, c_7357])).
% 41.99/32.69  tff(c_16864, plain, (![A_314]: (r1_xboole_0(k2_xboole_0(A_314, '#skF_6'), k4_xboole_0('#skF_5', A_314)))), inference(superposition, [status(thm), theory('equality')], [c_16526, c_7497])).
% 41.99/32.69  tff(c_16923, plain, (r1_xboole_0(k2_xboole_0('#skF_7', '#skF_6'), '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1027, c_16864])).
% 41.99/32.69  tff(c_16972, plain, (r1_xboole_0(k2_xboole_0('#skF_6', '#skF_7'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_16923])).
% 41.99/32.69  tff(c_16983, plain, (k3_xboole_0(k2_xboole_0('#skF_6', '#skF_7'), '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_16972, c_4])).
% 41.99/32.69  tff(c_16990, plain, $false, inference(negUnitSimplification, [status(thm)], [c_843, c_16983])).
% 41.99/32.69  tff(c_16991, plain, (r1_xboole_0('#skF_2', k2_xboole_0('#skF_4', '#skF_3'))), inference(splitRight, [status(thm)], [c_46])).
% 41.99/32.69  tff(c_17052, plain, (r1_xboole_0(k2_xboole_0('#skF_4', '#skF_3'), '#skF_2')), inference(resolution, [status(thm)], [c_16991, c_8])).
% 41.99/32.69  tff(c_17254, plain, (![A_320, C_321, B_322]: (r1_xboole_0(A_320, C_321) | ~r1_xboole_0(B_322, C_321) | ~r1_tarski(A_320, B_322))), inference(cnfTransformation, [status(thm)], [f_71])).
% 41.99/32.69  tff(c_19599, plain, (![A_387]: (r1_xboole_0(A_387, '#skF_2') | ~r1_tarski(A_387, k2_xboole_0('#skF_4', '#skF_3')))), inference(resolution, [status(thm)], [c_17052, c_17254])).
% 41.99/32.69  tff(c_19636, plain, (r1_xboole_0('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_94, c_19599])).
% 41.99/32.69  tff(c_19646, plain, (k3_xboole_0('#skF_3', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_19636, c_4])).
% 41.99/32.69  tff(c_19653, plain, $false, inference(negUnitSimplification, [status(thm)], [c_218, c_19646])).
% 41.99/32.69  tff(c_19654, plain, (r1_xboole_0('#skF_2', k2_xboole_0('#skF_4', '#skF_3'))), inference(splitRight, [status(thm)], [c_45])).
% 41.99/32.69  tff(c_19703, plain, (r1_xboole_0(k2_xboole_0('#skF_4', '#skF_3'), '#skF_2')), inference(resolution, [status(thm)], [c_19654, c_8])).
% 41.99/32.69  tff(c_19845, plain, (![A_397, C_398, B_399]: (r1_xboole_0(A_397, C_398) | ~r1_xboole_0(B_399, C_398) | ~r1_tarski(A_397, B_399))), inference(cnfTransformation, [status(thm)], [f_71])).
% 41.99/32.69  tff(c_21371, plain, (![A_448]: (r1_xboole_0(A_448, '#skF_2') | ~r1_tarski(A_448, k2_xboole_0('#skF_4', '#skF_3')))), inference(resolution, [status(thm)], [c_19703, c_19845])).
% 41.99/32.69  tff(c_21414, plain, (r1_xboole_0('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_94, c_21371])).
% 41.99/32.69  tff(c_21424, plain, (k3_xboole_0('#skF_3', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_21414, c_4])).
% 41.99/32.69  tff(c_21431, plain, $false, inference(negUnitSimplification, [status(thm)], [c_218, c_21424])).
% 41.99/32.69  tff(c_21432, plain, (r1_xboole_0('#skF_2', k2_xboole_0('#skF_4', '#skF_3'))), inference(splitRight, [status(thm)], [c_47])).
% 41.99/32.69  tff(c_21475, plain, (r1_xboole_0(k2_xboole_0('#skF_4', '#skF_3'), '#skF_2')), inference(resolution, [status(thm)], [c_21432, c_8])).
% 41.99/32.69  tff(c_21580, plain, (![A_459, C_460, B_461]: (r1_xboole_0(A_459, C_460) | ~r1_xboole_0(B_461, C_460) | ~r1_tarski(A_459, B_461))), inference(cnfTransformation, [status(thm)], [f_71])).
% 41.99/32.69  tff(c_22845, plain, (![A_500]: (r1_xboole_0(A_500, '#skF_2') | ~r1_tarski(A_500, k2_xboole_0('#skF_4', '#skF_3')))), inference(resolution, [status(thm)], [c_21475, c_21580])).
% 41.99/32.69  tff(c_22888, plain, (r1_xboole_0('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_94, c_22845])).
% 41.99/32.69  tff(c_22898, plain, (k3_xboole_0('#skF_3', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_22888, c_4])).
% 41.99/32.69  tff(c_22905, plain, $false, inference(negUnitSimplification, [status(thm)], [c_218, c_22898])).
% 41.99/32.69  tff(c_22907, plain, (r1_xboole_0('#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_40])).
% 41.99/32.69  tff(c_22956, plain, (![A_505, B_506]: (r1_xboole_0(A_505, B_506) | k3_xboole_0(A_505, B_506)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 41.99/32.69  tff(c_23029, plain, (![B_511, A_512]: (r1_xboole_0(B_511, A_512) | k3_xboole_0(A_512, B_511)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_22956, c_8])).
% 41.99/32.69  tff(c_22906, plain, (~r1_xboole_0('#skF_2', '#skF_4') | r1_xboole_0('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_40])).
% 41.99/32.69  tff(c_22917, plain, (~r1_xboole_0('#skF_2', '#skF_4')), inference(splitLeft, [status(thm)], [c_22906])).
% 41.99/32.69  tff(c_23039, plain, (k3_xboole_0('#skF_4', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_23029, c_22917])).
% 41.99/32.69  tff(c_22967, plain, (![B_506, A_505]: (r1_xboole_0(B_506, A_505) | k3_xboole_0(A_505, B_506)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_22956, c_8])).
% 41.99/32.69  tff(c_23293, plain, (~r1_xboole_0('#skF_5', k2_xboole_0('#skF_6', '#skF_7'))), inference(splitLeft, [status(thm)], [c_46])).
% 41.99/32.69  tff(c_23300, plain, (k3_xboole_0(k2_xboole_0('#skF_6', '#skF_7'), '#skF_5')!=k1_xboole_0), inference(resolution, [status(thm)], [c_22967, c_23293])).
% 41.99/32.69  tff(c_23138, plain, (r1_xboole_0('#skF_5', '#skF_6')), inference(splitLeft, [status(thm)], [c_45])).
% 41.99/32.69  tff(c_23144, plain, (k3_xboole_0('#skF_5', '#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_23138, c_4])).
% 41.99/32.69  tff(c_23187, plain, (![A_517, B_518]: (k2_xboole_0(k3_xboole_0(A_517, B_518), k4_xboole_0(A_517, B_518))=A_517)), inference(cnfTransformation, [status(thm)], [f_63])).
% 41.99/32.69  tff(c_23211, plain, (k2_xboole_0(k1_xboole_0, k4_xboole_0('#skF_5', '#skF_6'))='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_23144, c_23187])).
% 41.99/32.69  tff(c_23466, plain, (k4_xboole_0('#skF_5', '#skF_6')='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_23211, c_101])).
% 41.99/32.69  tff(c_23041, plain, (r1_xboole_0('#skF_5', '#skF_7')), inference(splitLeft, [status(thm)], [c_47])).
% 41.99/32.69  tff(c_23047, plain, (k3_xboole_0('#skF_5', '#skF_7')=k1_xboole_0), inference(resolution, [status(thm)], [c_23041, c_4])).
% 41.99/32.69  tff(c_23953, plain, (![A_552, B_553, C_554]: (k2_xboole_0(k4_xboole_0(A_552, B_553), k3_xboole_0(A_552, C_554))=k4_xboole_0(A_552, k4_xboole_0(B_553, C_554)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 41.99/32.69  tff(c_24007, plain, (![B_553]: (k4_xboole_0('#skF_5', k4_xboole_0(B_553, '#skF_7'))=k2_xboole_0(k4_xboole_0('#skF_5', B_553), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_23047, c_23953])).
% 41.99/32.69  tff(c_24046, plain, (![B_553]: (k4_xboole_0('#skF_5', k4_xboole_0(B_553, '#skF_7'))=k4_xboole_0('#skF_5', B_553))), inference(demodulation, [status(thm), theory('equality')], [c_101, c_2, c_24007])).
% 41.99/32.69  tff(c_39495, plain, (![B_754]: (k4_xboole_0('#skF_5', k4_xboole_0(B_754, '#skF_7'))=k4_xboole_0('#skF_5', B_754))), inference(demodulation, [status(thm), theory('equality')], [c_101, c_2, c_24007])).
% 41.99/32.69  tff(c_39688, plain, (![A_17]: (k4_xboole_0('#skF_5', k4_xboole_0(A_17, '#skF_7'))=k4_xboole_0('#skF_5', k2_xboole_0(A_17, '#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_22, c_39495])).
% 41.99/32.69  tff(c_95007, plain, (![A_1298]: (k4_xboole_0('#skF_5', k2_xboole_0(A_1298, '#skF_7'))=k4_xboole_0('#skF_5', A_1298))), inference(demodulation, [status(thm), theory('equality')], [c_24046, c_39688])).
% 41.99/32.69  tff(c_22939, plain, (![A_503, B_504]: (k3_xboole_0(A_503, B_504)=k1_xboole_0 | ~r1_xboole_0(A_503, B_504))), inference(cnfTransformation, [status(thm)], [f_31])).
% 41.99/32.69  tff(c_22947, plain, (k3_xboole_0('#skF_2', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_22907, c_22939])).
% 41.99/32.69  tff(c_23547, plain, (![A_526, B_527, C_528]: (~r1_xboole_0(A_526, B_527) | ~r2_hidden(C_528, k3_xboole_0(A_526, B_527)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 41.99/32.69  tff(c_23571, plain, (![C_528]: (~r1_xboole_0('#skF_2', '#skF_3') | ~r2_hidden(C_528, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_22947, c_23547])).
% 41.99/32.69  tff(c_23586, plain, (![C_528]: (~r2_hidden(C_528, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_22907, c_23571])).
% 41.99/32.69  tff(c_22968, plain, (![A_507, B_508]: (k4_xboole_0(A_507, k4_xboole_0(A_507, B_508))=k3_xboole_0(A_507, B_508))), inference(cnfTransformation, [status(thm)], [f_61])).
% 41.99/32.69  tff(c_22983, plain, (![A_16]: (k4_xboole_0(A_16, A_16)=k3_xboole_0(A_16, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_20, c_22968])).
% 41.99/32.69  tff(c_22986, plain, (![A_16]: (k4_xboole_0(A_16, A_16)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_22983])).
% 41.99/32.69  tff(c_23057, plain, (![A_513, B_514]: (k4_xboole_0(k2_xboole_0(A_513, B_514), B_514)=k4_xboole_0(A_513, B_514))), inference(cnfTransformation, [status(thm)], [f_59])).
% 41.99/32.69  tff(c_23073, plain, (![A_40]: (k4_xboole_0(k1_xboole_0, A_40)=k4_xboole_0(A_40, A_40))), inference(superposition, [status(thm), theory('equality')], [c_101, c_23057])).
% 41.99/32.69  tff(c_23090, plain, (![A_40]: (k4_xboole_0(k1_xboole_0, A_40)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_22986, c_23073])).
% 41.99/32.69  tff(c_24037, plain, (![A_16, C_554]: (k4_xboole_0(A_16, k4_xboole_0(k1_xboole_0, C_554))=k2_xboole_0(A_16, k3_xboole_0(A_16, C_554)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_23953])).
% 41.99/32.69  tff(c_24052, plain, (![A_16, C_554]: (k2_xboole_0(A_16, k3_xboole_0(A_16, C_554))=A_16)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_23090, c_24037])).
% 41.99/32.69  tff(c_24313, plain, (![B_566, A_567]: (k4_xboole_0(k2_xboole_0(B_566, A_567), B_566)=k4_xboole_0(A_567, B_566))), inference(superposition, [status(thm), theory('equality')], [c_2, c_23057])).
% 41.99/32.69  tff(c_24345, plain, (![A_16, C_554]: (k4_xboole_0(k3_xboole_0(A_16, C_554), A_16)=k4_xboole_0(A_16, A_16))), inference(superposition, [status(thm), theory('equality')], [c_24052, c_24313])).
% 41.99/32.69  tff(c_24383, plain, (![A_16, C_554]: (k4_xboole_0(k3_xboole_0(A_16, C_554), A_16)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_22986, c_24345])).
% 41.99/32.69  tff(c_23362, plain, (![A_523, B_524]: (k2_xboole_0(A_523, k4_xboole_0(B_524, A_523))=k2_xboole_0(A_523, B_524))), inference(cnfTransformation, [status(thm)], [f_55])).
% 41.99/32.69  tff(c_23396, plain, (![A_19, B_20]: (k2_xboole_0(k4_xboole_0(A_19, B_20), k3_xboole_0(A_19, B_20))=k2_xboole_0(k4_xboole_0(A_19, B_20), A_19))), inference(superposition, [status(thm), theory('equality')], [c_24, c_23362])).
% 41.99/32.69  tff(c_27281, plain, (![A_626, B_627]: (k2_xboole_0(k4_xboole_0(A_626, B_627), k3_xboole_0(A_626, B_627))=k2_xboole_0(A_626, k4_xboole_0(A_626, B_627)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_23396])).
% 41.99/32.69  tff(c_27299, plain, (![A_626, B_627]: (k4_xboole_0(A_626, k4_xboole_0(B_627, B_627))=k2_xboole_0(A_626, k4_xboole_0(A_626, B_627)))), inference(superposition, [status(thm), theory('equality')], [c_27281, c_28])).
% 41.99/32.69  tff(c_27479, plain, (![A_626, B_627]: (k2_xboole_0(A_626, k4_xboole_0(A_626, B_627))=A_626)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_22986, c_27299])).
% 41.99/32.69  tff(c_22987, plain, (![A_509]: (k4_xboole_0(A_509, A_509)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_22983])).
% 41.99/32.69  tff(c_22992, plain, (![A_509]: (k4_xboole_0(A_509, k1_xboole_0)=k3_xboole_0(A_509, A_509))), inference(superposition, [status(thm), theory('equality')], [c_22987, c_24])).
% 41.99/32.69  tff(c_23004, plain, (![A_509]: (k3_xboole_0(A_509, A_509)=A_509)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_22992])).
% 41.99/32.69  tff(c_28069, plain, (![A_635, C_636, B_637]: (k2_xboole_0(k3_xboole_0(A_635, C_636), k4_xboole_0(A_635, B_637))=k4_xboole_0(A_635, k4_xboole_0(B_637, C_636)))), inference(superposition, [status(thm), theory('equality')], [c_23953, c_2])).
% 41.99/32.69  tff(c_28252, plain, (![A_509, B_637]: (k4_xboole_0(A_509, k4_xboole_0(B_637, A_509))=k2_xboole_0(A_509, k4_xboole_0(A_509, B_637)))), inference(superposition, [status(thm), theory('equality')], [c_23004, c_28069])).
% 41.99/32.69  tff(c_28496, plain, (![A_640, B_641]: (k4_xboole_0(A_640, k4_xboole_0(B_641, A_640))=A_640)), inference(demodulation, [status(thm), theory('equality')], [c_27479, c_28252])).
% 41.99/32.69  tff(c_23193, plain, (![A_517, B_518]: (k4_xboole_0(k3_xboole_0(A_517, B_518), k4_xboole_0(A_517, B_518))=k4_xboole_0(A_517, k4_xboole_0(A_517, B_518)))), inference(superposition, [status(thm), theory('equality')], [c_23187, c_22])).
% 41.99/32.69  tff(c_23246, plain, (![A_517, B_518]: (k4_xboole_0(k3_xboole_0(A_517, B_518), k4_xboole_0(A_517, B_518))=k3_xboole_0(A_517, B_518))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_23193])).
% 41.99/32.69  tff(c_28564, plain, (![A_640, B_641]: (k4_xboole_0(k3_xboole_0(A_640, k4_xboole_0(B_641, A_640)), A_640)=k3_xboole_0(A_640, k4_xboole_0(B_641, A_640)))), inference(superposition, [status(thm), theory('equality')], [c_28496, c_23246])).
% 41.99/32.69  tff(c_28787, plain, (![A_642, B_643]: (k3_xboole_0(A_642, k4_xboole_0(B_643, A_642))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_24383, c_28564])).
% 41.99/32.69  tff(c_28877, plain, (![A_642, B_643]: (r2_hidden('#skF_1'(A_642, k4_xboole_0(B_643, A_642)), k1_xboole_0) | r1_xboole_0(A_642, k4_xboole_0(B_643, A_642)))), inference(superposition, [status(thm), theory('equality')], [c_28787, c_10])).
% 41.99/32.69  tff(c_29005, plain, (![A_642, B_643]: (r1_xboole_0(A_642, k4_xboole_0(B_643, A_642)))), inference(negUnitSimplification, [status(thm)], [c_23586, c_28877])).
% 41.99/32.69  tff(c_95489, plain, (![A_1299]: (r1_xboole_0(k2_xboole_0(A_1299, '#skF_7'), k4_xboole_0('#skF_5', A_1299)))), inference(superposition, [status(thm), theory('equality')], [c_95007, c_29005])).
% 41.99/32.69  tff(c_95583, plain, (r1_xboole_0(k2_xboole_0('#skF_6', '#skF_7'), '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_23466, c_95489])).
% 41.99/32.69  tff(c_95635, plain, (k3_xboole_0(k2_xboole_0('#skF_6', '#skF_7'), '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_95583, c_4])).
% 41.99/32.69  tff(c_95648, plain, $false, inference(negUnitSimplification, [status(thm)], [c_23300, c_95635])).
% 41.99/32.69  tff(c_95649, plain, (r1_xboole_0('#skF_2', k2_xboole_0('#skF_4', '#skF_3'))), inference(splitRight, [status(thm)], [c_46])).
% 41.99/32.69  tff(c_95657, plain, (r1_xboole_0(k2_xboole_0('#skF_4', '#skF_3'), '#skF_2')), inference(resolution, [status(thm)], [c_95649, c_8])).
% 41.99/32.69  tff(c_96075, plain, (![A_1309, C_1310, B_1311]: (r1_xboole_0(A_1309, C_1310) | ~r1_xboole_0(B_1311, C_1310) | ~r1_tarski(A_1309, B_1311))), inference(cnfTransformation, [status(thm)], [f_71])).
% 41.99/32.69  tff(c_101821, plain, (![A_1433]: (r1_xboole_0(A_1433, '#skF_2') | ~r1_tarski(A_1433, k2_xboole_0('#skF_4', '#skF_3')))), inference(resolution, [status(thm)], [c_95657, c_96075])).
% 41.99/32.69  tff(c_101854, plain, (r1_xboole_0('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_32, c_101821])).
% 41.99/32.69  tff(c_101859, plain, (k3_xboole_0('#skF_4', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_101854, c_4])).
% 41.99/32.69  tff(c_101866, plain, $false, inference(negUnitSimplification, [status(thm)], [c_23039, c_101859])).
% 41.99/32.69  tff(c_101867, plain, (r1_xboole_0('#skF_2', k2_xboole_0('#skF_4', '#skF_3'))), inference(splitRight, [status(thm)], [c_45])).
% 41.99/32.69  tff(c_101908, plain, (r1_xboole_0(k2_xboole_0('#skF_4', '#skF_3'), '#skF_2')), inference(resolution, [status(thm)], [c_101867, c_8])).
% 41.99/32.69  tff(c_102340, plain, (![A_1448, C_1449, B_1450]: (r1_xboole_0(A_1448, C_1449) | ~r1_xboole_0(B_1450, C_1449) | ~r1_tarski(A_1448, B_1450))), inference(cnfTransformation, [status(thm)], [f_71])).
% 41.99/32.69  tff(c_104999, plain, (![A_1529]: (r1_xboole_0(A_1529, '#skF_2') | ~r1_tarski(A_1529, k2_xboole_0('#skF_4', '#skF_3')))), inference(resolution, [status(thm)], [c_101908, c_102340])).
% 41.99/32.69  tff(c_105032, plain, (r1_xboole_0('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_32, c_104999])).
% 41.99/32.69  tff(c_105037, plain, (k3_xboole_0('#skF_4', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_105032, c_4])).
% 41.99/32.69  tff(c_105044, plain, $false, inference(negUnitSimplification, [status(thm)], [c_23039, c_105037])).
% 41.99/32.69  tff(c_105045, plain, (r1_xboole_0('#skF_2', k2_xboole_0('#skF_4', '#skF_3'))), inference(splitRight, [status(thm)], [c_47])).
% 41.99/32.69  tff(c_105061, plain, (r1_xboole_0(k2_xboole_0('#skF_4', '#skF_3'), '#skF_2')), inference(resolution, [status(thm)], [c_105045, c_8])).
% 41.99/32.69  tff(c_105514, plain, (![A_1551, C_1552, B_1553]: (r1_xboole_0(A_1551, C_1552) | ~r1_xboole_0(B_1553, C_1552) | ~r1_tarski(A_1551, B_1553))), inference(cnfTransformation, [status(thm)], [f_71])).
% 41.99/32.69  tff(c_109015, plain, (![A_1643]: (r1_xboole_0(A_1643, '#skF_2') | ~r1_tarski(A_1643, k2_xboole_0('#skF_4', '#skF_3')))), inference(resolution, [status(thm)], [c_105061, c_105514])).
% 41.99/32.69  tff(c_109065, plain, (r1_xboole_0('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_32, c_109015])).
% 41.99/32.69  tff(c_109070, plain, (k3_xboole_0('#skF_4', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_109065, c_4])).
% 41.99/32.69  tff(c_109077, plain, $false, inference(negUnitSimplification, [status(thm)], [c_23039, c_109070])).
% 41.99/32.69  tff(c_109079, plain, (r1_xboole_0('#skF_2', '#skF_4')), inference(splitRight, [status(thm)], [c_22906])).
% 41.99/32.69  tff(c_44, plain, (~r1_xboole_0('#skF_2', '#skF_4') | ~r1_xboole_0('#skF_2', '#skF_3') | ~r1_xboole_0('#skF_5', k2_xboole_0('#skF_6', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_90])).
% 41.99/32.69  tff(c_109195, plain, (~r1_xboole_0('#skF_5', k2_xboole_0('#skF_6', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_22907, c_109079, c_44])).
% 41.99/32.69  tff(c_109210, plain, (k3_xboole_0(k2_xboole_0('#skF_6', '#skF_7'), '#skF_5')!=k1_xboole_0), inference(resolution, [status(thm)], [c_109201, c_109195])).
% 41.99/32.69  tff(c_109078, plain, (r1_xboole_0('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_22906])).
% 41.99/32.69  tff(c_109094, plain, (![A_1644, B_1645]: (k3_xboole_0(A_1644, B_1645)=k1_xboole_0 | ~r1_xboole_0(A_1644, B_1645))), inference(cnfTransformation, [status(thm)], [f_31])).
% 41.99/32.69  tff(c_109116, plain, (k3_xboole_0('#skF_5', '#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_109078, c_109094])).
% 41.99/32.69  tff(c_109643, plain, (![A_1673, B_1674]: (k2_xboole_0(k3_xboole_0(A_1673, B_1674), k4_xboole_0(A_1673, B_1674))=A_1673)), inference(cnfTransformation, [status(thm)], [f_63])).
% 41.99/32.69  tff(c_109703, plain, (k2_xboole_0(k1_xboole_0, k4_xboole_0('#skF_5', '#skF_6'))='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_109116, c_109643])).
% 41.99/32.69  tff(c_110411, plain, (k4_xboole_0('#skF_5', '#skF_6')='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_109703, c_101])).
% 41.99/32.69  tff(c_109213, plain, (![A_1652, B_1653]: (k4_xboole_0(A_1652, k4_xboole_0(A_1652, B_1653))=k3_xboole_0(A_1652, B_1653))), inference(cnfTransformation, [status(thm)], [f_61])).
% 41.99/32.69  tff(c_109228, plain, (![A_16]: (k4_xboole_0(A_16, A_16)=k3_xboole_0(A_16, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_20, c_109213])).
% 41.99/32.69  tff(c_109231, plain, (![A_16]: (k4_xboole_0(A_16, A_16)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_109228])).
% 41.99/32.69  tff(c_109457, plain, (![A_1665, B_1666]: (k4_xboole_0(k2_xboole_0(A_1665, B_1666), B_1666)=k4_xboole_0(A_1665, B_1666))), inference(cnfTransformation, [status(thm)], [f_59])).
% 41.99/32.69  tff(c_109488, plain, (![A_40]: (k4_xboole_0(k1_xboole_0, A_40)=k4_xboole_0(A_40, A_40))), inference(superposition, [status(thm), theory('equality')], [c_101, c_109457])).
% 41.99/32.69  tff(c_109508, plain, (![A_40]: (k4_xboole_0(k1_xboole_0, A_40)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_109231, c_109488])).
% 41.99/32.69  tff(c_110103, plain, (![A_1696, B_1697, C_1698]: (k2_xboole_0(k4_xboole_0(A_1696, B_1697), k3_xboole_0(A_1696, C_1698))=k4_xboole_0(A_1696, k4_xboole_0(B_1697, C_1698)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 41.99/32.69  tff(c_110187, plain, (![A_16, C_1698]: (k4_xboole_0(A_16, k4_xboole_0(k1_xboole_0, C_1698))=k2_xboole_0(A_16, k3_xboole_0(A_16, C_1698)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_110103])).
% 41.99/32.69  tff(c_110203, plain, (![A_16, C_1698]: (k2_xboole_0(A_16, k3_xboole_0(A_16, C_1698))=A_16)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_109508, c_110187])).
% 41.99/32.69  tff(c_110726, plain, (![A_1711, B_1712]: (k4_xboole_0(k2_xboole_0(A_1711, B_1712), A_1711)=k4_xboole_0(B_1712, A_1711))), inference(superposition, [status(thm), theory('equality')], [c_2, c_109457])).
% 41.99/32.69  tff(c_110770, plain, (![A_16, C_1698]: (k4_xboole_0(k3_xboole_0(A_16, C_1698), A_16)=k4_xboole_0(A_16, A_16))), inference(superposition, [status(thm), theory('equality')], [c_110203, c_110726])).
% 41.99/32.69  tff(c_110812, plain, (![A_16, C_1698]: (k4_xboole_0(k3_xboole_0(A_16, C_1698), A_16)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_109231, c_110770])).
% 41.99/32.69  tff(c_109494, plain, (![A_1, B_2]: (k4_xboole_0(k2_xboole_0(A_1, B_2), A_1)=k4_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_109457])).
% 41.99/32.69  tff(c_18, plain, (![A_14, B_15]: (k2_xboole_0(A_14, k4_xboole_0(B_15, A_14))=k2_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_55])).
% 41.99/32.69  tff(c_110786, plain, (![B_15, A_14]: (k4_xboole_0(k4_xboole_0(B_15, A_14), A_14)=k4_xboole_0(k2_xboole_0(A_14, B_15), A_14))), inference(superposition, [status(thm), theory('equality')], [c_18, c_110726])).
% 41.99/32.69  tff(c_124829, plain, (![B_1885, A_1886]: (k4_xboole_0(k4_xboole_0(B_1885, A_1886), A_1886)=k4_xboole_0(B_1885, A_1886))), inference(demodulation, [status(thm), theory('equality')], [c_109494, c_110786])).
% 41.99/32.69  tff(c_109649, plain, (![A_1673, B_1674]: (k4_xboole_0(k3_xboole_0(A_1673, B_1674), k4_xboole_0(A_1673, B_1674))=k4_xboole_0(A_1673, k4_xboole_0(A_1673, B_1674)))), inference(superposition, [status(thm), theory('equality')], [c_109643, c_22])).
% 41.99/32.69  tff(c_109714, plain, (![A_1673, B_1674]: (k4_xboole_0(k3_xboole_0(A_1673, B_1674), k4_xboole_0(A_1673, B_1674))=k3_xboole_0(A_1673, B_1674))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_109649])).
% 41.99/32.69  tff(c_124898, plain, (![B_1885, A_1886]: (k4_xboole_0(k3_xboole_0(k4_xboole_0(B_1885, A_1886), A_1886), k4_xboole_0(B_1885, A_1886))=k3_xboole_0(k4_xboole_0(B_1885, A_1886), A_1886))), inference(superposition, [status(thm), theory('equality')], [c_124829, c_109714])).
% 41.99/32.69  tff(c_125161, plain, (![B_1887, A_1888]: (k3_xboole_0(k4_xboole_0(B_1887, A_1888), A_1888)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_110812, c_124898])).
% 41.99/32.69  tff(c_109211, plain, (![B_1650, A_1651]: (k3_xboole_0(B_1650, A_1651)=k1_xboole_0 | k3_xboole_0(A_1651, B_1650)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_109201, c_4])).
% 41.99/32.69  tff(c_125405, plain, (![A_1888, B_1887]: (k3_xboole_0(A_1888, k4_xboole_0(B_1887, A_1888))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_125161, c_109211])).
% 41.99/32.69  tff(c_109485, plain, (![A_14, B_15]: (k4_xboole_0(k2_xboole_0(A_14, B_15), k4_xboole_0(B_15, A_14))=k4_xboole_0(A_14, k4_xboole_0(B_15, A_14)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_109457])).
% 41.99/32.69  tff(c_109469, plain, (![B_1666, A_1665]: (k2_xboole_0(B_1666, k4_xboole_0(A_1665, B_1666))=k2_xboole_0(B_1666, k2_xboole_0(A_1665, B_1666)))), inference(superposition, [status(thm), theory('equality')], [c_109457, c_18])).
% 41.99/32.69  tff(c_109504, plain, (![B_1666, A_1665]: (k2_xboole_0(B_1666, k2_xboole_0(A_1665, B_1666))=k2_xboole_0(B_1666, A_1665))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_109469])).
% 41.99/32.69  tff(c_115496, plain, (![A_1801, B_1802]: (k4_xboole_0(k2_xboole_0(A_1801, B_1802), k4_xboole_0(A_1801, B_1802))=k3_xboole_0(k2_xboole_0(A_1801, B_1802), B_1802))), inference(superposition, [status(thm), theory('equality')], [c_109457, c_24])).
% 41.99/32.69  tff(c_115657, plain, (![A_17, B_18]: (k4_xboole_0(k2_xboole_0(k2_xboole_0(A_17, B_18), B_18), k4_xboole_0(A_17, B_18))=k3_xboole_0(k2_xboole_0(k2_xboole_0(A_17, B_18), B_18), B_18))), inference(superposition, [status(thm), theory('equality')], [c_22, c_115496])).
% 41.99/32.69  tff(c_146504, plain, (![B_2174, A_2175]: (k4_xboole_0(B_2174, k4_xboole_0(A_2175, B_2174))=k3_xboole_0(k2_xboole_0(B_2174, A_2175), B_2174))), inference(demodulation, [status(thm), theory('equality')], [c_109485, c_109504, c_109504, c_2, c_2, c_115657])).
% 41.99/32.69  tff(c_109232, plain, (![A_1654, B_1655]: (k2_xboole_0(A_1654, k4_xboole_0(B_1655, A_1654))=k2_xboole_0(A_1654, B_1655))), inference(cnfTransformation, [status(thm)], [f_55])).
% 41.99/32.69  tff(c_109251, plain, (![A_19, B_20]: (k2_xboole_0(k4_xboole_0(A_19, B_20), k3_xboole_0(A_19, B_20))=k2_xboole_0(k4_xboole_0(A_19, B_20), A_19))), inference(superposition, [status(thm), theory('equality')], [c_24, c_109232])).
% 41.99/32.69  tff(c_113883, plain, (![A_1778, B_1779]: (k2_xboole_0(k4_xboole_0(A_1778, B_1779), k3_xboole_0(A_1778, B_1779))=k2_xboole_0(A_1778, k4_xboole_0(A_1778, B_1779)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_109251])).
% 41.99/32.69  tff(c_113898, plain, (![A_1778, B_1779]: (k4_xboole_0(A_1778, k4_xboole_0(B_1779, B_1779))=k2_xboole_0(A_1778, k4_xboole_0(A_1778, B_1779)))), inference(superposition, [status(thm), theory('equality')], [c_113883, c_28])).
% 41.99/32.69  tff(c_114060, plain, (![A_1778, B_1779]: (k2_xboole_0(A_1778, k4_xboole_0(A_1778, B_1779))=A_1778)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_109231, c_113898])).
% 41.99/32.69  tff(c_109263, plain, (![A_19, B_20]: (k2_xboole_0(k4_xboole_0(A_19, B_20), k3_xboole_0(A_19, B_20))=k2_xboole_0(A_19, k4_xboole_0(A_19, B_20)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_109251])).
% 41.99/32.69  tff(c_114110, plain, (![A_19, B_20]: (k2_xboole_0(k4_xboole_0(A_19, B_20), k3_xboole_0(A_19, B_20))=A_19)), inference(demodulation, [status(thm), theory('equality')], [c_114060, c_109263])).
% 41.99/32.69  tff(c_146828, plain, (![B_2174, A_2175]: (k2_xboole_0(k3_xboole_0(k2_xboole_0(B_2174, A_2175), B_2174), k3_xboole_0(B_2174, k4_xboole_0(A_2175, B_2174)))=B_2174)), inference(superposition, [status(thm), theory('equality')], [c_146504, c_114110])).
% 41.99/32.69  tff(c_147419, plain, (![B_2176, A_2177]: (k3_xboole_0(k2_xboole_0(B_2176, A_2177), B_2176)=B_2176)), inference(demodulation, [status(thm), theory('equality')], [c_101, c_2, c_125405, c_146828])).
% 41.99/32.69  tff(c_6, plain, (![A_3, B_4]: (r1_xboole_0(A_3, B_4) | k3_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 41.99/32.69  tff(c_109788, plain, (![A_1679, C_1680, B_1681]: (r1_xboole_0(A_1679, C_1680) | ~r1_xboole_0(B_1681, C_1680) | ~r1_tarski(A_1679, B_1681))), inference(cnfTransformation, [status(thm)], [f_71])).
% 41.99/32.69  tff(c_112621, plain, (![A_1756, B_1757, A_1758]: (r1_xboole_0(A_1756, B_1757) | ~r1_tarski(A_1756, A_1758) | k3_xboole_0(A_1758, B_1757)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_109788])).
% 41.99/32.69  tff(c_112645, plain, (![A_40, B_1757, B_39]: (r1_xboole_0(A_40, B_1757) | k3_xboole_0(k2_xboole_0(B_39, A_40), B_1757)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_94, c_112621])).
% 41.99/32.69  tff(c_147762, plain, (![A_2179, B_2180]: (r1_xboole_0(A_2179, B_2180) | k1_xboole_0!=B_2180)), inference(superposition, [status(thm), theory('equality')], [c_147419, c_112645])).
% 41.99/32.69  tff(c_149135, plain, (![A_2187, B_2188]: (k3_xboole_0(A_2187, B_2188)=k1_xboole_0 | k1_xboole_0!=B_2188)), inference(resolution, [status(thm)], [c_147762, c_4])).
% 41.99/32.69  tff(c_149765, plain, (![A_2187, B_2188]: (k2_xboole_0(k1_xboole_0, k4_xboole_0(A_2187, B_2188))=A_2187 | k1_xboole_0!=B_2188)), inference(superposition, [status(thm), theory('equality')], [c_149135, c_26])).
% 41.99/32.69  tff(c_151418, plain, (![A_2187]: (k4_xboole_0(A_2187, k1_xboole_0)=A_2187)), inference(demodulation, [status(thm), theory('equality')], [c_101, c_149765])).
% 41.99/32.69  tff(c_36, plain, (~r1_xboole_0('#skF_2', '#skF_4') | ~r1_xboole_0('#skF_2', '#skF_3') | r1_xboole_0('#skF_5', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_90])).
% 41.99/32.69  tff(c_109129, plain, (r1_xboole_0('#skF_5', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_22907, c_109079, c_36])).
% 41.99/32.69  tff(c_109135, plain, (k3_xboole_0('#skF_5', '#skF_7')=k1_xboole_0), inference(resolution, [status(thm)], [c_109129, c_4])).
% 41.99/32.69  tff(c_110109, plain, (![A_1696, B_1697, C_1698]: (k4_xboole_0(k4_xboole_0(A_1696, k4_xboole_0(B_1697, C_1698)), k3_xboole_0(A_1696, C_1698))=k4_xboole_0(k4_xboole_0(A_1696, B_1697), k3_xboole_0(A_1696, C_1698)))), inference(superposition, [status(thm), theory('equality')], [c_110103, c_22])).
% 41.99/32.69  tff(c_118795, plain, (![A_1837, B_1838, C_1839]: (k4_xboole_0(k4_xboole_0(A_1837, k4_xboole_0(B_1838, C_1839)), k3_xboole_0(A_1837, C_1839))=k4_xboole_0(k4_xboole_0(A_1837, B_1838), k3_xboole_0(A_1837, C_1839)))), inference(superposition, [status(thm), theory('equality')], [c_110103, c_22])).
% 41.99/32.69  tff(c_119073, plain, (![A_1837, B_2, A_1]: (k4_xboole_0(k4_xboole_0(A_1837, k4_xboole_0(B_2, A_1)), k3_xboole_0(A_1837, A_1))=k4_xboole_0(k4_xboole_0(A_1837, k2_xboole_0(A_1, B_2)), k3_xboole_0(A_1837, A_1)))), inference(superposition, [status(thm), theory('equality')], [c_109494, c_118795])).
% 41.99/32.69  tff(c_203598, plain, (![A_2591, A_2592, B_2593]: (k4_xboole_0(k4_xboole_0(A_2591, k2_xboole_0(A_2592, B_2593)), k3_xboole_0(A_2591, A_2592))=k4_xboole_0(k4_xboole_0(A_2591, B_2593), k3_xboole_0(A_2591, A_2592)))), inference(demodulation, [status(thm), theory('equality')], [c_110109, c_119073])).
% 41.99/32.69  tff(c_204319, plain, (![B_2593]: (k4_xboole_0(k4_xboole_0('#skF_5', k2_xboole_0('#skF_7', B_2593)), k1_xboole_0)=k4_xboole_0(k4_xboole_0('#skF_5', B_2593), k3_xboole_0('#skF_5', '#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_109135, c_203598])).
% 41.99/32.69  tff(c_204488, plain, (![B_2594]: (k4_xboole_0('#skF_5', k2_xboole_0('#skF_7', B_2594))=k4_xboole_0('#skF_5', B_2594))), inference(demodulation, [status(thm), theory('equality')], [c_151418, c_151418, c_109135, c_204319])).
% 41.99/32.69  tff(c_109592, plain, (![A_1669, B_1670, C_1671]: (~r1_xboole_0(A_1669, B_1670) | ~r2_hidden(C_1671, k3_xboole_0(A_1669, B_1670)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 41.99/32.69  tff(c_109613, plain, (![C_1671]: (~r1_xboole_0('#skF_5', '#skF_7') | ~r2_hidden(C_1671, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_109135, c_109592])).
% 41.99/32.69  tff(c_109635, plain, (![C_1671]: (~r2_hidden(C_1671, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_109129, c_109613])).
% 41.99/32.69  tff(c_125225, plain, (![B_1887, A_1888]: (r2_hidden('#skF_1'(k4_xboole_0(B_1887, A_1888), A_1888), k1_xboole_0) | r1_xboole_0(k4_xboole_0(B_1887, A_1888), A_1888))), inference(superposition, [status(thm), theory('equality')], [c_125161, c_10])).
% 41.99/32.69  tff(c_125473, plain, (![B_1889, A_1890]: (r1_xboole_0(k4_xboole_0(B_1889, A_1890), A_1890))), inference(negUnitSimplification, [status(thm)], [c_109635, c_125225])).
% 41.99/32.69  tff(c_125619, plain, (![A_1890, B_1889]: (r1_xboole_0(A_1890, k4_xboole_0(B_1889, A_1890)))), inference(resolution, [status(thm)], [c_125473, c_8])).
% 41.99/32.69  tff(c_205070, plain, (![B_2595]: (r1_xboole_0(k2_xboole_0('#skF_7', B_2595), k4_xboole_0('#skF_5', B_2595)))), inference(superposition, [status(thm), theory('equality')], [c_204488, c_125619])).
% 41.99/32.69  tff(c_205165, plain, (r1_xboole_0(k2_xboole_0('#skF_7', '#skF_6'), '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_110411, c_205070])).
% 41.99/32.69  tff(c_205211, plain, (r1_xboole_0(k2_xboole_0('#skF_6', '#skF_7'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_205165])).
% 41.99/32.69  tff(c_205221, plain, (k3_xboole_0(k2_xboole_0('#skF_6', '#skF_7'), '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_205211, c_4])).
% 41.99/32.69  tff(c_205234, plain, $false, inference(negUnitSimplification, [status(thm)], [c_109210, c_205221])).
% 41.99/32.69  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 41.99/32.69  
% 41.99/32.69  Inference rules
% 41.99/32.69  ----------------------
% 41.99/32.69  #Ref     : 2
% 41.99/32.69  #Sup     : 52669
% 41.99/32.69  #Fact    : 0
% 41.99/32.69  #Define  : 0
% 41.99/32.69  #Split   : 89
% 41.99/32.69  #Chain   : 0
% 41.99/32.69  #Close   : 0
% 41.99/32.69  
% 41.99/32.69  Ordering : KBO
% 41.99/32.69  
% 41.99/32.69  Simplification rules
% 41.99/32.69  ----------------------
% 41.99/32.69  #Subsume      : 8753
% 41.99/32.69  #Demod        : 54142
% 41.99/32.69  #Tautology    : 28846
% 41.99/32.69  #SimpNegUnit  : 576
% 41.99/32.69  #BackRed      : 70
% 41.99/32.69  
% 41.99/32.69  #Partial instantiations: 0
% 41.99/32.69  #Strategies tried      : 1
% 41.99/32.69  
% 41.99/32.69  Timing (in seconds)
% 41.99/32.69  ----------------------
% 41.99/32.70  Preprocessing        : 0.30
% 41.99/32.70  Parsing              : 0.17
% 41.99/32.70  CNF conversion       : 0.02
% 41.99/32.70  Main loop            : 31.57
% 41.99/32.70  Inferencing          : 3.30
% 41.99/32.70  Reduction            : 19.90
% 41.99/32.70  Demodulation         : 17.45
% 41.99/32.70  BG Simplification    : 0.33
% 41.99/32.70  Subsumption          : 6.53
% 41.99/32.70  Abstraction          : 0.57
% 41.99/32.70  MUC search           : 0.00
% 41.99/32.70  Cooper               : 0.00
% 41.99/32.70  Total                : 31.97
% 41.99/32.70  Index Insertion      : 0.00
% 41.99/32.70  Index Deletion       : 0.00
% 41.99/32.70  Index Matching       : 0.00
% 41.99/32.70  BG Taut test         : 0.00
%------------------------------------------------------------------------------
