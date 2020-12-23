%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:54 EST 2020

% Result     : Theorem 8.09s
% Output     : CNFRefutation 8.09s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 256 expanded)
%              Number of leaves         :   29 (  96 expanded)
%              Depth                    :   25
%              Number of atoms          :  134 ( 380 expanded)
%              Number of equality atoms :   75 ( 169 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    5 (   2 average)

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

tff(f_94,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r1_tarski(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,C) )
       => r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_xboole_1)).

tff(f_71,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_73,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_53,axiom,(
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

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_67,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_79,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_77,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_69,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_75,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

tff(f_87,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(c_36,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_22,plain,(
    ! [A_19] : k4_xboole_0(A_19,k1_xboole_0) = A_19 ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_192,plain,(
    ! [A_55,B_56] : k4_xboole_0(k2_xboole_0(A_55,B_56),B_56) = k4_xboole_0(A_55,B_56) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_208,plain,(
    ! [A_55] : k4_xboole_0(A_55,k1_xboole_0) = k2_xboole_0(A_55,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_192,c_22])).

tff(c_228,plain,(
    ! [A_55] : k2_xboole_0(A_55,k1_xboole_0) = A_55 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_208])).

tff(c_14,plain,(
    ! [A_7,B_8] :
      ( r2_hidden('#skF_1'(A_7,B_8),A_7)
      | r1_xboole_0(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_38,plain,(
    r1_xboole_0('#skF_3','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_112,plain,(
    ! [A_45,B_46] :
      ( k3_xboole_0(A_45,B_46) = k1_xboole_0
      | ~ r1_xboole_0(A_45,B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_124,plain,(
    k3_xboole_0('#skF_3','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_38,c_112])).

tff(c_424,plain,(
    ! [A_67,B_68,C_69] :
      ( ~ r1_xboole_0(A_67,B_68)
      | ~ r2_hidden(C_69,k3_xboole_0(A_67,B_68)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_437,plain,(
    ! [C_69] :
      ( ~ r1_xboole_0('#skF_3','#skF_5')
      | ~ r2_hidden(C_69,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_124,c_424])).

tff(c_443,plain,(
    ! [C_70] : ~ r2_hidden(C_70,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_437])).

tff(c_449,plain,(
    ! [B_71] : r1_xboole_0(k1_xboole_0,B_71) ),
    inference(resolution,[status(thm)],[c_14,c_443])).

tff(c_8,plain,(
    ! [B_6,A_5] :
      ( r1_xboole_0(B_6,A_5)
      | ~ r1_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_457,plain,(
    ! [B_72] : r1_xboole_0(B_72,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_449,c_8])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( k3_xboole_0(A_3,B_4) = k1_xboole_0
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_463,plain,(
    ! [B_72] : k3_xboole_0(B_72,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_457,c_4])).

tff(c_275,plain,(
    ! [A_60,B_61] : k4_xboole_0(A_60,k4_xboole_0(A_60,B_61)) = k3_xboole_0(A_60,B_61) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_302,plain,(
    ! [A_19] : k4_xboole_0(A_19,A_19) = k3_xboole_0(A_19,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_275])).

tff(c_480,plain,(
    ! [A_19] : k4_xboole_0(A_19,A_19) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_463,c_302])).

tff(c_30,plain,(
    ! [A_27,B_28] : k4_xboole_0(A_27,k4_xboole_0(A_27,B_28)) = k3_xboole_0(A_27,B_28) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_501,plain,(
    ! [A_75] : k4_xboole_0(A_75,A_75) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_463,c_302])).

tff(c_510,plain,(
    ! [A_75] : k4_xboole_0(A_75,k1_xboole_0) = k3_xboole_0(A_75,A_75) ),
    inference(superposition,[status(thm),theory(equality)],[c_501,c_30])).

tff(c_532,plain,(
    ! [A_75] : k3_xboole_0(A_75,A_75) = A_75 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_510])).

tff(c_107,plain,(
    ! [A_43,B_44] :
      ( r1_xboole_0(A_43,B_44)
      | k3_xboole_0(A_43,B_44) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_110,plain,(
    ! [B_44,A_43] :
      ( r1_xboole_0(B_44,A_43)
      | k3_xboole_0(A_43,B_44) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_107,c_8])).

tff(c_539,plain,(
    ! [A_76] : k3_xboole_0(A_76,A_76) = A_76 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_510])).

tff(c_18,plain,(
    ! [A_12,B_13,C_16] :
      ( ~ r1_xboole_0(A_12,B_13)
      | ~ r2_hidden(C_16,k3_xboole_0(A_12,B_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_888,plain,(
    ! [A_95,C_96] :
      ( ~ r1_xboole_0(A_95,A_95)
      | ~ r2_hidden(C_96,A_95) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_539,c_18])).

tff(c_915,plain,(
    ! [C_96,A_43] :
      ( ~ r2_hidden(C_96,A_43)
      | k3_xboole_0(A_43,A_43) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_110,c_888])).

tff(c_932,plain,(
    ! [C_97,A_98] :
      ( ~ r2_hidden(C_97,A_98)
      | k1_xboole_0 != A_98 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_532,c_915])).

tff(c_980,plain,(
    ! [A_102,B_103] :
      ( k1_xboole_0 != A_102
      | r1_xboole_0(A_102,B_103) ) ),
    inference(resolution,[status(thm)],[c_14,c_932])).

tff(c_1514,plain,(
    ! [A_126,B_127] :
      ( k3_xboole_0(A_126,B_127) = k1_xboole_0
      | k1_xboole_0 != A_126 ) ),
    inference(resolution,[status(thm)],[c_980,c_4])).

tff(c_28,plain,(
    ! [A_25,B_26] : k4_xboole_0(A_25,k3_xboole_0(A_25,B_26)) = k4_xboole_0(A_25,B_26) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_1534,plain,(
    ! [A_126,B_127] :
      ( k4_xboole_0(A_126,k1_xboole_0) = k4_xboole_0(A_126,B_127)
      | k1_xboole_0 != A_126 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1514,c_28])).

tff(c_1672,plain,(
    ! [A_132,B_133] :
      ( k4_xboole_0(A_132,B_133) = A_132
      | k1_xboole_0 != A_132 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_1534])).

tff(c_1934,plain,(
    ! [A_140,B_141] :
      ( k3_xboole_0(A_140,B_141) = A_140
      | k1_xboole_0 != A_140 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_1672])).

tff(c_1957,plain,(
    ! [A_140,B_141] :
      ( k4_xboole_0(A_140,B_141) = k4_xboole_0(A_140,A_140)
      | k1_xboole_0 != A_140 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1934,c_28])).

tff(c_2006,plain,(
    ! [A_142,B_143] :
      ( k4_xboole_0(A_142,B_143) = k1_xboole_0
      | k1_xboole_0 != A_142 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_480,c_1957])).

tff(c_20,plain,(
    ! [A_17,B_18] : k2_xboole_0(A_17,k4_xboole_0(B_18,A_17)) = k2_xboole_0(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_2066,plain,(
    ! [B_143,A_142] :
      ( k2_xboole_0(B_143,k1_xboole_0) = k2_xboole_0(B_143,A_142)
      | k1_xboole_0 != A_142 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2006,c_20])).

tff(c_2128,plain,(
    ! [B_143] : k2_xboole_0(B_143,k1_xboole_0) = B_143 ),
    inference(demodulation,[status(thm),theory(equality)],[c_228,c_2066])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_635,plain,(
    ! [A_80,B_81] : k4_xboole_0(A_80,k3_xboole_0(A_80,B_81)) = k4_xboole_0(A_80,B_81) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_672,plain,(
    k4_xboole_0('#skF_3',k1_xboole_0) = k4_xboole_0('#skF_3','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_124,c_635])).

tff(c_683,plain,(
    k4_xboole_0('#skF_3','#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_672])).

tff(c_1030,plain,(
    ! [A_107,B_108,C_109] : k4_xboole_0(k4_xboole_0(A_107,B_108),C_109) = k4_xboole_0(A_107,k2_xboole_0(B_108,C_109)) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_4158,plain,(
    ! [C_210] : k4_xboole_0('#skF_3',k2_xboole_0('#skF_5',C_210)) = k4_xboole_0('#skF_3',C_210) ),
    inference(superposition,[status(thm),theory(equality)],[c_683,c_1030])).

tff(c_4255,plain,(
    ! [A_1] : k4_xboole_0('#skF_3',k2_xboole_0(A_1,'#skF_5')) = k4_xboole_0('#skF_3',A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_4158])).

tff(c_1044,plain,(
    ! [A_107,B_108] : k4_xboole_0(A_107,k2_xboole_0(B_108,k4_xboole_0(A_107,B_108))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1030,c_480])).

tff(c_1114,plain,(
    ! [A_107,B_108] : k4_xboole_0(A_107,k2_xboole_0(B_108,A_107)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_1044])).

tff(c_1060,plain,(
    ! [C_109,A_107,B_108] : k2_xboole_0(C_109,k4_xboole_0(A_107,k2_xboole_0(B_108,C_109))) = k2_xboole_0(C_109,k4_xboole_0(A_107,B_108)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1030,c_20])).

tff(c_26,plain,(
    ! [A_22,B_23,C_24] : k4_xboole_0(k4_xboole_0(A_22,B_23),C_24) = k4_xboole_0(A_22,k2_xboole_0(B_23,C_24)) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_1051,plain,(
    ! [A_107,B_108,B_28] : k4_xboole_0(A_107,k2_xboole_0(B_108,k4_xboole_0(k4_xboole_0(A_107,B_108),B_28))) = k3_xboole_0(k4_xboole_0(A_107,B_108),B_28) ),
    inference(superposition,[status(thm),theory(equality)],[c_1030,c_30])).

tff(c_12618,plain,(
    ! [A_304,B_305,B_306] : k4_xboole_0(A_304,k2_xboole_0(B_305,k4_xboole_0(A_304,k2_xboole_0(B_305,B_306)))) = k3_xboole_0(k4_xboole_0(A_304,B_305),B_306) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_1051])).

tff(c_12825,plain,(
    ! [A_107,B_108] : k4_xboole_0(A_107,k2_xboole_0(B_108,k4_xboole_0(A_107,B_108))) = k3_xboole_0(k4_xboole_0(A_107,B_108),B_108) ),
    inference(superposition,[status(thm),theory(equality)],[c_1060,c_12618])).

tff(c_12992,plain,(
    ! [A_307,B_308] : k3_xboole_0(k4_xboole_0(A_307,B_308),B_308) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1114,c_20,c_12825])).

tff(c_133,plain,(
    ! [B_47,A_48] :
      ( r1_xboole_0(B_47,A_48)
      | k3_xboole_0(A_48,B_47) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_107,c_8])).

tff(c_139,plain,(
    ! [B_47,A_48] :
      ( k3_xboole_0(B_47,A_48) = k1_xboole_0
      | k3_xboole_0(A_48,B_47) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_133,c_4])).

tff(c_13501,plain,(
    ! [B_313,A_314] : k3_xboole_0(B_313,k4_xboole_0(A_314,B_313)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_12992,c_139])).

tff(c_40,plain,(
    r1_tarski('#skF_3',k2_xboole_0('#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( r1_xboole_0(A_3,B_4)
      | k3_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_789,plain,(
    ! [A_83,C_84,B_85] :
      ( r1_xboole_0(A_83,C_84)
      | ~ r1_xboole_0(B_85,C_84)
      | ~ r1_tarski(A_83,B_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_4270,plain,(
    ! [A_211,B_212,A_213] :
      ( r1_xboole_0(A_211,B_212)
      | ~ r1_tarski(A_211,A_213)
      | k3_xboole_0(A_213,B_212) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_6,c_789])).

tff(c_4305,plain,(
    ! [B_212] :
      ( r1_xboole_0('#skF_3',B_212)
      | k3_xboole_0(k2_xboole_0('#skF_4','#skF_5'),B_212) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_40,c_4270])).

tff(c_14530,plain,(
    ! [A_320] : r1_xboole_0('#skF_3',k4_xboole_0(A_320,k2_xboole_0('#skF_4','#skF_5'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_13501,c_4305])).

tff(c_14556,plain,(
    r1_xboole_0('#skF_3',k4_xboole_0('#skF_3','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_4255,c_14530])).

tff(c_14628,plain,(
    k3_xboole_0('#skF_3',k4_xboole_0('#skF_3','#skF_4')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14556,c_4])).

tff(c_293,plain,(
    ! [A_27,B_28] : k4_xboole_0(A_27,k3_xboole_0(A_27,B_28)) = k3_xboole_0(A_27,k4_xboole_0(A_27,B_28)) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_275])).

tff(c_3574,plain,(
    ! [A_27,B_28] : k3_xboole_0(A_27,k4_xboole_0(A_27,B_28)) = k4_xboole_0(A_27,B_28) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_293])).

tff(c_14691,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_14628,c_3574])).

tff(c_14864,plain,(
    k2_xboole_0('#skF_4',k1_xboole_0) = k2_xboole_0('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_14691,c_20])).

tff(c_14903,plain,(
    k2_xboole_0('#skF_4','#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2128,c_14864])).

tff(c_59,plain,(
    ! [B_39,A_40] : k2_xboole_0(B_39,A_40) = k2_xboole_0(A_40,B_39) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_34,plain,(
    ! [A_32,B_33] : r1_tarski(A_32,k2_xboole_0(A_32,B_33)) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_74,plain,(
    ! [A_40,B_39] : r1_tarski(A_40,k2_xboole_0(B_39,A_40)) ),
    inference(superposition,[status(thm),theory(equality)],[c_59,c_34])).

tff(c_15111,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_14903,c_74])).

tff(c_15151,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_15111])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:41:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.09/3.13  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.09/3.14  
% 8.09/3.14  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.09/3.14  %$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 8.09/3.14  
% 8.09/3.14  %Foreground sorts:
% 8.09/3.14  
% 8.09/3.14  
% 8.09/3.14  %Background operators:
% 8.09/3.14  
% 8.09/3.14  
% 8.09/3.14  %Foreground operators:
% 8.09/3.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.09/3.14  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.09/3.14  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 8.09/3.14  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.09/3.14  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.09/3.14  tff('#skF_5', type, '#skF_5': $i).
% 8.09/3.14  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 8.09/3.14  tff('#skF_3', type, '#skF_3': $i).
% 8.09/3.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.09/3.14  tff('#skF_4', type, '#skF_4': $i).
% 8.09/3.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.09/3.14  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 8.09/3.14  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.09/3.14  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 8.09/3.14  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 8.09/3.14  
% 8.09/3.16  tff(f_94, negated_conjecture, ~(![A, B, C]: ((r1_tarski(A, k2_xboole_0(B, C)) & r1_xboole_0(A, C)) => r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_xboole_1)).
% 8.09/3.16  tff(f_71, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 8.09/3.16  tff(f_73, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_xboole_1)).
% 8.09/3.16  tff(f_53, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 8.09/3.16  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 8.09/3.16  tff(f_67, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 8.09/3.16  tff(f_35, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 8.09/3.16  tff(f_79, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 8.09/3.16  tff(f_77, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 8.09/3.16  tff(f_69, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 8.09/3.16  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 8.09/3.16  tff(f_75, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 8.09/3.16  tff(f_85, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_xboole_1)).
% 8.09/3.16  tff(f_87, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 8.09/3.16  tff(c_36, plain, (~r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_94])).
% 8.09/3.16  tff(c_22, plain, (![A_19]: (k4_xboole_0(A_19, k1_xboole_0)=A_19)), inference(cnfTransformation, [status(thm)], [f_71])).
% 8.09/3.16  tff(c_192, plain, (![A_55, B_56]: (k4_xboole_0(k2_xboole_0(A_55, B_56), B_56)=k4_xboole_0(A_55, B_56))), inference(cnfTransformation, [status(thm)], [f_73])).
% 8.09/3.16  tff(c_208, plain, (![A_55]: (k4_xboole_0(A_55, k1_xboole_0)=k2_xboole_0(A_55, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_192, c_22])).
% 8.09/3.16  tff(c_228, plain, (![A_55]: (k2_xboole_0(A_55, k1_xboole_0)=A_55)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_208])).
% 8.09/3.16  tff(c_14, plain, (![A_7, B_8]: (r2_hidden('#skF_1'(A_7, B_8), A_7) | r1_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_53])).
% 8.09/3.16  tff(c_38, plain, (r1_xboole_0('#skF_3', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_94])).
% 8.09/3.16  tff(c_112, plain, (![A_45, B_46]: (k3_xboole_0(A_45, B_46)=k1_xboole_0 | ~r1_xboole_0(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.09/3.16  tff(c_124, plain, (k3_xboole_0('#skF_3', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_38, c_112])).
% 8.09/3.16  tff(c_424, plain, (![A_67, B_68, C_69]: (~r1_xboole_0(A_67, B_68) | ~r2_hidden(C_69, k3_xboole_0(A_67, B_68)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 8.09/3.16  tff(c_437, plain, (![C_69]: (~r1_xboole_0('#skF_3', '#skF_5') | ~r2_hidden(C_69, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_124, c_424])).
% 8.09/3.16  tff(c_443, plain, (![C_70]: (~r2_hidden(C_70, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_437])).
% 8.09/3.16  tff(c_449, plain, (![B_71]: (r1_xboole_0(k1_xboole_0, B_71))), inference(resolution, [status(thm)], [c_14, c_443])).
% 8.09/3.16  tff(c_8, plain, (![B_6, A_5]: (r1_xboole_0(B_6, A_5) | ~r1_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 8.09/3.16  tff(c_457, plain, (![B_72]: (r1_xboole_0(B_72, k1_xboole_0))), inference(resolution, [status(thm)], [c_449, c_8])).
% 8.09/3.16  tff(c_4, plain, (![A_3, B_4]: (k3_xboole_0(A_3, B_4)=k1_xboole_0 | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.09/3.16  tff(c_463, plain, (![B_72]: (k3_xboole_0(B_72, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_457, c_4])).
% 8.09/3.16  tff(c_275, plain, (![A_60, B_61]: (k4_xboole_0(A_60, k4_xboole_0(A_60, B_61))=k3_xboole_0(A_60, B_61))), inference(cnfTransformation, [status(thm)], [f_79])).
% 8.09/3.16  tff(c_302, plain, (![A_19]: (k4_xboole_0(A_19, A_19)=k3_xboole_0(A_19, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_22, c_275])).
% 8.09/3.16  tff(c_480, plain, (![A_19]: (k4_xboole_0(A_19, A_19)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_463, c_302])).
% 8.09/3.16  tff(c_30, plain, (![A_27, B_28]: (k4_xboole_0(A_27, k4_xboole_0(A_27, B_28))=k3_xboole_0(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_79])).
% 8.09/3.16  tff(c_501, plain, (![A_75]: (k4_xboole_0(A_75, A_75)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_463, c_302])).
% 8.09/3.16  tff(c_510, plain, (![A_75]: (k4_xboole_0(A_75, k1_xboole_0)=k3_xboole_0(A_75, A_75))), inference(superposition, [status(thm), theory('equality')], [c_501, c_30])).
% 8.09/3.16  tff(c_532, plain, (![A_75]: (k3_xboole_0(A_75, A_75)=A_75)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_510])).
% 8.09/3.16  tff(c_107, plain, (![A_43, B_44]: (r1_xboole_0(A_43, B_44) | k3_xboole_0(A_43, B_44)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.09/3.16  tff(c_110, plain, (![B_44, A_43]: (r1_xboole_0(B_44, A_43) | k3_xboole_0(A_43, B_44)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_107, c_8])).
% 8.09/3.16  tff(c_539, plain, (![A_76]: (k3_xboole_0(A_76, A_76)=A_76)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_510])).
% 8.09/3.16  tff(c_18, plain, (![A_12, B_13, C_16]: (~r1_xboole_0(A_12, B_13) | ~r2_hidden(C_16, k3_xboole_0(A_12, B_13)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 8.09/3.16  tff(c_888, plain, (![A_95, C_96]: (~r1_xboole_0(A_95, A_95) | ~r2_hidden(C_96, A_95))), inference(superposition, [status(thm), theory('equality')], [c_539, c_18])).
% 8.09/3.16  tff(c_915, plain, (![C_96, A_43]: (~r2_hidden(C_96, A_43) | k3_xboole_0(A_43, A_43)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_110, c_888])).
% 8.09/3.16  tff(c_932, plain, (![C_97, A_98]: (~r2_hidden(C_97, A_98) | k1_xboole_0!=A_98)), inference(demodulation, [status(thm), theory('equality')], [c_532, c_915])).
% 8.09/3.16  tff(c_980, plain, (![A_102, B_103]: (k1_xboole_0!=A_102 | r1_xboole_0(A_102, B_103))), inference(resolution, [status(thm)], [c_14, c_932])).
% 8.09/3.16  tff(c_1514, plain, (![A_126, B_127]: (k3_xboole_0(A_126, B_127)=k1_xboole_0 | k1_xboole_0!=A_126)), inference(resolution, [status(thm)], [c_980, c_4])).
% 8.09/3.16  tff(c_28, plain, (![A_25, B_26]: (k4_xboole_0(A_25, k3_xboole_0(A_25, B_26))=k4_xboole_0(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_77])).
% 8.09/3.16  tff(c_1534, plain, (![A_126, B_127]: (k4_xboole_0(A_126, k1_xboole_0)=k4_xboole_0(A_126, B_127) | k1_xboole_0!=A_126)), inference(superposition, [status(thm), theory('equality')], [c_1514, c_28])).
% 8.09/3.16  tff(c_1672, plain, (![A_132, B_133]: (k4_xboole_0(A_132, B_133)=A_132 | k1_xboole_0!=A_132)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_1534])).
% 8.09/3.16  tff(c_1934, plain, (![A_140, B_141]: (k3_xboole_0(A_140, B_141)=A_140 | k1_xboole_0!=A_140)), inference(superposition, [status(thm), theory('equality')], [c_30, c_1672])).
% 8.09/3.16  tff(c_1957, plain, (![A_140, B_141]: (k4_xboole_0(A_140, B_141)=k4_xboole_0(A_140, A_140) | k1_xboole_0!=A_140)), inference(superposition, [status(thm), theory('equality')], [c_1934, c_28])).
% 8.09/3.16  tff(c_2006, plain, (![A_142, B_143]: (k4_xboole_0(A_142, B_143)=k1_xboole_0 | k1_xboole_0!=A_142)), inference(demodulation, [status(thm), theory('equality')], [c_480, c_1957])).
% 8.09/3.16  tff(c_20, plain, (![A_17, B_18]: (k2_xboole_0(A_17, k4_xboole_0(B_18, A_17))=k2_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_69])).
% 8.09/3.16  tff(c_2066, plain, (![B_143, A_142]: (k2_xboole_0(B_143, k1_xboole_0)=k2_xboole_0(B_143, A_142) | k1_xboole_0!=A_142)), inference(superposition, [status(thm), theory('equality')], [c_2006, c_20])).
% 8.09/3.16  tff(c_2128, plain, (![B_143]: (k2_xboole_0(B_143, k1_xboole_0)=B_143)), inference(demodulation, [status(thm), theory('equality')], [c_228, c_2066])).
% 8.09/3.16  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 8.09/3.16  tff(c_635, plain, (![A_80, B_81]: (k4_xboole_0(A_80, k3_xboole_0(A_80, B_81))=k4_xboole_0(A_80, B_81))), inference(cnfTransformation, [status(thm)], [f_77])).
% 8.09/3.16  tff(c_672, plain, (k4_xboole_0('#skF_3', k1_xboole_0)=k4_xboole_0('#skF_3', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_124, c_635])).
% 8.09/3.16  tff(c_683, plain, (k4_xboole_0('#skF_3', '#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_22, c_672])).
% 8.09/3.16  tff(c_1030, plain, (![A_107, B_108, C_109]: (k4_xboole_0(k4_xboole_0(A_107, B_108), C_109)=k4_xboole_0(A_107, k2_xboole_0(B_108, C_109)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 8.09/3.16  tff(c_4158, plain, (![C_210]: (k4_xboole_0('#skF_3', k2_xboole_0('#skF_5', C_210))=k4_xboole_0('#skF_3', C_210))), inference(superposition, [status(thm), theory('equality')], [c_683, c_1030])).
% 8.09/3.16  tff(c_4255, plain, (![A_1]: (k4_xboole_0('#skF_3', k2_xboole_0(A_1, '#skF_5'))=k4_xboole_0('#skF_3', A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_4158])).
% 8.09/3.16  tff(c_1044, plain, (![A_107, B_108]: (k4_xboole_0(A_107, k2_xboole_0(B_108, k4_xboole_0(A_107, B_108)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1030, c_480])).
% 8.09/3.16  tff(c_1114, plain, (![A_107, B_108]: (k4_xboole_0(A_107, k2_xboole_0(B_108, A_107))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_1044])).
% 8.09/3.16  tff(c_1060, plain, (![C_109, A_107, B_108]: (k2_xboole_0(C_109, k4_xboole_0(A_107, k2_xboole_0(B_108, C_109)))=k2_xboole_0(C_109, k4_xboole_0(A_107, B_108)))), inference(superposition, [status(thm), theory('equality')], [c_1030, c_20])).
% 8.09/3.16  tff(c_26, plain, (![A_22, B_23, C_24]: (k4_xboole_0(k4_xboole_0(A_22, B_23), C_24)=k4_xboole_0(A_22, k2_xboole_0(B_23, C_24)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 8.09/3.16  tff(c_1051, plain, (![A_107, B_108, B_28]: (k4_xboole_0(A_107, k2_xboole_0(B_108, k4_xboole_0(k4_xboole_0(A_107, B_108), B_28)))=k3_xboole_0(k4_xboole_0(A_107, B_108), B_28))), inference(superposition, [status(thm), theory('equality')], [c_1030, c_30])).
% 8.09/3.16  tff(c_12618, plain, (![A_304, B_305, B_306]: (k4_xboole_0(A_304, k2_xboole_0(B_305, k4_xboole_0(A_304, k2_xboole_0(B_305, B_306))))=k3_xboole_0(k4_xboole_0(A_304, B_305), B_306))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_1051])).
% 8.09/3.16  tff(c_12825, plain, (![A_107, B_108]: (k4_xboole_0(A_107, k2_xboole_0(B_108, k4_xboole_0(A_107, B_108)))=k3_xboole_0(k4_xboole_0(A_107, B_108), B_108))), inference(superposition, [status(thm), theory('equality')], [c_1060, c_12618])).
% 8.09/3.16  tff(c_12992, plain, (![A_307, B_308]: (k3_xboole_0(k4_xboole_0(A_307, B_308), B_308)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1114, c_20, c_12825])).
% 8.09/3.16  tff(c_133, plain, (![B_47, A_48]: (r1_xboole_0(B_47, A_48) | k3_xboole_0(A_48, B_47)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_107, c_8])).
% 8.09/3.16  tff(c_139, plain, (![B_47, A_48]: (k3_xboole_0(B_47, A_48)=k1_xboole_0 | k3_xboole_0(A_48, B_47)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_133, c_4])).
% 8.09/3.16  tff(c_13501, plain, (![B_313, A_314]: (k3_xboole_0(B_313, k4_xboole_0(A_314, B_313))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_12992, c_139])).
% 8.09/3.16  tff(c_40, plain, (r1_tarski('#skF_3', k2_xboole_0('#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_94])).
% 8.09/3.16  tff(c_6, plain, (![A_3, B_4]: (r1_xboole_0(A_3, B_4) | k3_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.09/3.16  tff(c_789, plain, (![A_83, C_84, B_85]: (r1_xboole_0(A_83, C_84) | ~r1_xboole_0(B_85, C_84) | ~r1_tarski(A_83, B_85))), inference(cnfTransformation, [status(thm)], [f_85])).
% 8.09/3.16  tff(c_4270, plain, (![A_211, B_212, A_213]: (r1_xboole_0(A_211, B_212) | ~r1_tarski(A_211, A_213) | k3_xboole_0(A_213, B_212)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_789])).
% 8.09/3.16  tff(c_4305, plain, (![B_212]: (r1_xboole_0('#skF_3', B_212) | k3_xboole_0(k2_xboole_0('#skF_4', '#skF_5'), B_212)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_40, c_4270])).
% 8.09/3.16  tff(c_14530, plain, (![A_320]: (r1_xboole_0('#skF_3', k4_xboole_0(A_320, k2_xboole_0('#skF_4', '#skF_5'))))), inference(superposition, [status(thm), theory('equality')], [c_13501, c_4305])).
% 8.09/3.16  tff(c_14556, plain, (r1_xboole_0('#skF_3', k4_xboole_0('#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_4255, c_14530])).
% 8.09/3.16  tff(c_14628, plain, (k3_xboole_0('#skF_3', k4_xboole_0('#skF_3', '#skF_4'))=k1_xboole_0), inference(resolution, [status(thm)], [c_14556, c_4])).
% 8.09/3.16  tff(c_293, plain, (![A_27, B_28]: (k4_xboole_0(A_27, k3_xboole_0(A_27, B_28))=k3_xboole_0(A_27, k4_xboole_0(A_27, B_28)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_275])).
% 8.09/3.16  tff(c_3574, plain, (![A_27, B_28]: (k3_xboole_0(A_27, k4_xboole_0(A_27, B_28))=k4_xboole_0(A_27, B_28))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_293])).
% 8.09/3.16  tff(c_14691, plain, (k4_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_14628, c_3574])).
% 8.09/3.16  tff(c_14864, plain, (k2_xboole_0('#skF_4', k1_xboole_0)=k2_xboole_0('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_14691, c_20])).
% 8.09/3.16  tff(c_14903, plain, (k2_xboole_0('#skF_4', '#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2128, c_14864])).
% 8.09/3.16  tff(c_59, plain, (![B_39, A_40]: (k2_xboole_0(B_39, A_40)=k2_xboole_0(A_40, B_39))), inference(cnfTransformation, [status(thm)], [f_27])).
% 8.09/3.16  tff(c_34, plain, (![A_32, B_33]: (r1_tarski(A_32, k2_xboole_0(A_32, B_33)))), inference(cnfTransformation, [status(thm)], [f_87])).
% 8.09/3.16  tff(c_74, plain, (![A_40, B_39]: (r1_tarski(A_40, k2_xboole_0(B_39, A_40)))), inference(superposition, [status(thm), theory('equality')], [c_59, c_34])).
% 8.09/3.16  tff(c_15111, plain, (r1_tarski('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_14903, c_74])).
% 8.09/3.16  tff(c_15151, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_15111])).
% 8.09/3.16  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.09/3.16  
% 8.09/3.16  Inference rules
% 8.09/3.16  ----------------------
% 8.09/3.16  #Ref     : 1
% 8.09/3.16  #Sup     : 3848
% 8.09/3.16  #Fact    : 0
% 8.09/3.16  #Define  : 0
% 8.09/3.16  #Split   : 5
% 8.09/3.16  #Chain   : 0
% 8.09/3.16  #Close   : 0
% 8.09/3.16  
% 8.09/3.16  Ordering : KBO
% 8.09/3.16  
% 8.09/3.16  Simplification rules
% 8.09/3.16  ----------------------
% 8.09/3.16  #Subsume      : 645
% 8.09/3.16  #Demod        : 2984
% 8.09/3.16  #Tautology    : 1947
% 8.09/3.16  #SimpNegUnit  : 71
% 8.09/3.16  #BackRed      : 7
% 8.09/3.16  
% 8.09/3.16  #Partial instantiations: 0
% 8.09/3.16  #Strategies tried      : 1
% 8.09/3.16  
% 8.09/3.16  Timing (in seconds)
% 8.09/3.16  ----------------------
% 8.09/3.17  Preprocessing        : 0.29
% 8.09/3.17  Parsing              : 0.16
% 8.09/3.17  CNF conversion       : 0.02
% 8.09/3.17  Main loop            : 2.11
% 8.09/3.17  Inferencing          : 0.50
% 8.09/3.17  Reduction            : 1.08
% 8.09/3.17  Demodulation         : 0.90
% 8.09/3.17  BG Simplification    : 0.06
% 8.09/3.17  Subsumption          : 0.38
% 8.09/3.17  Abstraction          : 0.08
% 8.09/3.17  MUC search           : 0.00
% 8.09/3.17  Cooper               : 0.00
% 8.09/3.17  Total                : 2.44
% 8.09/3.17  Index Insertion      : 0.00
% 8.09/3.17  Index Deletion       : 0.00
% 8.09/3.17  Index Matching       : 0.00
% 8.09/3.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
