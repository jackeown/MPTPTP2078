%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:52 EST 2020

% Result     : Theorem 3.44s
% Output     : CNFRefutation 3.44s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 206 expanded)
%              Number of leaves         :   39 (  82 expanded)
%              Depth                    :   13
%              Number of atoms          :  117 ( 296 expanded)
%              Number of equality atoms :   64 ( 160 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_xboole_0 > v1_relat_1 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k4_relat_1 > k2_relat_1 > k1_tarski > k1_setfam_1 > k1_relat_1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_39,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_56,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_104,negated_conjecture,(
    ~ ( k1_relat_1(k1_xboole_0) = k1_xboole_0
      & k2_relat_1(k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_37,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_45,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k4_xboole_0(B,k1_tarski(C)))
    <=> ( r2_hidden(A,B)
        & A != C ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).

tff(f_47,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_75,axiom,(
    ! [A,B,C,D] : v1_relat_1(k2_tarski(k4_tarski(A,B),k4_tarski(C,D))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_relat_1)).

tff(f_94,axiom,(
    ! [A,B,C,D,E] :
      ( v1_relat_1(E)
     => ( E = k2_tarski(k4_tarski(A,B),k4_tarski(C,D))
       => ( k1_relat_1(E) = k2_tarski(A,C)
          & k2_relat_1(E) = k2_tarski(B,D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_relat_1)).

tff(f_29,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_69,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_82,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k2_xboole_0(A,B)) = k2_xboole_0(k1_relat_1(A),k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_relat_1)).

tff(f_43,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_73,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => v1_relat_1(k4_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).

tff(f_41,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_53,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_100,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k2_relat_1(A) = k1_relat_1(k4_relat_1(A))
        & k1_relat_1(A) = k2_relat_1(k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).

tff(f_86,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_xboole_0(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_relat_1)).

tff(c_10,plain,(
    ! [A_5] : k2_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_123,plain,(
    ! [A_43,B_44] : k2_xboole_0(k1_tarski(A_43),B_44) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_127,plain,(
    ! [A_43] : k1_tarski(A_43) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_123])).

tff(c_54,plain,
    ( k2_relat_1(k1_xboole_0) != k1_xboole_0
    | k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_113,plain,(
    k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_8,plain,(
    ! [A_3] :
      ( r2_hidden('#skF_1'(A_3),A_3)
      | k1_xboole_0 = A_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_16,plain,(
    ! [A_9] : k4_xboole_0(k1_xboole_0,A_9) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_130,plain,(
    ! [C_47,B_48] : ~ r2_hidden(C_47,k4_xboole_0(B_48,k1_tarski(C_47))) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_133,plain,(
    ! [C_47] : ~ r2_hidden(C_47,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_130])).

tff(c_18,plain,(
    ! [A_10] : k2_tarski(A_10,A_10) = k1_tarski(A_10) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_383,plain,(
    ! [A_66,B_67,C_68,D_69] : v1_relat_1(k2_tarski(k4_tarski(A_66,B_67),k4_tarski(C_68,D_69))) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_387,plain,(
    ! [A_66,B_67] : v1_relat_1(k1_tarski(k4_tarski(A_66,B_67))) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_383])).

tff(c_40,plain,(
    ! [A_22,B_23,C_24,D_25] : v1_relat_1(k2_tarski(k4_tarski(A_22,B_23),k4_tarski(C_24,D_25))) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_48,plain,(
    ! [A_30,B_31,C_32,D_33] :
      ( k1_relat_1(k2_tarski(k4_tarski(A_30,B_31),k4_tarski(C_32,D_33))) = k2_tarski(A_30,C_32)
      | ~ v1_relat_1(k2_tarski(k4_tarski(A_30,B_31),k4_tarski(C_32,D_33))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_511,plain,(
    ! [A_91,B_92,C_93,D_94] : k1_relat_1(k2_tarski(k4_tarski(A_91,B_92),k4_tarski(C_93,D_94))) = k2_tarski(A_91,C_93) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_48])).

tff(c_524,plain,(
    ! [A_91,B_92] : k2_tarski(A_91,A_91) = k1_relat_1(k1_tarski(k4_tarski(A_91,B_92))) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_511])).

tff(c_529,plain,(
    ! [A_91,B_92] : k1_relat_1(k1_tarski(k4_tarski(A_91,B_92))) = k1_tarski(A_91) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_524])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_99,plain,(
    ! [A_40] :
      ( v1_relat_1(A_40)
      | ~ v1_xboole_0(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_103,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_6,c_99])).

tff(c_171,plain,(
    ! [B_53,A_54] : k2_xboole_0(B_53,A_54) = k2_xboole_0(A_54,B_53) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_201,plain,(
    ! [A_54] : k2_xboole_0(k1_xboole_0,A_54) = A_54 ),
    inference(superposition,[status(thm),theory(equality)],[c_171,c_10])).

tff(c_530,plain,(
    ! [A_95,B_96] :
      ( k2_xboole_0(k1_relat_1(A_95),k1_relat_1(B_96)) = k1_relat_1(k2_xboole_0(A_95,B_96))
      | ~ v1_relat_1(B_96)
      | ~ v1_relat_1(A_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_14,plain,(
    ! [A_7,B_8] : k4_xboole_0(A_7,k2_xboole_0(A_7,B_8)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_597,plain,(
    ! [A_99,B_100] :
      ( k4_xboole_0(k1_relat_1(A_99),k1_relat_1(k2_xboole_0(A_99,B_100))) = k1_xboole_0
      | ~ v1_relat_1(B_100)
      | ~ v1_relat_1(A_99) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_530,c_14])).

tff(c_618,plain,(
    ! [A_54] :
      ( k4_xboole_0(k1_relat_1(k1_xboole_0),k1_relat_1(A_54)) = k1_xboole_0
      | ~ v1_relat_1(A_54)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_201,c_597])).

tff(c_638,plain,(
    ! [A_101] :
      ( k4_xboole_0(k1_relat_1(k1_xboole_0),k1_relat_1(A_101)) = k1_xboole_0
      | ~ v1_relat_1(A_101) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_618])).

tff(c_659,plain,(
    ! [A_91,B_92] :
      ( k4_xboole_0(k1_relat_1(k1_xboole_0),k1_tarski(A_91)) = k1_xboole_0
      | ~ v1_relat_1(k1_tarski(k4_tarski(A_91,B_92))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_529,c_638])).

tff(c_710,plain,(
    ! [A_103] : k4_xboole_0(k1_relat_1(k1_xboole_0),k1_tarski(A_103)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_387,c_659])).

tff(c_28,plain,(
    ! [A_15,B_16,C_17] :
      ( r2_hidden(A_15,k4_xboole_0(B_16,k1_tarski(C_17)))
      | C_17 = A_15
      | ~ r2_hidden(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_715,plain,(
    ! [A_15,A_103] :
      ( r2_hidden(A_15,k1_xboole_0)
      | A_15 = A_103
      | ~ r2_hidden(A_15,k1_relat_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_710,c_28])).

tff(c_727,plain,(
    ! [A_105,A_104] :
      ( A_105 = A_104
      | ~ r2_hidden(A_104,k1_relat_1(k1_xboole_0)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_133,c_715])).

tff(c_730,plain,(
    ! [A_105] :
      ( A_105 = '#skF_1'(k1_relat_1(k1_xboole_0))
      | k1_relat_1(k1_xboole_0) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_727])).

tff(c_747,plain,(
    '#skF_1'(k1_relat_1(k1_xboole_0)) = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_113,c_730])).

tff(c_733,plain,(
    ! [A_105] : A_105 = '#skF_1'(k1_relat_1(k1_xboole_0)) ),
    inference(negUnitSimplification,[status(thm)],[c_113,c_730])).

tff(c_1072,plain,(
    ! [A_1002] : k1_xboole_0 = A_1002 ),
    inference(superposition,[status(thm),theory(equality)],[c_747,c_733])).

tff(c_1085,plain,(
    ! [A_91] : k1_tarski(A_91) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1072,c_529])).

tff(c_1197,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_127,c_1085])).

tff(c_1198,plain,(
    k2_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_1199,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_38,plain,(
    ! [A_21] :
      ( v1_relat_1(k4_relat_1(A_21))
      | ~ v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_12,plain,(
    ! [A_6] : k3_xboole_0(A_6,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_22,plain,(
    ! [A_11] : k2_zfmisc_1(A_11,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_50,plain,(
    ! [A_35] :
      ( k2_relat_1(k4_relat_1(A_35)) = k1_relat_1(A_35)
      | ~ v1_relat_1(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_1505,plain,(
    ! [A_1686] :
      ( k3_xboole_0(A_1686,k2_zfmisc_1(k1_relat_1(A_1686),k2_relat_1(A_1686))) = A_1686
      | ~ v1_relat_1(A_1686) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_1989,plain,(
    ! [A_1724] :
      ( k3_xboole_0(k4_relat_1(A_1724),k2_zfmisc_1(k1_relat_1(k4_relat_1(A_1724)),k1_relat_1(A_1724))) = k4_relat_1(A_1724)
      | ~ v1_relat_1(k4_relat_1(A_1724))
      | ~ v1_relat_1(A_1724) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_1505])).

tff(c_2010,plain,
    ( k3_xboole_0(k4_relat_1(k1_xboole_0),k2_zfmisc_1(k1_relat_1(k4_relat_1(k1_xboole_0)),k1_xboole_0)) = k4_relat_1(k1_xboole_0)
    | ~ v1_relat_1(k4_relat_1(k1_xboole_0))
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1199,c_1989])).

tff(c_2018,plain,
    ( k4_relat_1(k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(k4_relat_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_12,c_22,c_2010])).

tff(c_2019,plain,(
    ~ v1_relat_1(k4_relat_1(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_2018])).

tff(c_2022,plain,(
    ~ v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_38,c_2019])).

tff(c_2026,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_2022])).

tff(c_2027,plain,(
    k4_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_2018])).

tff(c_2038,plain,
    ( k2_relat_1(k1_xboole_0) = k1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_2027,c_50])).

tff(c_2052,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_1199,c_2038])).

tff(c_2054,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1198,c_2052])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.33  % Computer   : n005.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % DateTime   : Tue Dec  1 15:59:02 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.44/1.64  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.44/1.65  
% 3.44/1.65  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.44/1.65  %$ r2_hidden > v1_xboole_0 > v1_relat_1 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k4_relat_1 > k2_relat_1 > k1_tarski > k1_setfam_1 > k1_relat_1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_1
% 3.44/1.65  
% 3.44/1.65  %Foreground sorts:
% 3.44/1.65  
% 3.44/1.65  
% 3.44/1.65  %Background operators:
% 3.44/1.65  
% 3.44/1.65  
% 3.44/1.65  %Foreground operators:
% 3.44/1.65  tff(o_0_0_xboole_0, type, o_0_0_xboole_0: $i).
% 3.44/1.65  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.44/1.65  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.44/1.65  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.44/1.65  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.44/1.65  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.44/1.65  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.44/1.65  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.44/1.65  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.44/1.65  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.44/1.65  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.44/1.65  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.44/1.65  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.44/1.65  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.44/1.65  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.44/1.65  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.44/1.65  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.44/1.65  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.44/1.65  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 3.44/1.65  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.44/1.65  
% 3.44/1.67  tff(f_39, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 3.44/1.67  tff(f_56, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 3.44/1.67  tff(f_104, negated_conjecture, ~((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 3.44/1.67  tff(f_37, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 3.44/1.67  tff(f_45, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 3.44/1.67  tff(f_63, axiom, (![A, B, C]: (r2_hidden(A, k4_xboole_0(B, k1_tarski(C))) <=> (r2_hidden(A, B) & ~(A = C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 3.44/1.67  tff(f_47, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 3.44/1.67  tff(f_75, axiom, (![A, B, C, D]: v1_relat_1(k2_tarski(k4_tarski(A, B), k4_tarski(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc7_relat_1)).
% 3.44/1.67  tff(f_94, axiom, (![A, B, C, D, E]: (v1_relat_1(E) => ((E = k2_tarski(k4_tarski(A, B), k4_tarski(C, D))) => ((k1_relat_1(E) = k2_tarski(A, C)) & (k2_relat_1(E) = k2_tarski(B, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_relat_1)).
% 3.44/1.67  tff(f_29, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.44/1.67  tff(f_69, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relat_1)).
% 3.44/1.67  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 3.44/1.67  tff(f_82, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k2_xboole_0(A, B)) = k2_xboole_0(k1_relat_1(A), k1_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_relat_1)).
% 3.44/1.67  tff(f_43, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 3.44/1.67  tff(f_73, axiom, (![A]: (v1_relat_1(A) => v1_relat_1(k4_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_relat_1)).
% 3.44/1.67  tff(f_41, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 3.44/1.67  tff(f_53, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 3.44/1.67  tff(f_100, axiom, (![A]: (v1_relat_1(A) => ((k2_relat_1(A) = k1_relat_1(k4_relat_1(A))) & (k1_relat_1(A) = k2_relat_1(k4_relat_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_relat_1)).
% 3.44/1.67  tff(f_86, axiom, (![A]: (v1_relat_1(A) => (k3_xboole_0(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_relat_1)).
% 3.44/1.67  tff(c_10, plain, (![A_5]: (k2_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.44/1.67  tff(c_123, plain, (![A_43, B_44]: (k2_xboole_0(k1_tarski(A_43), B_44)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.44/1.67  tff(c_127, plain, (![A_43]: (k1_tarski(A_43)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_10, c_123])).
% 3.44/1.67  tff(c_54, plain, (k2_relat_1(k1_xboole_0)!=k1_xboole_0 | k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.44/1.67  tff(c_113, plain, (k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_54])).
% 3.44/1.67  tff(c_8, plain, (![A_3]: (r2_hidden('#skF_1'(A_3), A_3) | k1_xboole_0=A_3)), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.44/1.67  tff(c_16, plain, (![A_9]: (k4_xboole_0(k1_xboole_0, A_9)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.44/1.67  tff(c_130, plain, (![C_47, B_48]: (~r2_hidden(C_47, k4_xboole_0(B_48, k1_tarski(C_47))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.44/1.67  tff(c_133, plain, (![C_47]: (~r2_hidden(C_47, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_16, c_130])).
% 3.44/1.67  tff(c_18, plain, (![A_10]: (k2_tarski(A_10, A_10)=k1_tarski(A_10))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.44/1.67  tff(c_383, plain, (![A_66, B_67, C_68, D_69]: (v1_relat_1(k2_tarski(k4_tarski(A_66, B_67), k4_tarski(C_68, D_69))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.44/1.67  tff(c_387, plain, (![A_66, B_67]: (v1_relat_1(k1_tarski(k4_tarski(A_66, B_67))))), inference(superposition, [status(thm), theory('equality')], [c_18, c_383])).
% 3.44/1.67  tff(c_40, plain, (![A_22, B_23, C_24, D_25]: (v1_relat_1(k2_tarski(k4_tarski(A_22, B_23), k4_tarski(C_24, D_25))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.44/1.67  tff(c_48, plain, (![A_30, B_31, C_32, D_33]: (k1_relat_1(k2_tarski(k4_tarski(A_30, B_31), k4_tarski(C_32, D_33)))=k2_tarski(A_30, C_32) | ~v1_relat_1(k2_tarski(k4_tarski(A_30, B_31), k4_tarski(C_32, D_33))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.44/1.67  tff(c_511, plain, (![A_91, B_92, C_93, D_94]: (k1_relat_1(k2_tarski(k4_tarski(A_91, B_92), k4_tarski(C_93, D_94)))=k2_tarski(A_91, C_93))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_48])).
% 3.44/1.67  tff(c_524, plain, (![A_91, B_92]: (k2_tarski(A_91, A_91)=k1_relat_1(k1_tarski(k4_tarski(A_91, B_92))))), inference(superposition, [status(thm), theory('equality')], [c_18, c_511])).
% 3.44/1.67  tff(c_529, plain, (![A_91, B_92]: (k1_relat_1(k1_tarski(k4_tarski(A_91, B_92)))=k1_tarski(A_91))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_524])).
% 3.44/1.67  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.44/1.67  tff(c_99, plain, (![A_40]: (v1_relat_1(A_40) | ~v1_xboole_0(A_40))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.44/1.67  tff(c_103, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_99])).
% 3.44/1.67  tff(c_171, plain, (![B_53, A_54]: (k2_xboole_0(B_53, A_54)=k2_xboole_0(A_54, B_53))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.44/1.67  tff(c_201, plain, (![A_54]: (k2_xboole_0(k1_xboole_0, A_54)=A_54)), inference(superposition, [status(thm), theory('equality')], [c_171, c_10])).
% 3.44/1.67  tff(c_530, plain, (![A_95, B_96]: (k2_xboole_0(k1_relat_1(A_95), k1_relat_1(B_96))=k1_relat_1(k2_xboole_0(A_95, B_96)) | ~v1_relat_1(B_96) | ~v1_relat_1(A_95))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.44/1.67  tff(c_14, plain, (![A_7, B_8]: (k4_xboole_0(A_7, k2_xboole_0(A_7, B_8))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.44/1.67  tff(c_597, plain, (![A_99, B_100]: (k4_xboole_0(k1_relat_1(A_99), k1_relat_1(k2_xboole_0(A_99, B_100)))=k1_xboole_0 | ~v1_relat_1(B_100) | ~v1_relat_1(A_99))), inference(superposition, [status(thm), theory('equality')], [c_530, c_14])).
% 3.44/1.67  tff(c_618, plain, (![A_54]: (k4_xboole_0(k1_relat_1(k1_xboole_0), k1_relat_1(A_54))=k1_xboole_0 | ~v1_relat_1(A_54) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_201, c_597])).
% 3.44/1.67  tff(c_638, plain, (![A_101]: (k4_xboole_0(k1_relat_1(k1_xboole_0), k1_relat_1(A_101))=k1_xboole_0 | ~v1_relat_1(A_101))), inference(demodulation, [status(thm), theory('equality')], [c_103, c_618])).
% 3.44/1.67  tff(c_659, plain, (![A_91, B_92]: (k4_xboole_0(k1_relat_1(k1_xboole_0), k1_tarski(A_91))=k1_xboole_0 | ~v1_relat_1(k1_tarski(k4_tarski(A_91, B_92))))), inference(superposition, [status(thm), theory('equality')], [c_529, c_638])).
% 3.44/1.67  tff(c_710, plain, (![A_103]: (k4_xboole_0(k1_relat_1(k1_xboole_0), k1_tarski(A_103))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_387, c_659])).
% 3.44/1.67  tff(c_28, plain, (![A_15, B_16, C_17]: (r2_hidden(A_15, k4_xboole_0(B_16, k1_tarski(C_17))) | C_17=A_15 | ~r2_hidden(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.44/1.67  tff(c_715, plain, (![A_15, A_103]: (r2_hidden(A_15, k1_xboole_0) | A_15=A_103 | ~r2_hidden(A_15, k1_relat_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_710, c_28])).
% 3.44/1.67  tff(c_727, plain, (![A_105, A_104]: (A_105=A_104 | ~r2_hidden(A_104, k1_relat_1(k1_xboole_0)))), inference(negUnitSimplification, [status(thm)], [c_133, c_715])).
% 3.44/1.67  tff(c_730, plain, (![A_105]: (A_105='#skF_1'(k1_relat_1(k1_xboole_0)) | k1_relat_1(k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_727])).
% 3.44/1.67  tff(c_747, plain, ('#skF_1'(k1_relat_1(k1_xboole_0))=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_113, c_730])).
% 3.44/1.67  tff(c_733, plain, (![A_105]: (A_105='#skF_1'(k1_relat_1(k1_xboole_0)))), inference(negUnitSimplification, [status(thm)], [c_113, c_730])).
% 3.44/1.67  tff(c_1072, plain, (![A_1002]: (k1_xboole_0=A_1002)), inference(superposition, [status(thm), theory('equality')], [c_747, c_733])).
% 3.44/1.67  tff(c_1085, plain, (![A_91]: (k1_tarski(A_91)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1072, c_529])).
% 3.44/1.67  tff(c_1197, plain, $false, inference(negUnitSimplification, [status(thm)], [c_127, c_1085])).
% 3.44/1.67  tff(c_1198, plain, (k2_relat_1(k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_54])).
% 3.44/1.67  tff(c_1199, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_54])).
% 3.44/1.67  tff(c_38, plain, (![A_21]: (v1_relat_1(k4_relat_1(A_21)) | ~v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.44/1.67  tff(c_12, plain, (![A_6]: (k3_xboole_0(A_6, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.44/1.67  tff(c_22, plain, (![A_11]: (k2_zfmisc_1(A_11, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.44/1.67  tff(c_50, plain, (![A_35]: (k2_relat_1(k4_relat_1(A_35))=k1_relat_1(A_35) | ~v1_relat_1(A_35))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.44/1.67  tff(c_1505, plain, (![A_1686]: (k3_xboole_0(A_1686, k2_zfmisc_1(k1_relat_1(A_1686), k2_relat_1(A_1686)))=A_1686 | ~v1_relat_1(A_1686))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.44/1.67  tff(c_1989, plain, (![A_1724]: (k3_xboole_0(k4_relat_1(A_1724), k2_zfmisc_1(k1_relat_1(k4_relat_1(A_1724)), k1_relat_1(A_1724)))=k4_relat_1(A_1724) | ~v1_relat_1(k4_relat_1(A_1724)) | ~v1_relat_1(A_1724))), inference(superposition, [status(thm), theory('equality')], [c_50, c_1505])).
% 3.44/1.67  tff(c_2010, plain, (k3_xboole_0(k4_relat_1(k1_xboole_0), k2_zfmisc_1(k1_relat_1(k4_relat_1(k1_xboole_0)), k1_xboole_0))=k4_relat_1(k1_xboole_0) | ~v1_relat_1(k4_relat_1(k1_xboole_0)) | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1199, c_1989])).
% 3.44/1.67  tff(c_2018, plain, (k4_relat_1(k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k4_relat_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_103, c_12, c_22, c_2010])).
% 3.44/1.67  tff(c_2019, plain, (~v1_relat_1(k4_relat_1(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_2018])).
% 3.44/1.67  tff(c_2022, plain, (~v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_38, c_2019])).
% 3.44/1.67  tff(c_2026, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_103, c_2022])).
% 3.44/1.67  tff(c_2027, plain, (k4_relat_1(k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_2018])).
% 3.44/1.67  tff(c_2038, plain, (k2_relat_1(k1_xboole_0)=k1_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2027, c_50])).
% 3.44/1.67  tff(c_2052, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_103, c_1199, c_2038])).
% 3.44/1.67  tff(c_2054, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1198, c_2052])).
% 3.44/1.67  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.44/1.67  
% 3.44/1.67  Inference rules
% 3.44/1.67  ----------------------
% 3.44/1.67  #Ref     : 0
% 3.44/1.67  #Sup     : 535
% 3.44/1.67  #Fact    : 0
% 3.44/1.67  #Define  : 0
% 3.44/1.67  #Split   : 2
% 3.44/1.67  #Chain   : 0
% 3.44/1.67  #Close   : 0
% 3.44/1.67  
% 3.44/1.67  Ordering : KBO
% 3.44/1.67  
% 3.44/1.67  Simplification rules
% 3.44/1.67  ----------------------
% 3.44/1.67  #Subsume      : 79
% 3.44/1.67  #Demod        : 144
% 3.44/1.67  #Tautology    : 210
% 3.44/1.67  #SimpNegUnit  : 29
% 3.44/1.67  #BackRed      : 0
% 3.44/1.67  
% 3.44/1.67  #Partial instantiations: 686
% 3.44/1.67  #Strategies tried      : 1
% 3.44/1.67  
% 3.44/1.67  Timing (in seconds)
% 3.44/1.67  ----------------------
% 3.44/1.67  Preprocessing        : 0.34
% 3.44/1.67  Parsing              : 0.19
% 3.44/1.67  CNF conversion       : 0.02
% 3.44/1.67  Main loop            : 0.52
% 3.44/1.67  Inferencing          : 0.21
% 3.44/1.67  Reduction            : 0.18
% 3.44/1.67  Demodulation         : 0.13
% 3.44/1.67  BG Simplification    : 0.03
% 3.44/1.67  Subsumption          : 0.07
% 3.44/1.67  Abstraction          : 0.03
% 3.44/1.67  MUC search           : 0.00
% 3.44/1.67  Cooper               : 0.00
% 3.44/1.67  Total                : 0.90
% 3.44/1.67  Index Insertion      : 0.00
% 3.44/1.67  Index Deletion       : 0.00
% 3.44/1.67  Index Matching       : 0.00
% 3.44/1.67  BG Taut test         : 0.00
%------------------------------------------------------------------------------
