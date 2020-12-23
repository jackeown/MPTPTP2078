%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:46 EST 2020

% Result     : Theorem 24.48s
% Output     : CNFRefutation 24.48s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 286 expanded)
%              Number of leaves         :   37 ( 111 expanded)
%              Depth                    :   13
%              Number of atoms          :  106 ( 340 expanded)
%              Number of equality atoms :   80 ( 284 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(f_54,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_56,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_52,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_33,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_76,axiom,(
    ! [A,B] : k4_xboole_0(k1_tarski(A),k2_tarski(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_zfmisc_1)).

tff(f_74,axiom,(
    ! [A,B] : k3_xboole_0(k1_tarski(A),k2_tarski(A,B)) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_81,axiom,(
    ! [A,B] :
      ( A != B
     => k5_xboole_0(k1_tarski(A),k1_tarski(B)) = k2_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k3_xboole_0(B,k1_tarski(A)) = k1_tarski(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l31_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_31,axiom,(
    ! [A,B,C] : k5_xboole_0(k3_xboole_0(A,B),k3_xboole_0(C,B)) = k3_xboole_0(k5_xboole_0(A,C),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).

tff(f_72,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_84,negated_conjecture,(
    ~ ! [A,B] : k3_tarski(k2_tarski(k1_tarski(A),k1_tarski(B))) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_zfmisc_1)).

tff(c_38,plain,(
    ! [A_21] : k2_tarski(A_21,A_21) = k1_tarski(A_21) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_118,plain,(
    ! [A_72,B_73] : k1_enumset1(A_72,A_72,B_73) = k2_tarski(A_72,B_73) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_16,plain,(
    ! [E_20,A_14,B_15] : r2_hidden(E_20,k1_enumset1(A_14,B_15,E_20)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_136,plain,(
    ! [B_74,A_75] : r2_hidden(B_74,k2_tarski(A_75,B_74)) ),
    inference(superposition,[status(thm),theory(equality)],[c_118,c_16])).

tff(c_139,plain,(
    ! [A_21] : r2_hidden(A_21,k1_tarski(A_21)) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_136])).

tff(c_124,plain,(
    ! [B_73,A_72] : r2_hidden(B_73,k2_tarski(A_72,B_73)) ),
    inference(superposition,[status(thm),theory(equality)],[c_118,c_16])).

tff(c_8,plain,(
    ! [A_8] : k5_xboole_0(A_8,k1_xboole_0) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_58,plain,(
    ! [A_55,B_56] : k4_xboole_0(k1_tarski(A_55),k2_tarski(A_55,B_56)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_56,plain,(
    ! [A_53,B_54] : k3_xboole_0(k1_tarski(A_53),k2_tarski(A_53,B_54)) = k1_tarski(A_53) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_214,plain,(
    ! [A_88,B_89] : k5_xboole_0(A_88,k3_xboole_0(A_88,B_89)) = k4_xboole_0(A_88,B_89) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_226,plain,(
    ! [A_53,B_54] : k5_xboole_0(k1_tarski(A_53),k1_tarski(A_53)) = k4_xboole_0(k1_tarski(A_53),k2_tarski(A_53,B_54)) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_214])).

tff(c_236,plain,(
    ! [A_53] : k5_xboole_0(k1_tarski(A_53),k1_tarski(A_53)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_226])).

tff(c_60,plain,(
    ! [A_57,B_58] :
      ( k5_xboole_0(k1_tarski(A_57),k1_tarski(B_58)) = k2_tarski(A_57,B_58)
      | B_58 = A_57 ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_567,plain,(
    ! [A_108,B_109,C_110] : k5_xboole_0(k5_xboole_0(A_108,B_109),C_110) = k5_xboole_0(A_108,k5_xboole_0(B_109,C_110)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_8140,plain,(
    ! [A_298,B_299,C_300] :
      ( k5_xboole_0(k1_tarski(A_298),k5_xboole_0(k1_tarski(B_299),C_300)) = k5_xboole_0(k2_tarski(A_298,B_299),C_300)
      | B_299 = A_298 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_567])).

tff(c_8273,plain,(
    ! [A_298,A_53] :
      ( k5_xboole_0(k2_tarski(A_298,A_53),k1_tarski(A_53)) = k5_xboole_0(k1_tarski(A_298),k1_xboole_0)
      | A_53 = A_298 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_236,c_8140])).

tff(c_8303,plain,(
    ! [A_298,A_53] :
      ( k5_xboole_0(k2_tarski(A_298,A_53),k1_tarski(A_53)) = k1_tarski(A_298)
      | A_53 = A_298 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_8273])).

tff(c_10,plain,(
    ! [A_9,B_10,C_11] : k5_xboole_0(k5_xboole_0(A_9,B_10),C_11) = k5_xboole_0(A_9,k5_xboole_0(B_10,C_11)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_52,plain,(
    ! [B_50,A_49] :
      ( k3_xboole_0(B_50,k1_tarski(A_49)) = k1_tarski(A_49)
      | ~ r2_hidden(A_49,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_856,plain,(
    ! [A_122,B_123,C_124] : k5_xboole_0(k3_xboole_0(A_122,B_123),k3_xboole_0(C_124,B_123)) = k3_xboole_0(k5_xboole_0(A_122,C_124),B_123) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_14513,plain,(
    ! [A_387,A_388,B_389] : k5_xboole_0(k3_xboole_0(A_387,k2_tarski(A_388,B_389)),k1_tarski(A_388)) = k3_xboole_0(k5_xboole_0(A_387,k1_tarski(A_388)),k2_tarski(A_388,B_389)) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_856])).

tff(c_14608,plain,(
    ! [A_387,A_21] : k5_xboole_0(k3_xboole_0(A_387,k1_tarski(A_21)),k1_tarski(A_21)) = k3_xboole_0(k5_xboole_0(A_387,k1_tarski(A_21)),k2_tarski(A_21,A_21)) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_14513])).

tff(c_47702,plain,(
    ! [A_672,A_673] : k5_xboole_0(k3_xboole_0(A_672,k1_tarski(A_673)),k1_tarski(A_673)) = k3_xboole_0(k1_tarski(A_673),k5_xboole_0(A_672,k1_tarski(A_673))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_38,c_14608])).

tff(c_47887,plain,(
    ! [A_49,B_50] :
      ( k3_xboole_0(k1_tarski(A_49),k5_xboole_0(B_50,k1_tarski(A_49))) = k5_xboole_0(k1_tarski(A_49),k1_tarski(A_49))
      | ~ r2_hidden(A_49,B_50) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_47702])).

tff(c_47942,plain,(
    ! [A_674,B_675] :
      ( k3_xboole_0(k1_tarski(A_674),k5_xboole_0(B_675,k1_tarski(A_674))) = k1_xboole_0
      | ~ r2_hidden(A_674,B_675) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_236,c_47887])).

tff(c_451,plain,(
    ! [A_104,B_105] : k5_xboole_0(k5_xboole_0(A_104,B_105),k3_xboole_0(A_104,B_105)) = k2_xboole_0(A_104,B_105) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_490,plain,(
    ! [A_1,B_2] : k5_xboole_0(k5_xboole_0(A_1,B_2),k3_xboole_0(B_2,A_1)) = k2_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_451])).

tff(c_48052,plain,(
    ! [B_675,A_674] :
      ( k5_xboole_0(k5_xboole_0(k5_xboole_0(B_675,k1_tarski(A_674)),k1_tarski(A_674)),k1_xboole_0) = k2_xboole_0(k5_xboole_0(B_675,k1_tarski(A_674)),k1_tarski(A_674))
      | ~ r2_hidden(A_674,B_675) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_47942,c_490])).

tff(c_48238,plain,(
    ! [B_678,A_679] :
      ( k2_xboole_0(k5_xboole_0(B_678,k1_tarski(A_679)),k1_tarski(A_679)) = B_678
      | ~ r2_hidden(A_679,B_678) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_236,c_10,c_8,c_48052])).

tff(c_48320,plain,(
    ! [A_298,A_53] :
      ( k2_xboole_0(k1_tarski(A_298),k1_tarski(A_53)) = k2_tarski(A_298,A_53)
      | ~ r2_hidden(A_53,k2_tarski(A_298,A_53))
      | A_53 = A_298 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8303,c_48238])).

tff(c_48366,plain,(
    ! [A_680,A_681] :
      ( k2_xboole_0(k1_tarski(A_680),k1_tarski(A_681)) = k2_tarski(A_680,A_681)
      | A_681 = A_680 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_48320])).

tff(c_54,plain,(
    ! [A_51,B_52] : k3_tarski(k2_tarski(A_51,B_52)) = k2_xboole_0(A_51,B_52) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_62,plain,(
    k3_tarski(k2_tarski(k1_tarski('#skF_3'),k1_tarski('#skF_4'))) != k2_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_63,plain,(
    k2_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) != k2_tarski('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_62])).

tff(c_48454,plain,(
    '#skF_3' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_48366,c_63])).

tff(c_289,plain,(
    ! [B_96,A_97] :
      ( k3_xboole_0(B_96,k1_tarski(A_97)) = k1_tarski(A_97)
      | ~ r2_hidden(A_97,B_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_229,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k3_xboole_0(B_2,A_1)) = k4_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_214])).

tff(c_295,plain,(
    ! [A_97,B_96] :
      ( k5_xboole_0(k1_tarski(A_97),k1_tarski(A_97)) = k4_xboole_0(k1_tarski(A_97),B_96)
      | ~ r2_hidden(A_97,B_96) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_289,c_229])).

tff(c_324,plain,(
    ! [A_97,B_96] :
      ( k4_xboole_0(k1_tarski(A_97),B_96) = k1_xboole_0
      | ~ r2_hidden(A_97,B_96) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_236,c_295])).

tff(c_12,plain,(
    ! [A_12,B_13] : k5_xboole_0(k5_xboole_0(A_12,B_13),k3_xboole_0(A_12,B_13)) = k2_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_584,plain,(
    ! [A_108,B_109] : k5_xboole_0(A_108,k5_xboole_0(B_109,k3_xboole_0(A_108,B_109))) = k2_xboole_0(A_108,B_109) ),
    inference(superposition,[status(thm),theory(equality)],[c_567,c_12])).

tff(c_653,plain,(
    ! [A_111,B_112] : k5_xboole_0(A_111,k4_xboole_0(B_112,A_111)) = k2_xboole_0(A_111,B_112) ),
    inference(demodulation,[status(thm),theory(equality)],[c_229,c_584])).

tff(c_679,plain,(
    ! [B_96,A_97] :
      ( k2_xboole_0(B_96,k1_tarski(A_97)) = k5_xboole_0(B_96,k1_xboole_0)
      | ~ r2_hidden(A_97,B_96) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_324,c_653])).

tff(c_1001,plain,(
    ! [B_132,A_133] :
      ( k2_xboole_0(B_132,k1_tarski(A_133)) = B_132
      | ~ r2_hidden(A_133,B_132) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_679])).

tff(c_1015,plain,
    ( k2_tarski('#skF_3','#skF_4') != k1_tarski('#skF_3')
    | ~ r2_hidden('#skF_4',k1_tarski('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1001,c_63])).

tff(c_1047,plain,(
    ~ r2_hidden('#skF_4',k1_tarski('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1015])).

tff(c_48462,plain,(
    ~ r2_hidden('#skF_4',k1_tarski('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48454,c_1047])).

tff(c_48466,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_48462])).

tff(c_48468,plain,(
    r2_hidden('#skF_4',k1_tarski('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1015])).

tff(c_40,plain,(
    ! [A_22,B_23] : k1_enumset1(A_22,A_22,B_23) = k2_tarski(A_22,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_960,plain,(
    ! [E_127,C_128,B_129,A_130] :
      ( E_127 = C_128
      | E_127 = B_129
      | E_127 = A_130
      | ~ r2_hidden(E_127,k1_enumset1(A_130,B_129,C_128)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_49480,plain,(
    ! [E_757,B_758,A_759] :
      ( E_757 = B_758
      | E_757 = A_759
      | E_757 = A_759
      | ~ r2_hidden(E_757,k2_tarski(A_759,B_758)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_960])).

tff(c_49504,plain,(
    ! [E_760,A_761] :
      ( E_760 = A_761
      | E_760 = A_761
      | E_760 = A_761
      | ~ r2_hidden(E_760,k1_tarski(A_761)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_49480])).

tff(c_49521,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_48468,c_49504])).

tff(c_48467,plain,(
    k2_tarski('#skF_3','#skF_4') != k1_tarski('#skF_3') ),
    inference(splitRight,[status(thm)],[c_1015])).

tff(c_49524,plain,(
    k2_tarski('#skF_4','#skF_4') != k1_tarski('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_49521,c_49521,c_48467])).

tff(c_49529,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_49524])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:57:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 24.48/14.74  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 24.48/14.75  
% 24.48/14.75  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 24.48/14.75  %$ r2_hidden > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 24.48/14.75  
% 24.48/14.75  %Foreground sorts:
% 24.48/14.75  
% 24.48/14.75  
% 24.48/14.75  %Background operators:
% 24.48/14.75  
% 24.48/14.75  
% 24.48/14.75  %Foreground operators:
% 24.48/14.75  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 24.48/14.75  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 24.48/14.75  tff(k1_tarski, type, k1_tarski: $i > $i).
% 24.48/14.75  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 24.48/14.75  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 24.48/14.75  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 24.48/14.75  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 24.48/14.75  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 24.48/14.75  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 24.48/14.75  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 24.48/14.75  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 24.48/14.75  tff('#skF_3', type, '#skF_3': $i).
% 24.48/14.75  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 24.48/14.75  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 24.48/14.75  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 24.48/14.75  tff(k3_tarski, type, k3_tarski: $i > $i).
% 24.48/14.75  tff('#skF_4', type, '#skF_4': $i).
% 24.48/14.75  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 24.48/14.75  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 24.48/14.75  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 24.48/14.75  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 24.48/14.75  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 24.48/14.75  
% 24.48/14.77  tff(f_54, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 24.48/14.77  tff(f_56, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 24.48/14.77  tff(f_52, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 24.48/14.77  tff(f_33, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 24.48/14.77  tff(f_76, axiom, (![A, B]: (k4_xboole_0(k1_tarski(A), k2_tarski(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_zfmisc_1)).
% 24.48/14.77  tff(f_74, axiom, (![A, B]: (k3_xboole_0(k1_tarski(A), k2_tarski(A, B)) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_zfmisc_1)).
% 24.48/14.77  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 24.48/14.77  tff(f_81, axiom, (![A, B]: (~(A = B) => (k5_xboole_0(k1_tarski(A), k1_tarski(B)) = k2_tarski(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_zfmisc_1)).
% 24.48/14.77  tff(f_35, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 24.48/14.77  tff(f_70, axiom, (![A, B]: (r2_hidden(A, B) => (k3_xboole_0(B, k1_tarski(A)) = k1_tarski(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l31_zfmisc_1)).
% 24.48/14.77  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 24.48/14.77  tff(f_31, axiom, (![A, B, C]: (k5_xboole_0(k3_xboole_0(A, B), k3_xboole_0(C, B)) = k3_xboole_0(k5_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t112_xboole_1)).
% 24.48/14.77  tff(f_37, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_xboole_1)).
% 24.48/14.77  tff(f_72, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 24.48/14.77  tff(f_84, negated_conjecture, ~(![A, B]: (k3_tarski(k2_tarski(k1_tarski(A), k1_tarski(B))) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_zfmisc_1)).
% 24.48/14.77  tff(c_38, plain, (![A_21]: (k2_tarski(A_21, A_21)=k1_tarski(A_21))), inference(cnfTransformation, [status(thm)], [f_54])).
% 24.48/14.77  tff(c_118, plain, (![A_72, B_73]: (k1_enumset1(A_72, A_72, B_73)=k2_tarski(A_72, B_73))), inference(cnfTransformation, [status(thm)], [f_56])).
% 24.48/14.77  tff(c_16, plain, (![E_20, A_14, B_15]: (r2_hidden(E_20, k1_enumset1(A_14, B_15, E_20)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 24.48/14.77  tff(c_136, plain, (![B_74, A_75]: (r2_hidden(B_74, k2_tarski(A_75, B_74)))), inference(superposition, [status(thm), theory('equality')], [c_118, c_16])).
% 24.48/14.77  tff(c_139, plain, (![A_21]: (r2_hidden(A_21, k1_tarski(A_21)))), inference(superposition, [status(thm), theory('equality')], [c_38, c_136])).
% 24.48/14.77  tff(c_124, plain, (![B_73, A_72]: (r2_hidden(B_73, k2_tarski(A_72, B_73)))), inference(superposition, [status(thm), theory('equality')], [c_118, c_16])).
% 24.48/14.77  tff(c_8, plain, (![A_8]: (k5_xboole_0(A_8, k1_xboole_0)=A_8)), inference(cnfTransformation, [status(thm)], [f_33])).
% 24.48/14.77  tff(c_58, plain, (![A_55, B_56]: (k4_xboole_0(k1_tarski(A_55), k2_tarski(A_55, B_56))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_76])).
% 24.48/14.77  tff(c_56, plain, (![A_53, B_54]: (k3_xboole_0(k1_tarski(A_53), k2_tarski(A_53, B_54))=k1_tarski(A_53))), inference(cnfTransformation, [status(thm)], [f_74])).
% 24.48/14.77  tff(c_214, plain, (![A_88, B_89]: (k5_xboole_0(A_88, k3_xboole_0(A_88, B_89))=k4_xboole_0(A_88, B_89))), inference(cnfTransformation, [status(thm)], [f_29])).
% 24.48/14.77  tff(c_226, plain, (![A_53, B_54]: (k5_xboole_0(k1_tarski(A_53), k1_tarski(A_53))=k4_xboole_0(k1_tarski(A_53), k2_tarski(A_53, B_54)))), inference(superposition, [status(thm), theory('equality')], [c_56, c_214])).
% 24.48/14.77  tff(c_236, plain, (![A_53]: (k5_xboole_0(k1_tarski(A_53), k1_tarski(A_53))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_58, c_226])).
% 24.48/14.77  tff(c_60, plain, (![A_57, B_58]: (k5_xboole_0(k1_tarski(A_57), k1_tarski(B_58))=k2_tarski(A_57, B_58) | B_58=A_57)), inference(cnfTransformation, [status(thm)], [f_81])).
% 24.48/14.77  tff(c_567, plain, (![A_108, B_109, C_110]: (k5_xboole_0(k5_xboole_0(A_108, B_109), C_110)=k5_xboole_0(A_108, k5_xboole_0(B_109, C_110)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 24.48/14.77  tff(c_8140, plain, (![A_298, B_299, C_300]: (k5_xboole_0(k1_tarski(A_298), k5_xboole_0(k1_tarski(B_299), C_300))=k5_xboole_0(k2_tarski(A_298, B_299), C_300) | B_299=A_298)), inference(superposition, [status(thm), theory('equality')], [c_60, c_567])).
% 24.48/14.77  tff(c_8273, plain, (![A_298, A_53]: (k5_xboole_0(k2_tarski(A_298, A_53), k1_tarski(A_53))=k5_xboole_0(k1_tarski(A_298), k1_xboole_0) | A_53=A_298)), inference(superposition, [status(thm), theory('equality')], [c_236, c_8140])).
% 24.48/14.77  tff(c_8303, plain, (![A_298, A_53]: (k5_xboole_0(k2_tarski(A_298, A_53), k1_tarski(A_53))=k1_tarski(A_298) | A_53=A_298)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_8273])).
% 24.48/14.77  tff(c_10, plain, (![A_9, B_10, C_11]: (k5_xboole_0(k5_xboole_0(A_9, B_10), C_11)=k5_xboole_0(A_9, k5_xboole_0(B_10, C_11)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 24.48/14.77  tff(c_52, plain, (![B_50, A_49]: (k3_xboole_0(B_50, k1_tarski(A_49))=k1_tarski(A_49) | ~r2_hidden(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_70])).
% 24.48/14.77  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 24.48/14.77  tff(c_856, plain, (![A_122, B_123, C_124]: (k5_xboole_0(k3_xboole_0(A_122, B_123), k3_xboole_0(C_124, B_123))=k3_xboole_0(k5_xboole_0(A_122, C_124), B_123))), inference(cnfTransformation, [status(thm)], [f_31])).
% 24.48/14.77  tff(c_14513, plain, (![A_387, A_388, B_389]: (k5_xboole_0(k3_xboole_0(A_387, k2_tarski(A_388, B_389)), k1_tarski(A_388))=k3_xboole_0(k5_xboole_0(A_387, k1_tarski(A_388)), k2_tarski(A_388, B_389)))), inference(superposition, [status(thm), theory('equality')], [c_56, c_856])).
% 24.48/14.77  tff(c_14608, plain, (![A_387, A_21]: (k5_xboole_0(k3_xboole_0(A_387, k1_tarski(A_21)), k1_tarski(A_21))=k3_xboole_0(k5_xboole_0(A_387, k1_tarski(A_21)), k2_tarski(A_21, A_21)))), inference(superposition, [status(thm), theory('equality')], [c_38, c_14513])).
% 24.48/14.77  tff(c_47702, plain, (![A_672, A_673]: (k5_xboole_0(k3_xboole_0(A_672, k1_tarski(A_673)), k1_tarski(A_673))=k3_xboole_0(k1_tarski(A_673), k5_xboole_0(A_672, k1_tarski(A_673))))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_38, c_14608])).
% 24.48/14.77  tff(c_47887, plain, (![A_49, B_50]: (k3_xboole_0(k1_tarski(A_49), k5_xboole_0(B_50, k1_tarski(A_49)))=k5_xboole_0(k1_tarski(A_49), k1_tarski(A_49)) | ~r2_hidden(A_49, B_50))), inference(superposition, [status(thm), theory('equality')], [c_52, c_47702])).
% 24.48/14.77  tff(c_47942, plain, (![A_674, B_675]: (k3_xboole_0(k1_tarski(A_674), k5_xboole_0(B_675, k1_tarski(A_674)))=k1_xboole_0 | ~r2_hidden(A_674, B_675))), inference(demodulation, [status(thm), theory('equality')], [c_236, c_47887])).
% 24.48/14.77  tff(c_451, plain, (![A_104, B_105]: (k5_xboole_0(k5_xboole_0(A_104, B_105), k3_xboole_0(A_104, B_105))=k2_xboole_0(A_104, B_105))), inference(cnfTransformation, [status(thm)], [f_37])).
% 24.48/14.77  tff(c_490, plain, (![A_1, B_2]: (k5_xboole_0(k5_xboole_0(A_1, B_2), k3_xboole_0(B_2, A_1))=k2_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_451])).
% 24.48/14.77  tff(c_48052, plain, (![B_675, A_674]: (k5_xboole_0(k5_xboole_0(k5_xboole_0(B_675, k1_tarski(A_674)), k1_tarski(A_674)), k1_xboole_0)=k2_xboole_0(k5_xboole_0(B_675, k1_tarski(A_674)), k1_tarski(A_674)) | ~r2_hidden(A_674, B_675))), inference(superposition, [status(thm), theory('equality')], [c_47942, c_490])).
% 24.48/14.77  tff(c_48238, plain, (![B_678, A_679]: (k2_xboole_0(k5_xboole_0(B_678, k1_tarski(A_679)), k1_tarski(A_679))=B_678 | ~r2_hidden(A_679, B_678))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_236, c_10, c_8, c_48052])).
% 24.48/14.77  tff(c_48320, plain, (![A_298, A_53]: (k2_xboole_0(k1_tarski(A_298), k1_tarski(A_53))=k2_tarski(A_298, A_53) | ~r2_hidden(A_53, k2_tarski(A_298, A_53)) | A_53=A_298)), inference(superposition, [status(thm), theory('equality')], [c_8303, c_48238])).
% 24.48/14.77  tff(c_48366, plain, (![A_680, A_681]: (k2_xboole_0(k1_tarski(A_680), k1_tarski(A_681))=k2_tarski(A_680, A_681) | A_681=A_680)), inference(demodulation, [status(thm), theory('equality')], [c_124, c_48320])).
% 24.48/14.77  tff(c_54, plain, (![A_51, B_52]: (k3_tarski(k2_tarski(A_51, B_52))=k2_xboole_0(A_51, B_52))), inference(cnfTransformation, [status(thm)], [f_72])).
% 24.48/14.77  tff(c_62, plain, (k3_tarski(k2_tarski(k1_tarski('#skF_3'), k1_tarski('#skF_4')))!=k2_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_84])).
% 24.48/14.77  tff(c_63, plain, (k2_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))!=k2_tarski('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_62])).
% 24.48/14.77  tff(c_48454, plain, ('#skF_3'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_48366, c_63])).
% 24.48/14.77  tff(c_289, plain, (![B_96, A_97]: (k3_xboole_0(B_96, k1_tarski(A_97))=k1_tarski(A_97) | ~r2_hidden(A_97, B_96))), inference(cnfTransformation, [status(thm)], [f_70])).
% 24.48/14.77  tff(c_229, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k3_xboole_0(B_2, A_1))=k4_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_214])).
% 24.48/14.77  tff(c_295, plain, (![A_97, B_96]: (k5_xboole_0(k1_tarski(A_97), k1_tarski(A_97))=k4_xboole_0(k1_tarski(A_97), B_96) | ~r2_hidden(A_97, B_96))), inference(superposition, [status(thm), theory('equality')], [c_289, c_229])).
% 24.48/14.77  tff(c_324, plain, (![A_97, B_96]: (k4_xboole_0(k1_tarski(A_97), B_96)=k1_xboole_0 | ~r2_hidden(A_97, B_96))), inference(demodulation, [status(thm), theory('equality')], [c_236, c_295])).
% 24.48/14.77  tff(c_12, plain, (![A_12, B_13]: (k5_xboole_0(k5_xboole_0(A_12, B_13), k3_xboole_0(A_12, B_13))=k2_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_37])).
% 24.48/14.77  tff(c_584, plain, (![A_108, B_109]: (k5_xboole_0(A_108, k5_xboole_0(B_109, k3_xboole_0(A_108, B_109)))=k2_xboole_0(A_108, B_109))), inference(superposition, [status(thm), theory('equality')], [c_567, c_12])).
% 24.48/14.77  tff(c_653, plain, (![A_111, B_112]: (k5_xboole_0(A_111, k4_xboole_0(B_112, A_111))=k2_xboole_0(A_111, B_112))), inference(demodulation, [status(thm), theory('equality')], [c_229, c_584])).
% 24.48/14.77  tff(c_679, plain, (![B_96, A_97]: (k2_xboole_0(B_96, k1_tarski(A_97))=k5_xboole_0(B_96, k1_xboole_0) | ~r2_hidden(A_97, B_96))), inference(superposition, [status(thm), theory('equality')], [c_324, c_653])).
% 24.48/14.77  tff(c_1001, plain, (![B_132, A_133]: (k2_xboole_0(B_132, k1_tarski(A_133))=B_132 | ~r2_hidden(A_133, B_132))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_679])).
% 24.48/14.77  tff(c_1015, plain, (k2_tarski('#skF_3', '#skF_4')!=k1_tarski('#skF_3') | ~r2_hidden('#skF_4', k1_tarski('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1001, c_63])).
% 24.48/14.77  tff(c_1047, plain, (~r2_hidden('#skF_4', k1_tarski('#skF_3'))), inference(splitLeft, [status(thm)], [c_1015])).
% 24.48/14.77  tff(c_48462, plain, (~r2_hidden('#skF_4', k1_tarski('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_48454, c_1047])).
% 24.48/14.77  tff(c_48466, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_139, c_48462])).
% 24.48/14.77  tff(c_48468, plain, (r2_hidden('#skF_4', k1_tarski('#skF_3'))), inference(splitRight, [status(thm)], [c_1015])).
% 24.48/14.77  tff(c_40, plain, (![A_22, B_23]: (k1_enumset1(A_22, A_22, B_23)=k2_tarski(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_56])).
% 24.48/14.77  tff(c_960, plain, (![E_127, C_128, B_129, A_130]: (E_127=C_128 | E_127=B_129 | E_127=A_130 | ~r2_hidden(E_127, k1_enumset1(A_130, B_129, C_128)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 24.48/14.77  tff(c_49480, plain, (![E_757, B_758, A_759]: (E_757=B_758 | E_757=A_759 | E_757=A_759 | ~r2_hidden(E_757, k2_tarski(A_759, B_758)))), inference(superposition, [status(thm), theory('equality')], [c_40, c_960])).
% 24.48/14.77  tff(c_49504, plain, (![E_760, A_761]: (E_760=A_761 | E_760=A_761 | E_760=A_761 | ~r2_hidden(E_760, k1_tarski(A_761)))), inference(superposition, [status(thm), theory('equality')], [c_38, c_49480])).
% 24.48/14.77  tff(c_49521, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_48468, c_49504])).
% 24.48/14.77  tff(c_48467, plain, (k2_tarski('#skF_3', '#skF_4')!=k1_tarski('#skF_3')), inference(splitRight, [status(thm)], [c_1015])).
% 24.48/14.77  tff(c_49524, plain, (k2_tarski('#skF_4', '#skF_4')!=k1_tarski('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_49521, c_49521, c_48467])).
% 24.48/14.77  tff(c_49529, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_49524])).
% 24.48/14.77  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 24.48/14.77  
% 24.48/14.77  Inference rules
% 24.48/14.77  ----------------------
% 24.48/14.77  #Ref     : 0
% 24.48/14.77  #Sup     : 12157
% 24.48/14.77  #Fact    : 6
% 24.48/14.77  #Define  : 0
% 24.48/14.77  #Split   : 2
% 24.48/14.77  #Chain   : 0
% 24.48/14.77  #Close   : 0
% 24.48/14.77  
% 24.48/14.77  Ordering : KBO
% 24.48/14.77  
% 24.48/14.77  Simplification rules
% 24.48/14.77  ----------------------
% 24.48/14.77  #Subsume      : 1335
% 24.48/14.77  #Demod        : 17343
% 24.48/14.77  #Tautology    : 4239
% 24.48/14.77  #SimpNegUnit  : 0
% 24.48/14.77  #BackRed      : 17
% 24.48/14.77  
% 24.48/14.77  #Partial instantiations: 0
% 24.48/14.77  #Strategies tried      : 1
% 24.48/14.77  
% 24.48/14.77  Timing (in seconds)
% 24.48/14.77  ----------------------
% 24.48/14.77  Preprocessing        : 0.54
% 24.48/14.77  Parsing              : 0.27
% 24.48/14.77  CNF conversion       : 0.04
% 24.48/14.77  Main loop            : 13.31
% 24.48/14.77  Inferencing          : 1.99
% 24.48/14.77  Reduction            : 8.44
% 24.48/14.77  Demodulation         : 7.75
% 24.48/14.77  BG Simplification    : 0.33
% 24.48/14.77  Subsumption          : 2.05
% 24.48/14.77  Abstraction          : 0.57
% 24.48/14.77  MUC search           : 0.00
% 24.48/14.77  Cooper               : 0.00
% 24.48/14.77  Total                : 13.90
% 24.48/14.77  Index Insertion      : 0.00
% 24.48/14.77  Index Deletion       : 0.00
% 24.48/14.77  Index Matching       : 0.00
% 24.48/14.77  BG Taut test         : 0.00
%------------------------------------------------------------------------------
