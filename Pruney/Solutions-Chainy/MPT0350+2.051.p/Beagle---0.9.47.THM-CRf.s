%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:32 EST 2020

% Result     : Theorem 13.28s
% Output     : CNFRefutation 13.28s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 129 expanded)
%              Number of leaves         :   48 (  63 expanded)
%              Depth                    :   11
%              Number of atoms          :  101 ( 140 expanded)
%              Number of equality atoms :   54 (  76 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_91,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_113,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k4_subset_1(A,B,k3_subset_1(A,B)) = k2_subset_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_subset_1)).

tff(f_95,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_102,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_89,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_49,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_55,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_53,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k4_xboole_0(k2_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l98_xboole_1)).

tff(f_99,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_108,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(c_64,plain,(
    ! [A_63] : k2_subset_1(A_63) = A_63 ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_74,plain,(
    k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3','#skF_4')) != k2_subset_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_77,plain,(
    k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3','#skF_4')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_74])).

tff(c_76,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_2058,plain,(
    ! [A_172,B_173] :
      ( k4_xboole_0(A_172,B_173) = k3_subset_1(A_172,B_173)
      | ~ m1_subset_1(B_173,k1_zfmisc_1(A_172)) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_2075,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_76,c_2058])).

tff(c_70,plain,(
    ! [A_68] : ~ v1_xboole_0(k1_zfmisc_1(A_68)) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_677,plain,(
    ! [B_126,A_127] :
      ( r2_hidden(B_126,A_127)
      | ~ m1_subset_1(B_126,A_127)
      | v1_xboole_0(A_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_42,plain,(
    ! [C_58,A_54] :
      ( r1_tarski(C_58,A_54)
      | ~ r2_hidden(C_58,k1_zfmisc_1(A_54)) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_684,plain,(
    ! [B_126,A_54] :
      ( r1_tarski(B_126,A_54)
      | ~ m1_subset_1(B_126,k1_zfmisc_1(A_54))
      | v1_xboole_0(k1_zfmisc_1(A_54)) ) ),
    inference(resolution,[status(thm)],[c_677,c_42])).

tff(c_814,plain,(
    ! [B_140,A_141] :
      ( r1_tarski(B_140,A_141)
      | ~ m1_subset_1(B_140,k1_zfmisc_1(A_141)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_684])).

tff(c_827,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_76,c_814])).

tff(c_20,plain,(
    ! [A_18,B_19] :
      ( k3_xboole_0(A_18,B_19) = A_18
      | ~ r1_tarski(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_831,plain,(
    k3_xboole_0('#skF_4','#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_827,c_20])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_528,plain,(
    ! [A_118,B_119] : k5_xboole_0(A_118,k3_xboole_0(A_118,B_119)) = k4_xboole_0(A_118,B_119) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_872,plain,(
    ! [B_142,A_143] : k5_xboole_0(B_142,k3_xboole_0(A_143,B_142)) = k4_xboole_0(B_142,A_143) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_528])).

tff(c_889,plain,(
    k5_xboole_0('#skF_3','#skF_4') = k4_xboole_0('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_831,c_872])).

tff(c_4,plain,(
    ! [B_4,A_3] : k5_xboole_0(B_4,A_3) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_182,plain,(
    ! [B_89,A_90] : k5_xboole_0(B_89,A_90) = k5_xboole_0(A_90,B_89) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_22,plain,(
    ! [A_20] : k5_xboole_0(A_20,k1_xboole_0) = A_20 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_198,plain,(
    ! [A_90] : k5_xboole_0(k1_xboole_0,A_90) = A_90 ),
    inference(superposition,[status(thm),theory(equality)],[c_182,c_22])).

tff(c_28,plain,(
    ! [A_26] : k5_xboole_0(A_26,A_26) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1493,plain,(
    ! [A_160,B_161,C_162] : k5_xboole_0(k5_xboole_0(A_160,B_161),C_162) = k5_xboole_0(A_160,k5_xboole_0(B_161,C_162)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1574,plain,(
    ! [A_26,C_162] : k5_xboole_0(A_26,k5_xboole_0(A_26,C_162)) = k5_xboole_0(k1_xboole_0,C_162) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_1493])).

tff(c_1590,plain,(
    ! [A_163,C_164] : k5_xboole_0(A_163,k5_xboole_0(A_163,C_164)) = C_164 ),
    inference(demodulation,[status(thm),theory(equality)],[c_198,c_1574])).

tff(c_1740,plain,(
    ! [A_166,B_167] : k5_xboole_0(A_166,k5_xboole_0(B_167,A_166)) = B_167 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_1590])).

tff(c_1790,plain,(
    k5_xboole_0('#skF_4',k4_xboole_0('#skF_3','#skF_4')) = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_889,c_1740])).

tff(c_2607,plain,(
    k5_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2075,c_1790])).

tff(c_24,plain,(
    ! [A_21,B_22] : r1_xboole_0(k4_xboole_0(A_21,B_22),B_22) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_323,plain,(
    ! [A_97,B_98] :
      ( k3_xboole_0(A_97,B_98) = k1_xboole_0
      | ~ r1_xboole_0(A_97,B_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_328,plain,(
    ! [A_99,B_100] : k3_xboole_0(k4_xboole_0(A_99,B_100),B_100) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_24,c_323])).

tff(c_129,plain,(
    ! [B_83,A_84] : k3_xboole_0(B_83,A_84) = k3_xboole_0(A_84,B_83) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_16,plain,(
    ! [A_14,B_15] : r1_tarski(k3_xboole_0(A_14,B_15),A_14) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_144,plain,(
    ! [B_83,A_84] : r1_tarski(k3_xboole_0(B_83,A_84),A_84) ),
    inference(superposition,[status(thm),theory(equality)],[c_129,c_16])).

tff(c_355,plain,(
    ! [B_101] : r1_tarski(k1_xboole_0,B_101) ),
    inference(superposition,[status(thm),theory(equality)],[c_328,c_144])).

tff(c_369,plain,(
    ! [B_104] : k3_xboole_0(k1_xboole_0,B_104) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_355,c_20])).

tff(c_381,plain,(
    ! [B_104] : k3_xboole_0(B_104,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_369,c_2])).

tff(c_544,plain,(
    ! [B_104] : k5_xboole_0(B_104,k1_xboole_0) = k4_xboole_0(B_104,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_381,c_528])).

tff(c_571,plain,(
    ! [B_104] : k4_xboole_0(B_104,k1_xboole_0) = B_104 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_544])).

tff(c_327,plain,(
    ! [A_21,B_22] : k3_xboole_0(k4_xboole_0(A_21,B_22),B_22) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_24,c_323])).

tff(c_2090,plain,(
    k3_xboole_0(k3_subset_1('#skF_3','#skF_4'),'#skF_4') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2075,c_327])).

tff(c_2229,plain,(
    ! [A_174,B_175] : k4_xboole_0(k2_xboole_0(A_174,B_175),k3_xboole_0(A_174,B_175)) = k5_xboole_0(A_174,B_175) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_7734,plain,(
    ! [A_295,B_296] : k4_xboole_0(k2_xboole_0(A_295,B_296),k3_xboole_0(B_296,A_295)) = k5_xboole_0(A_295,B_296) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_2229])).

tff(c_7817,plain,(
    k4_xboole_0(k2_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')),k1_xboole_0) = k5_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2090,c_7734])).

tff(c_7874,plain,(
    k2_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2607,c_571,c_7817])).

tff(c_68,plain,(
    ! [A_66,B_67] :
      ( m1_subset_1(k3_subset_1(A_66,B_67),k1_zfmisc_1(A_66))
      | ~ m1_subset_1(B_67,k1_zfmisc_1(A_66)) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_3628,plain,(
    ! [A_214,B_215,C_216] :
      ( k4_subset_1(A_214,B_215,C_216) = k2_xboole_0(B_215,C_216)
      | ~ m1_subset_1(C_216,k1_zfmisc_1(A_214))
      | ~ m1_subset_1(B_215,k1_zfmisc_1(A_214)) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_41894,plain,(
    ! [A_535,B_536,B_537] :
      ( k4_subset_1(A_535,B_536,k3_subset_1(A_535,B_537)) = k2_xboole_0(B_536,k3_subset_1(A_535,B_537))
      | ~ m1_subset_1(B_536,k1_zfmisc_1(A_535))
      | ~ m1_subset_1(B_537,k1_zfmisc_1(A_535)) ) ),
    inference(resolution,[status(thm)],[c_68,c_3628])).

tff(c_42271,plain,(
    ! [B_541] :
      ( k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3',B_541)) = k2_xboole_0('#skF_4',k3_subset_1('#skF_3',B_541))
      | ~ m1_subset_1(B_541,k1_zfmisc_1('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_76,c_41894])).

tff(c_42290,plain,(
    k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3','#skF_4')) = k2_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_76,c_42271])).

tff(c_42298,plain,(
    k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3','#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7874,c_42290])).

tff(c_42300,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_77,c_42298])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:50:57 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 13.28/6.84  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.28/6.85  
% 13.28/6.85  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.28/6.85  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 13.28/6.85  
% 13.28/6.85  %Foreground sorts:
% 13.28/6.85  
% 13.28/6.85  
% 13.28/6.85  %Background operators:
% 13.28/6.85  
% 13.28/6.85  
% 13.28/6.85  %Foreground operators:
% 13.28/6.85  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 13.28/6.85  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 13.28/6.85  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 13.28/6.85  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 13.28/6.85  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 13.28/6.85  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 13.28/6.85  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 13.28/6.85  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 13.28/6.85  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 13.28/6.85  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 13.28/6.85  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 13.28/6.85  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 13.28/6.85  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 13.28/6.85  tff('#skF_3', type, '#skF_3': $i).
% 13.28/6.85  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 13.28/6.85  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 13.28/6.85  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 13.28/6.85  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 13.28/6.85  tff(k3_tarski, type, k3_tarski: $i > $i).
% 13.28/6.85  tff('#skF_4', type, '#skF_4': $i).
% 13.28/6.85  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 13.28/6.85  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 13.28/6.85  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 13.28/6.85  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 13.28/6.85  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 13.28/6.85  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 13.28/6.85  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 13.28/6.85  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 13.28/6.85  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 13.28/6.85  
% 13.28/6.87  tff(f_91, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 13.28/6.87  tff(f_113, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k4_subset_1(A, B, k3_subset_1(A, B)) = k2_subset_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_subset_1)).
% 13.28/6.87  tff(f_95, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 13.28/6.87  tff(f_102, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 13.28/6.87  tff(f_89, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 13.28/6.87  tff(f_74, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 13.28/6.87  tff(f_47, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 13.28/6.87  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 13.28/6.87  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 13.28/6.87  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 13.28/6.87  tff(f_49, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 13.28/6.87  tff(f_55, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 13.28/6.87  tff(f_53, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 13.28/6.87  tff(f_51, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 13.28/6.87  tff(f_33, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 13.28/6.87  tff(f_41, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 13.28/6.87  tff(f_35, axiom, (![A, B]: (k5_xboole_0(A, B) = k4_xboole_0(k2_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l98_xboole_1)).
% 13.28/6.87  tff(f_99, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 13.28/6.87  tff(f_108, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 13.28/6.87  tff(c_64, plain, (![A_63]: (k2_subset_1(A_63)=A_63)), inference(cnfTransformation, [status(thm)], [f_91])).
% 13.28/6.87  tff(c_74, plain, (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', '#skF_4'))!=k2_subset_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_113])).
% 13.28/6.87  tff(c_77, plain, (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', '#skF_4'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_74])).
% 13.28/6.87  tff(c_76, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_113])).
% 13.28/6.87  tff(c_2058, plain, (![A_172, B_173]: (k4_xboole_0(A_172, B_173)=k3_subset_1(A_172, B_173) | ~m1_subset_1(B_173, k1_zfmisc_1(A_172)))), inference(cnfTransformation, [status(thm)], [f_95])).
% 13.28/6.87  tff(c_2075, plain, (k4_xboole_0('#skF_3', '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_76, c_2058])).
% 13.28/6.87  tff(c_70, plain, (![A_68]: (~v1_xboole_0(k1_zfmisc_1(A_68)))), inference(cnfTransformation, [status(thm)], [f_102])).
% 13.28/6.87  tff(c_677, plain, (![B_126, A_127]: (r2_hidden(B_126, A_127) | ~m1_subset_1(B_126, A_127) | v1_xboole_0(A_127))), inference(cnfTransformation, [status(thm)], [f_89])).
% 13.28/6.87  tff(c_42, plain, (![C_58, A_54]: (r1_tarski(C_58, A_54) | ~r2_hidden(C_58, k1_zfmisc_1(A_54)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 13.28/6.87  tff(c_684, plain, (![B_126, A_54]: (r1_tarski(B_126, A_54) | ~m1_subset_1(B_126, k1_zfmisc_1(A_54)) | v1_xboole_0(k1_zfmisc_1(A_54)))), inference(resolution, [status(thm)], [c_677, c_42])).
% 13.28/6.87  tff(c_814, plain, (![B_140, A_141]: (r1_tarski(B_140, A_141) | ~m1_subset_1(B_140, k1_zfmisc_1(A_141)))), inference(negUnitSimplification, [status(thm)], [c_70, c_684])).
% 13.28/6.87  tff(c_827, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_76, c_814])).
% 13.28/6.87  tff(c_20, plain, (![A_18, B_19]: (k3_xboole_0(A_18, B_19)=A_18 | ~r1_tarski(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_47])).
% 13.28/6.87  tff(c_831, plain, (k3_xboole_0('#skF_4', '#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_827, c_20])).
% 13.28/6.87  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 13.28/6.87  tff(c_528, plain, (![A_118, B_119]: (k5_xboole_0(A_118, k3_xboole_0(A_118, B_119))=k4_xboole_0(A_118, B_119))), inference(cnfTransformation, [status(thm)], [f_37])).
% 13.28/6.87  tff(c_872, plain, (![B_142, A_143]: (k5_xboole_0(B_142, k3_xboole_0(A_143, B_142))=k4_xboole_0(B_142, A_143))), inference(superposition, [status(thm), theory('equality')], [c_2, c_528])).
% 13.28/6.87  tff(c_889, plain, (k5_xboole_0('#skF_3', '#skF_4')=k4_xboole_0('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_831, c_872])).
% 13.28/6.87  tff(c_4, plain, (![B_4, A_3]: (k5_xboole_0(B_4, A_3)=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 13.28/6.87  tff(c_182, plain, (![B_89, A_90]: (k5_xboole_0(B_89, A_90)=k5_xboole_0(A_90, B_89))), inference(cnfTransformation, [status(thm)], [f_29])).
% 13.28/6.87  tff(c_22, plain, (![A_20]: (k5_xboole_0(A_20, k1_xboole_0)=A_20)), inference(cnfTransformation, [status(thm)], [f_49])).
% 13.28/6.87  tff(c_198, plain, (![A_90]: (k5_xboole_0(k1_xboole_0, A_90)=A_90)), inference(superposition, [status(thm), theory('equality')], [c_182, c_22])).
% 13.28/6.87  tff(c_28, plain, (![A_26]: (k5_xboole_0(A_26, A_26)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_55])).
% 13.28/6.87  tff(c_1493, plain, (![A_160, B_161, C_162]: (k5_xboole_0(k5_xboole_0(A_160, B_161), C_162)=k5_xboole_0(A_160, k5_xboole_0(B_161, C_162)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 13.28/6.87  tff(c_1574, plain, (![A_26, C_162]: (k5_xboole_0(A_26, k5_xboole_0(A_26, C_162))=k5_xboole_0(k1_xboole_0, C_162))), inference(superposition, [status(thm), theory('equality')], [c_28, c_1493])).
% 13.28/6.87  tff(c_1590, plain, (![A_163, C_164]: (k5_xboole_0(A_163, k5_xboole_0(A_163, C_164))=C_164)), inference(demodulation, [status(thm), theory('equality')], [c_198, c_1574])).
% 13.28/6.87  tff(c_1740, plain, (![A_166, B_167]: (k5_xboole_0(A_166, k5_xboole_0(B_167, A_166))=B_167)), inference(superposition, [status(thm), theory('equality')], [c_4, c_1590])).
% 13.28/6.87  tff(c_1790, plain, (k5_xboole_0('#skF_4', k4_xboole_0('#skF_3', '#skF_4'))='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_889, c_1740])).
% 13.28/6.87  tff(c_2607, plain, (k5_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2075, c_1790])).
% 13.28/6.87  tff(c_24, plain, (![A_21, B_22]: (r1_xboole_0(k4_xboole_0(A_21, B_22), B_22))), inference(cnfTransformation, [status(thm)], [f_51])).
% 13.28/6.87  tff(c_323, plain, (![A_97, B_98]: (k3_xboole_0(A_97, B_98)=k1_xboole_0 | ~r1_xboole_0(A_97, B_98))), inference(cnfTransformation, [status(thm)], [f_33])).
% 13.28/6.87  tff(c_328, plain, (![A_99, B_100]: (k3_xboole_0(k4_xboole_0(A_99, B_100), B_100)=k1_xboole_0)), inference(resolution, [status(thm)], [c_24, c_323])).
% 13.28/6.87  tff(c_129, plain, (![B_83, A_84]: (k3_xboole_0(B_83, A_84)=k3_xboole_0(A_84, B_83))), inference(cnfTransformation, [status(thm)], [f_27])).
% 13.28/6.87  tff(c_16, plain, (![A_14, B_15]: (r1_tarski(k3_xboole_0(A_14, B_15), A_14))), inference(cnfTransformation, [status(thm)], [f_41])).
% 13.28/6.87  tff(c_144, plain, (![B_83, A_84]: (r1_tarski(k3_xboole_0(B_83, A_84), A_84))), inference(superposition, [status(thm), theory('equality')], [c_129, c_16])).
% 13.28/6.87  tff(c_355, plain, (![B_101]: (r1_tarski(k1_xboole_0, B_101))), inference(superposition, [status(thm), theory('equality')], [c_328, c_144])).
% 13.28/6.87  tff(c_369, plain, (![B_104]: (k3_xboole_0(k1_xboole_0, B_104)=k1_xboole_0)), inference(resolution, [status(thm)], [c_355, c_20])).
% 13.28/6.87  tff(c_381, plain, (![B_104]: (k3_xboole_0(B_104, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_369, c_2])).
% 13.28/6.87  tff(c_544, plain, (![B_104]: (k5_xboole_0(B_104, k1_xboole_0)=k4_xboole_0(B_104, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_381, c_528])).
% 13.28/6.87  tff(c_571, plain, (![B_104]: (k4_xboole_0(B_104, k1_xboole_0)=B_104)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_544])).
% 13.28/6.87  tff(c_327, plain, (![A_21, B_22]: (k3_xboole_0(k4_xboole_0(A_21, B_22), B_22)=k1_xboole_0)), inference(resolution, [status(thm)], [c_24, c_323])).
% 13.28/6.87  tff(c_2090, plain, (k3_xboole_0(k3_subset_1('#skF_3', '#skF_4'), '#skF_4')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_2075, c_327])).
% 13.28/6.87  tff(c_2229, plain, (![A_174, B_175]: (k4_xboole_0(k2_xboole_0(A_174, B_175), k3_xboole_0(A_174, B_175))=k5_xboole_0(A_174, B_175))), inference(cnfTransformation, [status(thm)], [f_35])).
% 13.28/6.87  tff(c_7734, plain, (![A_295, B_296]: (k4_xboole_0(k2_xboole_0(A_295, B_296), k3_xboole_0(B_296, A_295))=k5_xboole_0(A_295, B_296))), inference(superposition, [status(thm), theory('equality')], [c_2, c_2229])).
% 13.28/6.87  tff(c_7817, plain, (k4_xboole_0(k2_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4')), k1_xboole_0)=k5_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_2090, c_7734])).
% 13.28/6.87  tff(c_7874, plain, (k2_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2607, c_571, c_7817])).
% 13.28/6.87  tff(c_68, plain, (![A_66, B_67]: (m1_subset_1(k3_subset_1(A_66, B_67), k1_zfmisc_1(A_66)) | ~m1_subset_1(B_67, k1_zfmisc_1(A_66)))), inference(cnfTransformation, [status(thm)], [f_99])).
% 13.28/6.87  tff(c_3628, plain, (![A_214, B_215, C_216]: (k4_subset_1(A_214, B_215, C_216)=k2_xboole_0(B_215, C_216) | ~m1_subset_1(C_216, k1_zfmisc_1(A_214)) | ~m1_subset_1(B_215, k1_zfmisc_1(A_214)))), inference(cnfTransformation, [status(thm)], [f_108])).
% 13.28/6.87  tff(c_41894, plain, (![A_535, B_536, B_537]: (k4_subset_1(A_535, B_536, k3_subset_1(A_535, B_537))=k2_xboole_0(B_536, k3_subset_1(A_535, B_537)) | ~m1_subset_1(B_536, k1_zfmisc_1(A_535)) | ~m1_subset_1(B_537, k1_zfmisc_1(A_535)))), inference(resolution, [status(thm)], [c_68, c_3628])).
% 13.28/6.87  tff(c_42271, plain, (![B_541]: (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', B_541))=k2_xboole_0('#skF_4', k3_subset_1('#skF_3', B_541)) | ~m1_subset_1(B_541, k1_zfmisc_1('#skF_3')))), inference(resolution, [status(thm)], [c_76, c_41894])).
% 13.28/6.87  tff(c_42290, plain, (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', '#skF_4'))=k2_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_76, c_42271])).
% 13.28/6.87  tff(c_42298, plain, (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', '#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_7874, c_42290])).
% 13.28/6.87  tff(c_42300, plain, $false, inference(negUnitSimplification, [status(thm)], [c_77, c_42298])).
% 13.28/6.87  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.28/6.87  
% 13.28/6.87  Inference rules
% 13.28/6.87  ----------------------
% 13.28/6.87  #Ref     : 0
% 13.28/6.87  #Sup     : 10502
% 13.28/6.87  #Fact    : 0
% 13.28/6.87  #Define  : 0
% 13.28/6.87  #Split   : 0
% 13.28/6.87  #Chain   : 0
% 13.28/6.87  #Close   : 0
% 13.28/6.87  
% 13.28/6.87  Ordering : KBO
% 13.28/6.87  
% 13.28/6.87  Simplification rules
% 13.28/6.87  ----------------------
% 13.28/6.87  #Subsume      : 161
% 13.28/6.87  #Demod        : 14135
% 13.28/6.87  #Tautology    : 6904
% 13.28/6.87  #SimpNegUnit  : 14
% 13.28/6.87  #BackRed      : 9
% 13.28/6.87  
% 13.28/6.87  #Partial instantiations: 0
% 13.28/6.87  #Strategies tried      : 1
% 13.28/6.87  
% 13.28/6.87  Timing (in seconds)
% 13.28/6.87  ----------------------
% 13.28/6.87  Preprocessing        : 0.36
% 13.28/6.87  Parsing              : 0.18
% 13.28/6.87  CNF conversion       : 0.02
% 13.28/6.87  Main loop            : 5.74
% 13.28/6.87  Inferencing          : 0.84
% 13.28/6.87  Reduction            : 3.65
% 13.28/6.87  Demodulation         : 3.31
% 13.28/6.87  BG Simplification    : 0.11
% 13.28/6.87  Subsumption          : 0.92
% 13.28/6.87  Abstraction          : 0.17
% 13.28/6.87  MUC search           : 0.00
% 13.28/6.87  Cooper               : 0.00
% 13.28/6.87  Total                : 6.13
% 13.28/6.87  Index Insertion      : 0.00
% 13.28/6.87  Index Deletion       : 0.00
% 13.28/6.87  Index Matching       : 0.00
% 13.28/6.87  BG Taut test         : 0.00
%------------------------------------------------------------------------------
