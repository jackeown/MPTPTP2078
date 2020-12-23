%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:39 EST 2020

% Result     : Theorem 4.20s
% Output     : CNFRefutation 4.63s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 942 expanded)
%              Number of leaves         :   44 ( 320 expanded)
%              Depth                    :   15
%              Number of atoms          :  195 (1962 expanded)
%              Number of equality atoms :   75 ( 493 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k5_relset_1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k5_relset_1,type,(
    k5_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_144,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A)))
       => ( r1_tarski(B,C)
         => r2_relset_1(B,A,k5_relset_1(B,A,D,C),D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_relset_1)).

tff(f_127,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_67,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_65,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_51,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k2_xboole_0(k1_tarski(A),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_zfmisc_1)).

tff(f_54,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_115,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_91,axiom,(
    ! [A,B] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & ~ ( k1_relat_1(k2_zfmisc_1(A,B)) = A
            & k2_relat_1(k2_zfmisc_1(A,B)) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t195_relat_1)).

tff(f_102,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).

tff(f_137,axiom,(
    ! [A,B] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A,B))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relset_1)).

tff(f_79,axiom,(
    ! [A] : k7_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t111_relat_1)).

tff(f_37,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_47,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_119,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k5_relset_1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k5_relset_1)).

tff(f_108,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t102_relat_1)).

tff(f_41,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_boole)).

tff(c_62,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_380,plain,(
    ! [A_100,B_101,D_102] :
      ( r2_relset_1(A_100,B_101,D_102,D_102)
      | ~ m1_subset_1(D_102,k1_zfmisc_1(k2_zfmisc_1(A_100,B_101))) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_394,plain,(
    r2_relset_1('#skF_3','#skF_2','#skF_5','#skF_5') ),
    inference(resolution,[status(thm)],[c_62,c_380])).

tff(c_60,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_28,plain,(
    ! [A_20,B_21] : v1_relat_1(k2_zfmisc_1(A_20,B_21)) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_189,plain,(
    ! [B_77,A_78] :
      ( v1_relat_1(B_77)
      | ~ m1_subset_1(B_77,k1_zfmisc_1(A_78))
      | ~ v1_relat_1(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_201,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_2')) ),
    inference(resolution,[status(thm)],[c_62,c_189])).

tff(c_211,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_201])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_272,plain,(
    ! [A_85,B_86] :
      ( k2_xboole_0(k1_tarski(A_85),B_86) = B_86
      | ~ r2_hidden(A_85,B_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_20,plain,(
    ! [A_13,B_14] : k2_xboole_0(k1_tarski(A_13),B_14) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_304,plain,(
    ! [B_89,A_90] :
      ( k1_xboole_0 != B_89
      | ~ r2_hidden(A_90,B_89) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_272,c_20])).

tff(c_308,plain,(
    ! [A_1] :
      ( k1_xboole_0 != A_1
      | v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_4,c_304])).

tff(c_341,plain,(
    ! [C_96,B_97,A_98] :
      ( v1_xboole_0(C_96)
      | ~ m1_subset_1(C_96,k1_zfmisc_1(k2_zfmisc_1(B_97,A_98)))
      | ~ v1_xboole_0(A_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_361,plain,
    ( v1_xboole_0('#skF_5')
    | ~ v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_62,c_341])).

tff(c_364,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_361])).

tff(c_368,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(resolution,[status(thm)],[c_308,c_364])).

tff(c_152,plain,(
    ! [A_73,B_74] :
      ( r1_tarski(A_73,B_74)
      | ~ m1_subset_1(A_73,k1_zfmisc_1(B_74)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_168,plain,(
    r1_tarski('#skF_5',k2_zfmisc_1('#skF_3','#skF_2')) ),
    inference(resolution,[status(thm)],[c_62,c_152])).

tff(c_36,plain,(
    ! [A_27,B_28] :
      ( k2_relat_1(k2_zfmisc_1(A_27,B_28)) = B_28
      | k1_xboole_0 = B_28
      | k1_xboole_0 = A_27 ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_462,plain,(
    ! [A_117,B_118] :
      ( r1_tarski(k2_relat_1(A_117),k2_relat_1(B_118))
      | ~ r1_tarski(A_117,B_118)
      | ~ v1_relat_1(B_118)
      | ~ v1_relat_1(A_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_474,plain,(
    ! [A_117,B_28,A_27] :
      ( r1_tarski(k2_relat_1(A_117),B_28)
      | ~ r1_tarski(A_117,k2_zfmisc_1(A_27,B_28))
      | ~ v1_relat_1(k2_zfmisc_1(A_27,B_28))
      | ~ v1_relat_1(A_117)
      | k1_xboole_0 = B_28
      | k1_xboole_0 = A_27 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_462])).

tff(c_807,plain,(
    ! [A_183,B_184,A_185] :
      ( r1_tarski(k2_relat_1(A_183),B_184)
      | ~ r1_tarski(A_183,k2_zfmisc_1(A_185,B_184))
      | ~ v1_relat_1(A_183)
      | k1_xboole_0 = B_184
      | k1_xboole_0 = A_185 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_474])).

tff(c_809,plain,
    ( r1_tarski(k2_relat_1('#skF_5'),'#skF_2')
    | ~ v1_relat_1('#skF_5')
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_168,c_807])).

tff(c_818,plain,
    ( r1_tarski(k2_relat_1('#skF_5'),'#skF_2')
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_211,c_809])).

tff(c_819,plain,
    ( r1_tarski(k2_relat_1('#skF_5'),'#skF_2')
    | k1_xboole_0 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_368,c_818])).

tff(c_825,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_819])).

tff(c_56,plain,(
    ! [A_50,B_51] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_50,B_51))) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_393,plain,(
    ! [A_50,B_51] : r2_relset_1(A_50,B_51,k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_56,c_380])).

tff(c_841,plain,(
    ! [A_50,B_51] : r2_relset_1(A_50,B_51,'#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_825,c_825,c_393])).

tff(c_34,plain,(
    ! [A_26] : k7_relat_1(k1_xboole_0,A_26) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_863,plain,(
    ! [A_26] : k7_relat_1('#skF_3',A_26) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_825,c_825,c_34])).

tff(c_8,plain,(
    ! [A_7] : k3_xboole_0(A_7,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_859,plain,(
    ! [A_7] : k3_xboole_0(A_7,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_825,c_825,c_8])).

tff(c_16,plain,(
    ! [B_10] : k2_zfmisc_1(k1_xboole_0,B_10) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_862,plain,(
    ! [B_10] : k2_zfmisc_1('#skF_3',B_10) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_825,c_825,c_16])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( k3_xboole_0(A_5,B_6) = A_5
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_188,plain,(
    k3_xboole_0('#skF_5',k2_zfmisc_1('#skF_3','#skF_2')) = '#skF_5' ),
    inference(resolution,[status(thm)],[c_168,c_6])).

tff(c_921,plain,(
    k3_xboole_0('#skF_5','#skF_3') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_862,c_188])).

tff(c_1074,plain,(
    '#skF_5' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_859,c_921])).

tff(c_576,plain,(
    ! [A_133,B_134,C_135,D_136] :
      ( k5_relset_1(A_133,B_134,C_135,D_136) = k7_relat_1(C_135,D_136)
      | ~ m1_subset_1(C_135,k1_zfmisc_1(k2_zfmisc_1(A_133,B_134))) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_591,plain,(
    ! [D_136] : k5_relset_1('#skF_3','#skF_2','#skF_5',D_136) = k7_relat_1('#skF_5',D_136) ),
    inference(resolution,[status(thm)],[c_62,c_576])).

tff(c_58,plain,(
    ~ r2_relset_1('#skF_3','#skF_2',k5_relset_1('#skF_3','#skF_2','#skF_5','#skF_4'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_599,plain,(
    ~ r2_relset_1('#skF_3','#skF_2',k7_relat_1('#skF_5','#skF_4'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_591,c_58])).

tff(c_1078,plain,(
    ~ r2_relset_1('#skF_3','#skF_2',k7_relat_1('#skF_3','#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1074,c_1074,c_599])).

tff(c_1085,plain,(
    ~ r2_relset_1('#skF_3','#skF_2','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_863,c_1078])).

tff(c_1149,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_841,c_1085])).

tff(c_1151,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_819])).

tff(c_38,plain,(
    ! [A_27,B_28] :
      ( k1_relat_1(k2_zfmisc_1(A_27,B_28)) = A_27
      | k1_xboole_0 = B_28
      | k1_xboole_0 = A_27 ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_402,plain,(
    ! [A_106,B_107] :
      ( r1_tarski(k1_relat_1(A_106),k1_relat_1(B_107))
      | ~ r1_tarski(A_106,B_107)
      | ~ v1_relat_1(B_107)
      | ~ v1_relat_1(A_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_417,plain,(
    ! [A_106,A_27,B_28] :
      ( r1_tarski(k1_relat_1(A_106),A_27)
      | ~ r1_tarski(A_106,k2_zfmisc_1(A_27,B_28))
      | ~ v1_relat_1(k2_zfmisc_1(A_27,B_28))
      | ~ v1_relat_1(A_106)
      | k1_xboole_0 = B_28
      | k1_xboole_0 = A_27 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_402])).

tff(c_1613,plain,(
    ! [A_1340,A_1341,B_1342] :
      ( r1_tarski(k1_relat_1(A_1340),A_1341)
      | ~ r1_tarski(A_1340,k2_zfmisc_1(A_1341,B_1342))
      | ~ v1_relat_1(A_1340)
      | k1_xboole_0 = B_1342
      | k1_xboole_0 = A_1341 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_417])).

tff(c_1618,plain,
    ( r1_tarski(k1_relat_1('#skF_5'),'#skF_3')
    | ~ v1_relat_1('#skF_5')
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_168,c_1613])).

tff(c_1630,plain,
    ( r1_tarski(k1_relat_1('#skF_5'),'#skF_3')
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_211,c_1618])).

tff(c_1631,plain,(
    r1_tarski(k1_relat_1('#skF_5'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_1151,c_368,c_1630])).

tff(c_44,plain,(
    ! [B_33,A_32] :
      ( k7_relat_1(B_33,A_32) = B_33
      | ~ r1_tarski(k1_relat_1(B_33),A_32)
      | ~ v1_relat_1(B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_1682,plain,
    ( k7_relat_1('#skF_5','#skF_3') = '#skF_5'
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_1631,c_44])).

tff(c_1694,plain,(
    k7_relat_1('#skF_5','#skF_3') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_211,c_1682])).

tff(c_30,plain,(
    ! [C_24,A_22,B_23] :
      ( k7_relat_1(k7_relat_1(C_24,A_22),B_23) = k7_relat_1(C_24,A_22)
      | ~ r1_tarski(A_22,B_23)
      | ~ v1_relat_1(C_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1700,plain,(
    ! [B_23] :
      ( k7_relat_1('#skF_5',B_23) = k7_relat_1('#skF_5','#skF_3')
      | ~ r1_tarski('#skF_3',B_23)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1694,c_30])).

tff(c_1831,plain,(
    ! [B_1349] :
      ( k7_relat_1('#skF_5',B_1349) = '#skF_5'
      | ~ r1_tarski('#skF_3',B_1349) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_211,c_1694,c_1700])).

tff(c_1835,plain,(
    k7_relat_1('#skF_5','#skF_4') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_60,c_1831])).

tff(c_1836,plain,(
    ~ r2_relset_1('#skF_3','#skF_2','#skF_5','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1835,c_599])).

tff(c_1839,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_394,c_1836])).

tff(c_1841,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_361])).

tff(c_10,plain,(
    ! [A_8] :
      ( k1_xboole_0 = A_8
      | ~ v1_xboole_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1849,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_1841,c_10])).

tff(c_1840,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_361])).

tff(c_1845,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_1840,c_10])).

tff(c_1875,plain,(
    '#skF_5' = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1849,c_1845])).

tff(c_1861,plain,(
    ! [A_50,B_51] : m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(A_50,B_51))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1845,c_56])).

tff(c_2122,plain,(
    ! [A_1376,B_1377] : m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1(A_1376,B_1377))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1875,c_1861])).

tff(c_50,plain,(
    ! [A_42,B_43,D_45] :
      ( r2_relset_1(A_42,B_43,D_45,D_45)
      | ~ m1_subset_1(D_45,k1_zfmisc_1(k2_zfmisc_1(A_42,B_43))) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_2138,plain,(
    ! [A_1376,B_1377] : r2_relset_1(A_1376,B_1377,'#skF_2','#skF_2') ),
    inference(resolution,[status(thm)],[c_2122,c_50])).

tff(c_1869,plain,(
    ! [A_26] : k7_relat_1('#skF_5',A_26) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1845,c_1845,c_34])).

tff(c_1907,plain,(
    ! [A_26] : k7_relat_1('#skF_2',A_26) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1875,c_1875,c_1869])).

tff(c_2121,plain,(
    ! [A_50,B_51] : m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1(A_50,B_51))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1875,c_1861])).

tff(c_2182,plain,(
    ! [A_1383,B_1384,C_1385,D_1386] :
      ( k5_relset_1(A_1383,B_1384,C_1385,D_1386) = k7_relat_1(C_1385,D_1386)
      | ~ m1_subset_1(C_1385,k1_zfmisc_1(k2_zfmisc_1(A_1383,B_1384))) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_2184,plain,(
    ! [A_50,B_51,D_1386] : k5_relset_1(A_50,B_51,'#skF_2',D_1386) = k7_relat_1('#skF_2',D_1386) ),
    inference(resolution,[status(thm)],[c_2121,c_2182])).

tff(c_2193,plain,(
    ! [A_50,B_51,D_1386] : k5_relset_1(A_50,B_51,'#skF_2',D_1386) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1907,c_2184])).

tff(c_1884,plain,(
    ~ r2_relset_1('#skF_3','#skF_2',k5_relset_1('#skF_3','#skF_2','#skF_2','#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1875,c_1875,c_58])).

tff(c_2195,plain,(
    ~ r2_relset_1('#skF_3','#skF_2','#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2193,c_1884])).

tff(c_2198,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2138,c_2195])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:58:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.20/1.75  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.20/1.76  
% 4.20/1.76  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.54/1.76  %$ r2_relset_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k5_relset_1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 4.54/1.76  
% 4.54/1.76  %Foreground sorts:
% 4.54/1.76  
% 4.54/1.76  
% 4.54/1.76  %Background operators:
% 4.54/1.76  
% 4.54/1.76  
% 4.54/1.76  %Foreground operators:
% 4.54/1.76  tff(k5_relset_1, type, k5_relset_1: ($i * $i * $i * $i) > $i).
% 4.54/1.76  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.54/1.76  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 4.54/1.76  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.54/1.76  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.54/1.76  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 4.54/1.76  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.54/1.76  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.54/1.76  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.54/1.76  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.54/1.76  tff('#skF_5', type, '#skF_5': $i).
% 4.54/1.76  tff('#skF_2', type, '#skF_2': $i).
% 4.54/1.76  tff('#skF_3', type, '#skF_3': $i).
% 4.54/1.76  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.54/1.76  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.54/1.76  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.54/1.76  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.54/1.76  tff('#skF_4', type, '#skF_4': $i).
% 4.54/1.76  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.54/1.76  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.54/1.76  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.54/1.76  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.54/1.76  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.54/1.76  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.54/1.76  
% 4.63/1.79  tff(f_144, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A))) => (r1_tarski(B, C) => r2_relset_1(B, A, k5_relset_1(B, A, D, C), D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_relset_1)).
% 4.63/1.79  tff(f_127, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 4.63/1.79  tff(f_67, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 4.63/1.79  tff(f_65, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 4.63/1.79  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 4.63/1.79  tff(f_51, axiom, (![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_zfmisc_1)).
% 4.63/1.79  tff(f_54, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 4.63/1.79  tff(f_115, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => v1_xboole_0(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc4_relset_1)).
% 4.63/1.79  tff(f_58, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 4.63/1.79  tff(f_91, axiom, (![A, B]: ~((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~((k1_relat_1(k2_zfmisc_1(A, B)) = A) & (k2_relat_1(k2_zfmisc_1(A, B)) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t195_relat_1)).
% 4.63/1.79  tff(f_102, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_relat_1)).
% 4.63/1.79  tff(f_137, axiom, (![A, B]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_relset_1)).
% 4.63/1.79  tff(f_79, axiom, (![A]: (k7_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t111_relat_1)).
% 4.63/1.79  tff(f_37, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 4.63/1.79  tff(f_47, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 4.63/1.79  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 4.63/1.79  tff(f_119, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k5_relset_1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k5_relset_1)).
% 4.63/1.79  tff(f_108, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t97_relat_1)).
% 4.63/1.79  tff(f_73, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t102_relat_1)).
% 4.63/1.79  tff(f_41, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_boole)).
% 4.63/1.79  tff(c_62, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_144])).
% 4.63/1.79  tff(c_380, plain, (![A_100, B_101, D_102]: (r2_relset_1(A_100, B_101, D_102, D_102) | ~m1_subset_1(D_102, k1_zfmisc_1(k2_zfmisc_1(A_100, B_101))))), inference(cnfTransformation, [status(thm)], [f_127])).
% 4.63/1.79  tff(c_394, plain, (r2_relset_1('#skF_3', '#skF_2', '#skF_5', '#skF_5')), inference(resolution, [status(thm)], [c_62, c_380])).
% 4.63/1.79  tff(c_60, plain, (r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_144])).
% 4.63/1.79  tff(c_28, plain, (![A_20, B_21]: (v1_relat_1(k2_zfmisc_1(A_20, B_21)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.63/1.79  tff(c_189, plain, (![B_77, A_78]: (v1_relat_1(B_77) | ~m1_subset_1(B_77, k1_zfmisc_1(A_78)) | ~v1_relat_1(A_78))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.63/1.79  tff(c_201, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_2'))), inference(resolution, [status(thm)], [c_62, c_189])).
% 4.63/1.79  tff(c_211, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_201])).
% 4.63/1.79  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.63/1.79  tff(c_272, plain, (![A_85, B_86]: (k2_xboole_0(k1_tarski(A_85), B_86)=B_86 | ~r2_hidden(A_85, B_86))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.63/1.79  tff(c_20, plain, (![A_13, B_14]: (k2_xboole_0(k1_tarski(A_13), B_14)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.63/1.79  tff(c_304, plain, (![B_89, A_90]: (k1_xboole_0!=B_89 | ~r2_hidden(A_90, B_89))), inference(superposition, [status(thm), theory('equality')], [c_272, c_20])).
% 4.63/1.79  tff(c_308, plain, (![A_1]: (k1_xboole_0!=A_1 | v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_4, c_304])).
% 4.63/1.79  tff(c_341, plain, (![C_96, B_97, A_98]: (v1_xboole_0(C_96) | ~m1_subset_1(C_96, k1_zfmisc_1(k2_zfmisc_1(B_97, A_98))) | ~v1_xboole_0(A_98))), inference(cnfTransformation, [status(thm)], [f_115])).
% 4.63/1.79  tff(c_361, plain, (v1_xboole_0('#skF_5') | ~v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_62, c_341])).
% 4.63/1.79  tff(c_364, plain, (~v1_xboole_0('#skF_2')), inference(splitLeft, [status(thm)], [c_361])).
% 4.63/1.79  tff(c_368, plain, (k1_xboole_0!='#skF_2'), inference(resolution, [status(thm)], [c_308, c_364])).
% 4.63/1.79  tff(c_152, plain, (![A_73, B_74]: (r1_tarski(A_73, B_74) | ~m1_subset_1(A_73, k1_zfmisc_1(B_74)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.63/1.79  tff(c_168, plain, (r1_tarski('#skF_5', k2_zfmisc_1('#skF_3', '#skF_2'))), inference(resolution, [status(thm)], [c_62, c_152])).
% 4.63/1.79  tff(c_36, plain, (![A_27, B_28]: (k2_relat_1(k2_zfmisc_1(A_27, B_28))=B_28 | k1_xboole_0=B_28 | k1_xboole_0=A_27)), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.63/1.79  tff(c_462, plain, (![A_117, B_118]: (r1_tarski(k2_relat_1(A_117), k2_relat_1(B_118)) | ~r1_tarski(A_117, B_118) | ~v1_relat_1(B_118) | ~v1_relat_1(A_117))), inference(cnfTransformation, [status(thm)], [f_102])).
% 4.63/1.79  tff(c_474, plain, (![A_117, B_28, A_27]: (r1_tarski(k2_relat_1(A_117), B_28) | ~r1_tarski(A_117, k2_zfmisc_1(A_27, B_28)) | ~v1_relat_1(k2_zfmisc_1(A_27, B_28)) | ~v1_relat_1(A_117) | k1_xboole_0=B_28 | k1_xboole_0=A_27)), inference(superposition, [status(thm), theory('equality')], [c_36, c_462])).
% 4.63/1.79  tff(c_807, plain, (![A_183, B_184, A_185]: (r1_tarski(k2_relat_1(A_183), B_184) | ~r1_tarski(A_183, k2_zfmisc_1(A_185, B_184)) | ~v1_relat_1(A_183) | k1_xboole_0=B_184 | k1_xboole_0=A_185)), inference(demodulation, [status(thm), theory('equality')], [c_28, c_474])).
% 4.63/1.79  tff(c_809, plain, (r1_tarski(k2_relat_1('#skF_5'), '#skF_2') | ~v1_relat_1('#skF_5') | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_168, c_807])).
% 4.63/1.79  tff(c_818, plain, (r1_tarski(k2_relat_1('#skF_5'), '#skF_2') | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_211, c_809])).
% 4.63/1.79  tff(c_819, plain, (r1_tarski(k2_relat_1('#skF_5'), '#skF_2') | k1_xboole_0='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_368, c_818])).
% 4.63/1.79  tff(c_825, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_819])).
% 4.63/1.79  tff(c_56, plain, (![A_50, B_51]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_50, B_51))))), inference(cnfTransformation, [status(thm)], [f_137])).
% 4.63/1.79  tff(c_393, plain, (![A_50, B_51]: (r2_relset_1(A_50, B_51, k1_xboole_0, k1_xboole_0))), inference(resolution, [status(thm)], [c_56, c_380])).
% 4.63/1.79  tff(c_841, plain, (![A_50, B_51]: (r2_relset_1(A_50, B_51, '#skF_3', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_825, c_825, c_393])).
% 4.63/1.79  tff(c_34, plain, (![A_26]: (k7_relat_1(k1_xboole_0, A_26)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_79])).
% 4.63/1.79  tff(c_863, plain, (![A_26]: (k7_relat_1('#skF_3', A_26)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_825, c_825, c_34])).
% 4.63/1.79  tff(c_8, plain, (![A_7]: (k3_xboole_0(A_7, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.63/1.79  tff(c_859, plain, (![A_7]: (k3_xboole_0(A_7, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_825, c_825, c_8])).
% 4.63/1.79  tff(c_16, plain, (![B_10]: (k2_zfmisc_1(k1_xboole_0, B_10)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.63/1.79  tff(c_862, plain, (![B_10]: (k2_zfmisc_1('#skF_3', B_10)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_825, c_825, c_16])).
% 4.63/1.79  tff(c_6, plain, (![A_5, B_6]: (k3_xboole_0(A_5, B_6)=A_5 | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.63/1.79  tff(c_188, plain, (k3_xboole_0('#skF_5', k2_zfmisc_1('#skF_3', '#skF_2'))='#skF_5'), inference(resolution, [status(thm)], [c_168, c_6])).
% 4.63/1.79  tff(c_921, plain, (k3_xboole_0('#skF_5', '#skF_3')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_862, c_188])).
% 4.63/1.79  tff(c_1074, plain, ('#skF_5'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_859, c_921])).
% 4.63/1.79  tff(c_576, plain, (![A_133, B_134, C_135, D_136]: (k5_relset_1(A_133, B_134, C_135, D_136)=k7_relat_1(C_135, D_136) | ~m1_subset_1(C_135, k1_zfmisc_1(k2_zfmisc_1(A_133, B_134))))), inference(cnfTransformation, [status(thm)], [f_119])).
% 4.63/1.79  tff(c_591, plain, (![D_136]: (k5_relset_1('#skF_3', '#skF_2', '#skF_5', D_136)=k7_relat_1('#skF_5', D_136))), inference(resolution, [status(thm)], [c_62, c_576])).
% 4.63/1.79  tff(c_58, plain, (~r2_relset_1('#skF_3', '#skF_2', k5_relset_1('#skF_3', '#skF_2', '#skF_5', '#skF_4'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_144])).
% 4.63/1.79  tff(c_599, plain, (~r2_relset_1('#skF_3', '#skF_2', k7_relat_1('#skF_5', '#skF_4'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_591, c_58])).
% 4.63/1.79  tff(c_1078, plain, (~r2_relset_1('#skF_3', '#skF_2', k7_relat_1('#skF_3', '#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1074, c_1074, c_599])).
% 4.63/1.79  tff(c_1085, plain, (~r2_relset_1('#skF_3', '#skF_2', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_863, c_1078])).
% 4.63/1.79  tff(c_1149, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_841, c_1085])).
% 4.63/1.79  tff(c_1151, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_819])).
% 4.63/1.79  tff(c_38, plain, (![A_27, B_28]: (k1_relat_1(k2_zfmisc_1(A_27, B_28))=A_27 | k1_xboole_0=B_28 | k1_xboole_0=A_27)), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.63/1.79  tff(c_402, plain, (![A_106, B_107]: (r1_tarski(k1_relat_1(A_106), k1_relat_1(B_107)) | ~r1_tarski(A_106, B_107) | ~v1_relat_1(B_107) | ~v1_relat_1(A_106))), inference(cnfTransformation, [status(thm)], [f_102])).
% 4.63/1.79  tff(c_417, plain, (![A_106, A_27, B_28]: (r1_tarski(k1_relat_1(A_106), A_27) | ~r1_tarski(A_106, k2_zfmisc_1(A_27, B_28)) | ~v1_relat_1(k2_zfmisc_1(A_27, B_28)) | ~v1_relat_1(A_106) | k1_xboole_0=B_28 | k1_xboole_0=A_27)), inference(superposition, [status(thm), theory('equality')], [c_38, c_402])).
% 4.63/1.79  tff(c_1613, plain, (![A_1340, A_1341, B_1342]: (r1_tarski(k1_relat_1(A_1340), A_1341) | ~r1_tarski(A_1340, k2_zfmisc_1(A_1341, B_1342)) | ~v1_relat_1(A_1340) | k1_xboole_0=B_1342 | k1_xboole_0=A_1341)), inference(demodulation, [status(thm), theory('equality')], [c_28, c_417])).
% 4.63/1.79  tff(c_1618, plain, (r1_tarski(k1_relat_1('#skF_5'), '#skF_3') | ~v1_relat_1('#skF_5') | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_168, c_1613])).
% 4.63/1.79  tff(c_1630, plain, (r1_tarski(k1_relat_1('#skF_5'), '#skF_3') | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_211, c_1618])).
% 4.63/1.79  tff(c_1631, plain, (r1_tarski(k1_relat_1('#skF_5'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_1151, c_368, c_1630])).
% 4.63/1.79  tff(c_44, plain, (![B_33, A_32]: (k7_relat_1(B_33, A_32)=B_33 | ~r1_tarski(k1_relat_1(B_33), A_32) | ~v1_relat_1(B_33))), inference(cnfTransformation, [status(thm)], [f_108])).
% 4.63/1.79  tff(c_1682, plain, (k7_relat_1('#skF_5', '#skF_3')='#skF_5' | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_1631, c_44])).
% 4.63/1.79  tff(c_1694, plain, (k7_relat_1('#skF_5', '#skF_3')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_211, c_1682])).
% 4.63/1.79  tff(c_30, plain, (![C_24, A_22, B_23]: (k7_relat_1(k7_relat_1(C_24, A_22), B_23)=k7_relat_1(C_24, A_22) | ~r1_tarski(A_22, B_23) | ~v1_relat_1(C_24))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.63/1.79  tff(c_1700, plain, (![B_23]: (k7_relat_1('#skF_5', B_23)=k7_relat_1('#skF_5', '#skF_3') | ~r1_tarski('#skF_3', B_23) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_1694, c_30])).
% 4.63/1.79  tff(c_1831, plain, (![B_1349]: (k7_relat_1('#skF_5', B_1349)='#skF_5' | ~r1_tarski('#skF_3', B_1349))), inference(demodulation, [status(thm), theory('equality')], [c_211, c_1694, c_1700])).
% 4.63/1.79  tff(c_1835, plain, (k7_relat_1('#skF_5', '#skF_4')='#skF_5'), inference(resolution, [status(thm)], [c_60, c_1831])).
% 4.63/1.79  tff(c_1836, plain, (~r2_relset_1('#skF_3', '#skF_2', '#skF_5', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1835, c_599])).
% 4.63/1.79  tff(c_1839, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_394, c_1836])).
% 4.63/1.79  tff(c_1841, plain, (v1_xboole_0('#skF_2')), inference(splitRight, [status(thm)], [c_361])).
% 4.63/1.79  tff(c_10, plain, (![A_8]: (k1_xboole_0=A_8 | ~v1_xboole_0(A_8))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.63/1.79  tff(c_1849, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_1841, c_10])).
% 4.63/1.79  tff(c_1840, plain, (v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_361])).
% 4.63/1.79  tff(c_1845, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_1840, c_10])).
% 4.63/1.79  tff(c_1875, plain, ('#skF_5'='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1849, c_1845])).
% 4.63/1.79  tff(c_1861, plain, (![A_50, B_51]: (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(A_50, B_51))))), inference(demodulation, [status(thm), theory('equality')], [c_1845, c_56])).
% 4.63/1.79  tff(c_2122, plain, (![A_1376, B_1377]: (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1(A_1376, B_1377))))), inference(demodulation, [status(thm), theory('equality')], [c_1875, c_1861])).
% 4.63/1.79  tff(c_50, plain, (![A_42, B_43, D_45]: (r2_relset_1(A_42, B_43, D_45, D_45) | ~m1_subset_1(D_45, k1_zfmisc_1(k2_zfmisc_1(A_42, B_43))))), inference(cnfTransformation, [status(thm)], [f_127])).
% 4.63/1.79  tff(c_2138, plain, (![A_1376, B_1377]: (r2_relset_1(A_1376, B_1377, '#skF_2', '#skF_2'))), inference(resolution, [status(thm)], [c_2122, c_50])).
% 4.63/1.79  tff(c_1869, plain, (![A_26]: (k7_relat_1('#skF_5', A_26)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1845, c_1845, c_34])).
% 4.63/1.79  tff(c_1907, plain, (![A_26]: (k7_relat_1('#skF_2', A_26)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1875, c_1875, c_1869])).
% 4.63/1.79  tff(c_2121, plain, (![A_50, B_51]: (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1(A_50, B_51))))), inference(demodulation, [status(thm), theory('equality')], [c_1875, c_1861])).
% 4.63/1.79  tff(c_2182, plain, (![A_1383, B_1384, C_1385, D_1386]: (k5_relset_1(A_1383, B_1384, C_1385, D_1386)=k7_relat_1(C_1385, D_1386) | ~m1_subset_1(C_1385, k1_zfmisc_1(k2_zfmisc_1(A_1383, B_1384))))), inference(cnfTransformation, [status(thm)], [f_119])).
% 4.63/1.79  tff(c_2184, plain, (![A_50, B_51, D_1386]: (k5_relset_1(A_50, B_51, '#skF_2', D_1386)=k7_relat_1('#skF_2', D_1386))), inference(resolution, [status(thm)], [c_2121, c_2182])).
% 4.63/1.79  tff(c_2193, plain, (![A_50, B_51, D_1386]: (k5_relset_1(A_50, B_51, '#skF_2', D_1386)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1907, c_2184])).
% 4.63/1.79  tff(c_1884, plain, (~r2_relset_1('#skF_3', '#skF_2', k5_relset_1('#skF_3', '#skF_2', '#skF_2', '#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1875, c_1875, c_58])).
% 4.63/1.79  tff(c_2195, plain, (~r2_relset_1('#skF_3', '#skF_2', '#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2193, c_1884])).
% 4.63/1.79  tff(c_2198, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2138, c_2195])).
% 4.63/1.79  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.63/1.79  
% 4.63/1.79  Inference rules
% 4.63/1.79  ----------------------
% 4.63/1.79  #Ref     : 0
% 4.63/1.79  #Sup     : 516
% 4.63/1.79  #Fact    : 0
% 4.63/1.79  #Define  : 0
% 4.63/1.79  #Split   : 8
% 4.63/1.79  #Chain   : 0
% 4.63/1.79  #Close   : 0
% 4.63/1.79  
% 4.63/1.79  Ordering : KBO
% 4.63/1.79  
% 4.63/1.79  Simplification rules
% 4.63/1.79  ----------------------
% 4.63/1.79  #Subsume      : 49
% 4.63/1.79  #Demod        : 409
% 4.63/1.79  #Tautology    : 256
% 4.63/1.79  #SimpNegUnit  : 4
% 4.63/1.79  #BackRed      : 84
% 4.63/1.79  
% 4.63/1.79  #Partial instantiations: 256
% 4.63/1.79  #Strategies tried      : 1
% 4.63/1.79  
% 4.63/1.79  Timing (in seconds)
% 4.63/1.79  ----------------------
% 4.63/1.79  Preprocessing        : 0.35
% 4.63/1.79  Parsing              : 0.19
% 4.63/1.79  CNF conversion       : 0.02
% 4.63/1.79  Main loop            : 0.66
% 4.63/1.79  Inferencing          : 0.24
% 4.63/1.79  Reduction            : 0.22
% 4.63/1.79  Demodulation         : 0.16
% 4.63/1.79  BG Simplification    : 0.03
% 4.63/1.79  Subsumption          : 0.11
% 4.63/1.79  Abstraction          : 0.03
% 4.63/1.79  MUC search           : 0.00
% 4.63/1.79  Cooper               : 0.00
% 4.63/1.79  Total                : 1.06
% 4.63/1.79  Index Insertion      : 0.00
% 4.63/1.79  Index Deletion       : 0.00
% 4.63/1.79  Index Matching       : 0.00
% 4.63/1.79  BG Taut test         : 0.00
%------------------------------------------------------------------------------
