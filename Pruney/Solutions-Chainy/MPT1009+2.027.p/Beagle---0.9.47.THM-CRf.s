%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:46 EST 2020

% Result     : Theorem 5.41s
% Output     : CNFRefutation 5.80s
% Verified   : 
% Statistics : Number of formulae       :  129 ( 415 expanded)
%              Number of leaves         :   41 ( 156 expanded)
%              Depth                    :   12
%              Number of atoms          :  203 ( 861 expanded)
%              Number of equality atoms :   65 ( 222 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_116,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,k1_tarski(A),B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r1_tarski(k7_relset_1(k1_tarski(A),B,D,C),k1_tarski(k1_funct_1(D,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_2)).

tff(f_88,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k9_relat_1(B,A),k2_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_relat_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_104,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C)))
     => ( r1_tarski(k1_relat_1(D),B)
       => m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_relset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_64,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_94,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_84,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( k1_relat_1(B) = k1_tarski(A)
       => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_98,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_35,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_tarski(B,C))
    <=> ~ ( A != k1_xboole_0
          & A != k1_tarski(B)
          & A != k1_tarski(C)
          & A != k2_tarski(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l45_zfmisc_1)).

tff(f_76,axiom,(
    ! [A] : k9_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t150_relat_1)).

tff(c_60,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_137,plain,(
    ! [C_54,A_55,B_56] :
      ( v1_relat_1(C_54)
      | ~ m1_subset_1(C_54,k1_zfmisc_1(k2_zfmisc_1(A_55,B_56))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_150,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_137])).

tff(c_40,plain,(
    ! [B_20,A_19] :
      ( r1_tarski(k9_relat_1(B_20,A_19),k2_relat_1(B_20))
      | ~ v1_relat_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_30,plain,(
    ! [B_14] : k2_zfmisc_1(k1_xboole_0,B_14) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_569,plain,(
    ! [D_125,B_126,C_127,A_128] :
      ( m1_subset_1(D_125,k1_zfmisc_1(k2_zfmisc_1(B_126,C_127)))
      | ~ r1_tarski(k1_relat_1(D_125),B_126)
      | ~ m1_subset_1(D_125,k1_zfmisc_1(k2_zfmisc_1(A_128,C_127))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_588,plain,(
    ! [B_130] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(B_130,'#skF_2')))
      | ~ r1_tarski(k1_relat_1('#skF_4'),B_130) ) ),
    inference(resolution,[status(thm)],[c_60,c_569])).

tff(c_608,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(k1_xboole_0))
    | ~ r1_tarski(k1_relat_1('#skF_4'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_588])).

tff(c_630,plain,(
    ~ r1_tarski(k1_relat_1('#skF_4'),k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_608])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_34,plain,(
    ! [A_15,B_16] :
      ( m1_subset_1(A_15,k1_zfmisc_1(B_16))
      | ~ r1_tarski(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_28,plain,(
    ! [A_13] : k2_zfmisc_1(A_13,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_151,plain,(
    ! [C_57] :
      ( v1_relat_1(C_57)
      | ~ m1_subset_1(C_57,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_137])).

tff(c_157,plain,(
    ! [A_58] :
      ( v1_relat_1(A_58)
      | ~ r1_tarski(A_58,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_34,c_151])).

tff(c_166,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_6,c_157])).

tff(c_355,plain,(
    ! [C_94,A_95,B_96] :
      ( v4_relat_1(C_94,A_95)
      | ~ m1_subset_1(C_94,k1_zfmisc_1(k2_zfmisc_1(A_95,B_96))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_404,plain,(
    ! [A_105,A_106,B_107] :
      ( v4_relat_1(A_105,A_106)
      | ~ r1_tarski(A_105,k2_zfmisc_1(A_106,B_107)) ) ),
    inference(resolution,[status(thm)],[c_34,c_355])).

tff(c_429,plain,(
    ! [A_106,B_107] : v4_relat_1(k2_zfmisc_1(A_106,B_107),A_106) ),
    inference(resolution,[status(thm)],[c_6,c_404])).

tff(c_327,plain,(
    ! [B_92,A_93] :
      ( r1_tarski(k1_relat_1(B_92),A_93)
      | ~ v4_relat_1(B_92,A_93)
      | ~ v1_relat_1(B_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_208,plain,(
    ! [B_66,A_67] :
      ( B_66 = A_67
      | ~ r1_tarski(B_66,A_67)
      | ~ r1_tarski(A_67,B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_226,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ r1_tarski(A_3,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_8,c_208])).

tff(c_453,plain,(
    ! [B_115] :
      ( k1_relat_1(B_115) = k1_xboole_0
      | ~ v4_relat_1(B_115,k1_xboole_0)
      | ~ v1_relat_1(B_115) ) ),
    inference(resolution,[status(thm)],[c_327,c_226])).

tff(c_457,plain,(
    ! [B_107] :
      ( k1_relat_1(k2_zfmisc_1(k1_xboole_0,B_107)) = k1_xboole_0
      | ~ v1_relat_1(k2_zfmisc_1(k1_xboole_0,B_107)) ) ),
    inference(resolution,[status(thm)],[c_429,c_453])).

tff(c_468,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_166,c_30,c_30,c_457])).

tff(c_64,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_44,plain,(
    ! [B_23,A_22] :
      ( k1_tarski(k1_funct_1(B_23,A_22)) = k2_relat_1(B_23)
      | k1_tarski(A_22) != k1_relat_1(B_23)
      | ~ v1_funct_1(B_23)
      | ~ v1_relat_1(B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_441,plain,(
    ! [A_111,B_112,C_113,D_114] :
      ( k7_relset_1(A_111,B_112,C_113,D_114) = k9_relat_1(C_113,D_114)
      | ~ m1_subset_1(C_113,k1_zfmisc_1(k2_zfmisc_1(A_111,B_112))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_452,plain,(
    ! [D_114] : k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4',D_114) = k9_relat_1('#skF_4',D_114) ),
    inference(resolution,[status(thm)],[c_60,c_441])).

tff(c_56,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_493,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_452,c_56])).

tff(c_505,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_493])).

tff(c_507,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_150,c_64,c_505])).

tff(c_727,plain,(
    k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_507])).

tff(c_370,plain,(
    v4_relat_1('#skF_4',k1_tarski('#skF_1')) ),
    inference(resolution,[status(thm)],[c_60,c_355])).

tff(c_38,plain,(
    ! [B_18,A_17] :
      ( r1_tarski(k1_relat_1(B_18),A_17)
      | ~ v4_relat_1(B_18,A_17)
      | ~ v1_relat_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_10,plain,(
    ! [A_4] : k2_tarski(A_4,A_4) = k1_tarski(A_4) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_654,plain,(
    ! [B_133,C_134,A_135] :
      ( k2_tarski(B_133,C_134) = A_135
      | k1_tarski(C_134) = A_135
      | k1_tarski(B_133) = A_135
      | k1_xboole_0 = A_135
      | ~ r1_tarski(A_135,k2_tarski(B_133,C_134)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_667,plain,(
    ! [A_4,A_135] :
      ( k2_tarski(A_4,A_4) = A_135
      | k1_tarski(A_4) = A_135
      | k1_tarski(A_4) = A_135
      | k1_xboole_0 = A_135
      | ~ r1_tarski(A_135,k1_tarski(A_4)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_654])).

tff(c_1687,plain,(
    ! [A_235,A_236] :
      ( k1_tarski(A_235) = A_236
      | k1_tarski(A_235) = A_236
      | k1_tarski(A_235) = A_236
      | k1_xboole_0 = A_236
      | ~ r1_tarski(A_236,k1_tarski(A_235)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_667])).

tff(c_1708,plain,(
    ! [A_237,B_238] :
      ( k1_tarski(A_237) = k1_relat_1(B_238)
      | k1_relat_1(B_238) = k1_xboole_0
      | ~ v4_relat_1(B_238,k1_tarski(A_237))
      | ~ v1_relat_1(B_238) ) ),
    inference(resolution,[status(thm)],[c_38,c_1687])).

tff(c_1746,plain,
    ( k1_tarski('#skF_1') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_370,c_1708])).

tff(c_1765,plain,
    ( k1_tarski('#skF_1') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_150,c_1746])).

tff(c_1766,plain,(
    k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_727,c_1765])).

tff(c_32,plain,(
    ! [A_15,B_16] :
      ( r1_tarski(A_15,B_16)
      | ~ m1_subset_1(A_15,k1_zfmisc_1(B_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_641,plain,(
    ! [B_132] :
      ( r1_tarski('#skF_4',k2_zfmisc_1(B_132,'#skF_2'))
      | ~ r1_tarski(k1_relat_1('#skF_4'),B_132) ) ),
    inference(resolution,[status(thm)],[c_588,c_32])).

tff(c_653,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_2')) ),
    inference(resolution,[status(thm)],[c_6,c_641])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_701,plain,
    ( k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_2') = '#skF_4'
    | ~ r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_2'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_653,c_2])).

tff(c_1005,plain,(
    ~ r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_2'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_701])).

tff(c_1768,plain,(
    ~ r1_tarski(k2_zfmisc_1(k1_xboole_0,'#skF_2'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1766,c_1005])).

tff(c_1780,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_30,c_1768])).

tff(c_1781,plain,(
    k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_2') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_701])).

tff(c_2467,plain,(
    ! [D_292,B_293,B_294] :
      ( m1_subset_1(D_292,k1_zfmisc_1(k2_zfmisc_1(B_293,B_294)))
      | ~ r1_tarski(k1_relat_1(D_292),B_293)
      | ~ m1_subset_1(D_292,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_569])).

tff(c_2563,plain,(
    ! [D_298] :
      ( m1_subset_1(D_298,k1_zfmisc_1('#skF_4'))
      | ~ r1_tarski(k1_relat_1(D_298),k1_relat_1('#skF_4'))
      | ~ m1_subset_1(D_298,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1781,c_2467])).

tff(c_2572,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1('#skF_4'))
    | ~ r1_tarski(k1_xboole_0,k1_relat_1('#skF_4'))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_468,c_2563])).

tff(c_2586,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1('#skF_4'))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_2572])).

tff(c_2590,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_2586])).

tff(c_2593,plain,(
    ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_34,c_2590])).

tff(c_2597,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_2593])).

tff(c_2599,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_2586])).

tff(c_2707,plain,(
    ! [A_300,A_301] :
      ( k1_tarski(A_300) = A_301
      | k1_tarski(A_300) = A_301
      | k1_tarski(A_300) = A_301
      | k1_xboole_0 = A_301
      | ~ r1_tarski(A_301,k1_tarski(A_300)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_667])).

tff(c_4262,plain,(
    ! [A_367,B_368] :
      ( k1_tarski(A_367) = k1_relat_1(B_368)
      | k1_relat_1(B_368) = k1_xboole_0
      | ~ v4_relat_1(B_368,k1_tarski(A_367))
      | ~ v1_relat_1(B_368) ) ),
    inference(resolution,[status(thm)],[c_38,c_2707])).

tff(c_4312,plain,
    ( k1_tarski('#skF_1') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_370,c_4262])).

tff(c_4338,plain,
    ( k1_tarski('#skF_1') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_150,c_4312])).

tff(c_4339,plain,(
    k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_727,c_4338])).

tff(c_4129,plain,(
    ! [D_362,B_363,B_364] :
      ( r1_tarski(D_362,k2_zfmisc_1(B_363,B_364))
      | ~ r1_tarski(k1_relat_1(D_362),B_363)
      | ~ m1_subset_1(D_362,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_2467,c_32])).

tff(c_4165,plain,(
    ! [D_365,B_366] :
      ( r1_tarski(D_365,k2_zfmisc_1(k1_relat_1(D_365),B_366))
      | ~ m1_subset_1(D_365,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_6,c_4129])).

tff(c_50,plain,(
    ! [C_29,A_27,B_28] :
      ( v4_relat_1(C_29,A_27)
      | ~ m1_subset_1(C_29,k1_zfmisc_1(k2_zfmisc_1(A_27,B_28))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_611,plain,(
    ! [B_130] :
      ( v4_relat_1('#skF_4',B_130)
      | ~ r1_tarski(k1_relat_1('#skF_4'),B_130) ) ),
    inference(resolution,[status(thm)],[c_588,c_50])).

tff(c_4239,plain,(
    ! [B_366] :
      ( v4_relat_1('#skF_4',k2_zfmisc_1(k1_relat_1(k1_relat_1('#skF_4')),B_366))
      | ~ m1_subset_1(k1_relat_1('#skF_4'),k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_4165,c_611])).

tff(c_4252,plain,(
    ~ m1_subset_1(k1_relat_1('#skF_4'),k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_4239])).

tff(c_4340,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4339,c_4252])).

tff(c_4362,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2599,c_4340])).

tff(c_4364,plain,(
    m1_subset_1(k1_relat_1('#skF_4'),k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_4239])).

tff(c_4378,plain,(
    r1_tarski(k1_relat_1('#skF_4'),k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_4364,c_32])).

tff(c_4387,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_630,c_4378])).

tff(c_4388,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_507])).

tff(c_4423,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_4388])).

tff(c_4427,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_150,c_4423])).

tff(c_4428,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_608])).

tff(c_4457,plain,(
    r1_tarski('#skF_4',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_4428,c_32])).

tff(c_4491,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_4457,c_226])).

tff(c_4518,plain,(
    ! [A_3] : r1_tarski('#skF_4',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4491,c_8])).

tff(c_42,plain,(
    ! [A_21] : k9_relat_1(k1_xboole_0,A_21) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_4515,plain,(
    ! [A_21] : k9_relat_1('#skF_4',A_21) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4491,c_4491,c_42])).

tff(c_4767,plain,(
    ~ r1_tarski('#skF_4',k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4515,c_493])).

tff(c_4770,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4518,c_4767])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n012.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 12:26:37 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.41/2.03  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.41/2.04  
% 5.41/2.04  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.41/2.05  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 5.41/2.05  
% 5.41/2.05  %Foreground sorts:
% 5.41/2.05  
% 5.41/2.05  
% 5.41/2.05  %Background operators:
% 5.41/2.05  
% 5.41/2.05  
% 5.41/2.05  %Foreground operators:
% 5.41/2.05  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.41/2.05  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.41/2.05  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.41/2.05  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.41/2.05  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.41/2.05  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.41/2.05  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.41/2.05  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 5.41/2.05  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.41/2.05  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.41/2.05  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.41/2.05  tff('#skF_2', type, '#skF_2': $i).
% 5.41/2.05  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 5.41/2.05  tff('#skF_3', type, '#skF_3': $i).
% 5.41/2.05  tff('#skF_1', type, '#skF_1': $i).
% 5.41/2.05  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 5.41/2.05  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.41/2.05  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 5.41/2.05  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.41/2.05  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.41/2.05  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.41/2.05  tff('#skF_4', type, '#skF_4': $i).
% 5.41/2.05  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.41/2.05  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 5.41/2.05  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.41/2.05  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.41/2.05  
% 5.80/2.06  tff(f_116, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, k1_tarski(A), B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r1_tarski(k7_relset_1(k1_tarski(A), B, D, C), k1_tarski(k1_funct_1(D, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_funct_2)).
% 5.80/2.06  tff(f_88, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 5.80/2.06  tff(f_74, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k9_relat_1(B, A), k2_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t144_relat_1)).
% 5.80/2.06  tff(f_60, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 5.80/2.06  tff(f_104, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C))) => (r1_tarski(k1_relat_1(D), B) => m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_relset_1)).
% 5.80/2.06  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.80/2.06  tff(f_64, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 5.80/2.06  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 5.80/2.06  tff(f_94, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 5.80/2.06  tff(f_70, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 5.80/2.06  tff(f_84, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_funct_1)).
% 5.80/2.06  tff(f_98, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 5.80/2.06  tff(f_35, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 5.80/2.06  tff(f_54, axiom, (![A, B, C]: (r1_tarski(A, k2_tarski(B, C)) <=> ~(((~(A = k1_xboole_0) & ~(A = k1_tarski(B))) & ~(A = k1_tarski(C))) & ~(A = k2_tarski(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l45_zfmisc_1)).
% 5.80/2.06  tff(f_76, axiom, (![A]: (k9_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t150_relat_1)).
% 5.80/2.06  tff(c_60, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_116])).
% 5.80/2.06  tff(c_137, plain, (![C_54, A_55, B_56]: (v1_relat_1(C_54) | ~m1_subset_1(C_54, k1_zfmisc_1(k2_zfmisc_1(A_55, B_56))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 5.80/2.06  tff(c_150, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_60, c_137])).
% 5.80/2.06  tff(c_40, plain, (![B_20, A_19]: (r1_tarski(k9_relat_1(B_20, A_19), k2_relat_1(B_20)) | ~v1_relat_1(B_20))), inference(cnfTransformation, [status(thm)], [f_74])).
% 5.80/2.06  tff(c_30, plain, (![B_14]: (k2_zfmisc_1(k1_xboole_0, B_14)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.80/2.06  tff(c_569, plain, (![D_125, B_126, C_127, A_128]: (m1_subset_1(D_125, k1_zfmisc_1(k2_zfmisc_1(B_126, C_127))) | ~r1_tarski(k1_relat_1(D_125), B_126) | ~m1_subset_1(D_125, k1_zfmisc_1(k2_zfmisc_1(A_128, C_127))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 5.80/2.06  tff(c_588, plain, (![B_130]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(B_130, '#skF_2'))) | ~r1_tarski(k1_relat_1('#skF_4'), B_130))), inference(resolution, [status(thm)], [c_60, c_569])).
% 5.80/2.06  tff(c_608, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k1_relat_1('#skF_4'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_30, c_588])).
% 5.80/2.06  tff(c_630, plain, (~r1_tarski(k1_relat_1('#skF_4'), k1_xboole_0)), inference(splitLeft, [status(thm)], [c_608])).
% 5.80/2.06  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.80/2.06  tff(c_34, plain, (![A_15, B_16]: (m1_subset_1(A_15, k1_zfmisc_1(B_16)) | ~r1_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.80/2.06  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.80/2.06  tff(c_28, plain, (![A_13]: (k2_zfmisc_1(A_13, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.80/2.06  tff(c_151, plain, (![C_57]: (v1_relat_1(C_57) | ~m1_subset_1(C_57, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_137])).
% 5.80/2.06  tff(c_157, plain, (![A_58]: (v1_relat_1(A_58) | ~r1_tarski(A_58, k1_xboole_0))), inference(resolution, [status(thm)], [c_34, c_151])).
% 5.80/2.06  tff(c_166, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_157])).
% 5.80/2.06  tff(c_355, plain, (![C_94, A_95, B_96]: (v4_relat_1(C_94, A_95) | ~m1_subset_1(C_94, k1_zfmisc_1(k2_zfmisc_1(A_95, B_96))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 5.80/2.06  tff(c_404, plain, (![A_105, A_106, B_107]: (v4_relat_1(A_105, A_106) | ~r1_tarski(A_105, k2_zfmisc_1(A_106, B_107)))), inference(resolution, [status(thm)], [c_34, c_355])).
% 5.80/2.06  tff(c_429, plain, (![A_106, B_107]: (v4_relat_1(k2_zfmisc_1(A_106, B_107), A_106))), inference(resolution, [status(thm)], [c_6, c_404])).
% 5.80/2.06  tff(c_327, plain, (![B_92, A_93]: (r1_tarski(k1_relat_1(B_92), A_93) | ~v4_relat_1(B_92, A_93) | ~v1_relat_1(B_92))), inference(cnfTransformation, [status(thm)], [f_70])).
% 5.80/2.06  tff(c_208, plain, (![B_66, A_67]: (B_66=A_67 | ~r1_tarski(B_66, A_67) | ~r1_tarski(A_67, B_66))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.80/2.06  tff(c_226, plain, (![A_3]: (k1_xboole_0=A_3 | ~r1_tarski(A_3, k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_208])).
% 5.80/2.06  tff(c_453, plain, (![B_115]: (k1_relat_1(B_115)=k1_xboole_0 | ~v4_relat_1(B_115, k1_xboole_0) | ~v1_relat_1(B_115))), inference(resolution, [status(thm)], [c_327, c_226])).
% 5.80/2.06  tff(c_457, plain, (![B_107]: (k1_relat_1(k2_zfmisc_1(k1_xboole_0, B_107))=k1_xboole_0 | ~v1_relat_1(k2_zfmisc_1(k1_xboole_0, B_107)))), inference(resolution, [status(thm)], [c_429, c_453])).
% 5.80/2.06  tff(c_468, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_166, c_30, c_30, c_457])).
% 5.80/2.06  tff(c_64, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_116])).
% 5.80/2.06  tff(c_44, plain, (![B_23, A_22]: (k1_tarski(k1_funct_1(B_23, A_22))=k2_relat_1(B_23) | k1_tarski(A_22)!=k1_relat_1(B_23) | ~v1_funct_1(B_23) | ~v1_relat_1(B_23))), inference(cnfTransformation, [status(thm)], [f_84])).
% 5.80/2.06  tff(c_441, plain, (![A_111, B_112, C_113, D_114]: (k7_relset_1(A_111, B_112, C_113, D_114)=k9_relat_1(C_113, D_114) | ~m1_subset_1(C_113, k1_zfmisc_1(k2_zfmisc_1(A_111, B_112))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 5.80/2.06  tff(c_452, plain, (![D_114]: (k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', D_114)=k9_relat_1('#skF_4', D_114))), inference(resolution, [status(thm)], [c_60, c_441])).
% 5.80/2.06  tff(c_56, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_116])).
% 5.80/2.06  tff(c_493, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_452, c_56])).
% 5.80/2.06  tff(c_505, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_44, c_493])).
% 5.80/2.06  tff(c_507, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_150, c_64, c_505])).
% 5.80/2.06  tff(c_727, plain, (k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(splitLeft, [status(thm)], [c_507])).
% 5.80/2.06  tff(c_370, plain, (v4_relat_1('#skF_4', k1_tarski('#skF_1'))), inference(resolution, [status(thm)], [c_60, c_355])).
% 5.80/2.06  tff(c_38, plain, (![B_18, A_17]: (r1_tarski(k1_relat_1(B_18), A_17) | ~v4_relat_1(B_18, A_17) | ~v1_relat_1(B_18))), inference(cnfTransformation, [status(thm)], [f_70])).
% 5.80/2.06  tff(c_10, plain, (![A_4]: (k2_tarski(A_4, A_4)=k1_tarski(A_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.80/2.06  tff(c_654, plain, (![B_133, C_134, A_135]: (k2_tarski(B_133, C_134)=A_135 | k1_tarski(C_134)=A_135 | k1_tarski(B_133)=A_135 | k1_xboole_0=A_135 | ~r1_tarski(A_135, k2_tarski(B_133, C_134)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.80/2.06  tff(c_667, plain, (![A_4, A_135]: (k2_tarski(A_4, A_4)=A_135 | k1_tarski(A_4)=A_135 | k1_tarski(A_4)=A_135 | k1_xboole_0=A_135 | ~r1_tarski(A_135, k1_tarski(A_4)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_654])).
% 5.80/2.06  tff(c_1687, plain, (![A_235, A_236]: (k1_tarski(A_235)=A_236 | k1_tarski(A_235)=A_236 | k1_tarski(A_235)=A_236 | k1_xboole_0=A_236 | ~r1_tarski(A_236, k1_tarski(A_235)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_667])).
% 5.80/2.06  tff(c_1708, plain, (![A_237, B_238]: (k1_tarski(A_237)=k1_relat_1(B_238) | k1_relat_1(B_238)=k1_xboole_0 | ~v4_relat_1(B_238, k1_tarski(A_237)) | ~v1_relat_1(B_238))), inference(resolution, [status(thm)], [c_38, c_1687])).
% 5.80/2.06  tff(c_1746, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_370, c_1708])).
% 5.80/2.06  tff(c_1765, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_150, c_1746])).
% 5.80/2.06  tff(c_1766, plain, (k1_relat_1('#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_727, c_1765])).
% 5.80/2.06  tff(c_32, plain, (![A_15, B_16]: (r1_tarski(A_15, B_16) | ~m1_subset_1(A_15, k1_zfmisc_1(B_16)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.80/2.06  tff(c_641, plain, (![B_132]: (r1_tarski('#skF_4', k2_zfmisc_1(B_132, '#skF_2')) | ~r1_tarski(k1_relat_1('#skF_4'), B_132))), inference(resolution, [status(thm)], [c_588, c_32])).
% 5.80/2.06  tff(c_653, plain, (r1_tarski('#skF_4', k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_2'))), inference(resolution, [status(thm)], [c_6, c_641])).
% 5.80/2.06  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.80/2.06  tff(c_701, plain, (k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_2')='#skF_4' | ~r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_2'), '#skF_4')), inference(resolution, [status(thm)], [c_653, c_2])).
% 5.80/2.06  tff(c_1005, plain, (~r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_2'), '#skF_4')), inference(splitLeft, [status(thm)], [c_701])).
% 5.80/2.06  tff(c_1768, plain, (~r1_tarski(k2_zfmisc_1(k1_xboole_0, '#skF_2'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1766, c_1005])).
% 5.80/2.06  tff(c_1780, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_30, c_1768])).
% 5.80/2.06  tff(c_1781, plain, (k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_2')='#skF_4'), inference(splitRight, [status(thm)], [c_701])).
% 5.80/2.06  tff(c_2467, plain, (![D_292, B_293, B_294]: (m1_subset_1(D_292, k1_zfmisc_1(k2_zfmisc_1(B_293, B_294))) | ~r1_tarski(k1_relat_1(D_292), B_293) | ~m1_subset_1(D_292, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_569])).
% 5.80/2.06  tff(c_2563, plain, (![D_298]: (m1_subset_1(D_298, k1_zfmisc_1('#skF_4')) | ~r1_tarski(k1_relat_1(D_298), k1_relat_1('#skF_4')) | ~m1_subset_1(D_298, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_1781, c_2467])).
% 5.80/2.06  tff(c_2572, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1('#skF_4')) | ~r1_tarski(k1_xboole_0, k1_relat_1('#skF_4')) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_468, c_2563])).
% 5.80/2.06  tff(c_2586, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1('#skF_4')) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_2572])).
% 5.80/2.06  tff(c_2590, plain, (~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_2586])).
% 5.80/2.06  tff(c_2593, plain, (~r1_tarski(k1_xboole_0, k1_xboole_0)), inference(resolution, [status(thm)], [c_34, c_2590])).
% 5.80/2.06  tff(c_2597, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_2593])).
% 5.80/2.06  tff(c_2599, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitRight, [status(thm)], [c_2586])).
% 5.80/2.06  tff(c_2707, plain, (![A_300, A_301]: (k1_tarski(A_300)=A_301 | k1_tarski(A_300)=A_301 | k1_tarski(A_300)=A_301 | k1_xboole_0=A_301 | ~r1_tarski(A_301, k1_tarski(A_300)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_667])).
% 5.80/2.06  tff(c_4262, plain, (![A_367, B_368]: (k1_tarski(A_367)=k1_relat_1(B_368) | k1_relat_1(B_368)=k1_xboole_0 | ~v4_relat_1(B_368, k1_tarski(A_367)) | ~v1_relat_1(B_368))), inference(resolution, [status(thm)], [c_38, c_2707])).
% 5.80/2.06  tff(c_4312, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_370, c_4262])).
% 5.80/2.06  tff(c_4338, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_150, c_4312])).
% 5.80/2.06  tff(c_4339, plain, (k1_relat_1('#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_727, c_4338])).
% 5.80/2.06  tff(c_4129, plain, (![D_362, B_363, B_364]: (r1_tarski(D_362, k2_zfmisc_1(B_363, B_364)) | ~r1_tarski(k1_relat_1(D_362), B_363) | ~m1_subset_1(D_362, k1_zfmisc_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_2467, c_32])).
% 5.80/2.06  tff(c_4165, plain, (![D_365, B_366]: (r1_tarski(D_365, k2_zfmisc_1(k1_relat_1(D_365), B_366)) | ~m1_subset_1(D_365, k1_zfmisc_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_6, c_4129])).
% 5.80/2.06  tff(c_50, plain, (![C_29, A_27, B_28]: (v4_relat_1(C_29, A_27) | ~m1_subset_1(C_29, k1_zfmisc_1(k2_zfmisc_1(A_27, B_28))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 5.80/2.06  tff(c_611, plain, (![B_130]: (v4_relat_1('#skF_4', B_130) | ~r1_tarski(k1_relat_1('#skF_4'), B_130))), inference(resolution, [status(thm)], [c_588, c_50])).
% 5.80/2.06  tff(c_4239, plain, (![B_366]: (v4_relat_1('#skF_4', k2_zfmisc_1(k1_relat_1(k1_relat_1('#skF_4')), B_366)) | ~m1_subset_1(k1_relat_1('#skF_4'), k1_zfmisc_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_4165, c_611])).
% 5.80/2.06  tff(c_4252, plain, (~m1_subset_1(k1_relat_1('#skF_4'), k1_zfmisc_1(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_4239])).
% 5.80/2.06  tff(c_4340, plain, (~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_4339, c_4252])).
% 5.80/2.06  tff(c_4362, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2599, c_4340])).
% 5.80/2.06  tff(c_4364, plain, (m1_subset_1(k1_relat_1('#skF_4'), k1_zfmisc_1(k1_xboole_0))), inference(splitRight, [status(thm)], [c_4239])).
% 5.80/2.06  tff(c_4378, plain, (r1_tarski(k1_relat_1('#skF_4'), k1_xboole_0)), inference(resolution, [status(thm)], [c_4364, c_32])).
% 5.80/2.06  tff(c_4387, plain, $false, inference(negUnitSimplification, [status(thm)], [c_630, c_4378])).
% 5.80/2.06  tff(c_4388, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_507])).
% 5.80/2.06  tff(c_4423, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_40, c_4388])).
% 5.80/2.06  tff(c_4427, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_150, c_4423])).
% 5.80/2.06  tff(c_4428, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_xboole_0))), inference(splitRight, [status(thm)], [c_608])).
% 5.80/2.06  tff(c_4457, plain, (r1_tarski('#skF_4', k1_xboole_0)), inference(resolution, [status(thm)], [c_4428, c_32])).
% 5.80/2.06  tff(c_4491, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_4457, c_226])).
% 5.80/2.06  tff(c_4518, plain, (![A_3]: (r1_tarski('#skF_4', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_4491, c_8])).
% 5.80/2.06  tff(c_42, plain, (![A_21]: (k9_relat_1(k1_xboole_0, A_21)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_76])).
% 5.80/2.06  tff(c_4515, plain, (![A_21]: (k9_relat_1('#skF_4', A_21)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4491, c_4491, c_42])).
% 5.80/2.06  tff(c_4767, plain, (~r1_tarski('#skF_4', k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_4515, c_493])).
% 5.80/2.06  tff(c_4770, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4518, c_4767])).
% 5.80/2.06  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.80/2.06  
% 5.80/2.06  Inference rules
% 5.80/2.06  ----------------------
% 5.80/2.06  #Ref     : 0
% 5.80/2.06  #Sup     : 1002
% 5.80/2.06  #Fact    : 0
% 5.80/2.06  #Define  : 0
% 5.80/2.06  #Split   : 11
% 5.80/2.06  #Chain   : 0
% 5.80/2.06  #Close   : 0
% 5.80/2.06  
% 5.80/2.06  Ordering : KBO
% 5.80/2.06  
% 5.80/2.06  Simplification rules
% 5.80/2.06  ----------------------
% 5.80/2.06  #Subsume      : 165
% 5.80/2.06  #Demod        : 1143
% 5.80/2.06  #Tautology    : 520
% 5.80/2.06  #SimpNegUnit  : 6
% 5.80/2.06  #BackRed      : 67
% 5.80/2.06  
% 5.80/2.06  #Partial instantiations: 0
% 5.80/2.06  #Strategies tried      : 1
% 5.80/2.06  
% 5.80/2.06  Timing (in seconds)
% 5.80/2.06  ----------------------
% 5.80/2.07  Preprocessing        : 0.32
% 5.80/2.07  Parsing              : 0.17
% 5.80/2.07  CNF conversion       : 0.02
% 5.80/2.07  Main loop            : 0.99
% 5.80/2.07  Inferencing          : 0.32
% 5.80/2.07  Reduction            : 0.37
% 5.80/2.07  Demodulation         : 0.27
% 5.80/2.07  BG Simplification    : 0.03
% 5.80/2.07  Subsumption          : 0.19
% 5.80/2.07  Abstraction          : 0.04
% 5.80/2.07  MUC search           : 0.00
% 5.80/2.07  Cooper               : 0.00
% 5.80/2.07  Total                : 1.35
% 5.80/2.07  Index Insertion      : 0.00
% 5.80/2.07  Index Deletion       : 0.00
% 5.80/2.07  Index Matching       : 0.00
% 5.80/2.07  BG Taut test         : 0.00
%------------------------------------------------------------------------------
