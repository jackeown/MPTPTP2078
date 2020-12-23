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
% DateTime   : Thu Dec  3 10:14:26 EST 2020

% Result     : Theorem 3.69s
% Output     : CNFRefutation 3.69s
% Verified   : 
% Statistics : Number of formulae       :  110 (1211 expanded)
%              Number of leaves         :   46 ( 454 expanded)
%              Depth                    :   20
%              Number of atoms          :  177 (3044 expanded)
%              Number of equality atoms :   64 (1219 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k11_relat_1,type,(
    k11_relat_1: ( $i * $i ) > $i )).

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

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_151,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_tarski(A),B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => k2_relset_1(k1_tarski(A),B,C) = k1_tarski(k1_funct_1(C,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_funct_2)).

tff(f_97,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_107,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_129,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( ( B = k1_xboole_0
           => A = k1_xboole_0 )
         => ( v1_funct_2(C,A,B)
          <=> A = k1_relset_1(A,B,C) ) )
        & ( B = k1_xboole_0
         => ( A = k1_xboole_0
            | ( v1_funct_2(C,A,B)
            <=> C = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_60,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] : k11_relat_1(A,B) = k9_relat_1(A,k1_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_relat_1)).

tff(f_78,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_85,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r2_hidden(A,k1_relat_1(B))
      <=> k11_relat_1(B,A) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t205_relat_1)).

tff(f_93,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => k11_relat_1(B,A) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_funct_1)).

tff(f_111,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_139,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_41,axiom,(
    ! [A] : ~ v1_xboole_0(k1_tarski(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_xboole_0)).

tff(f_103,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_80,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_161,plain,(
    ! [C_60,A_61,B_62] :
      ( v1_relat_1(C_60)
      | ~ m1_subset_1(C_60,k1_zfmisc_1(k2_zfmisc_1(A_61,B_62))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_173,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_80,c_161])).

tff(c_84,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_20,plain,(
    ! [A_10] : k2_zfmisc_1(A_10,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_78,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_82,plain,(
    v1_funct_2('#skF_3',k1_tarski('#skF_1'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_367,plain,(
    ! [A_115,B_116,C_117] :
      ( k1_relset_1(A_115,B_116,C_117) = k1_relat_1(C_117)
      | ~ m1_subset_1(C_117,k1_zfmisc_1(k2_zfmisc_1(A_115,B_116))) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_385,plain,(
    k1_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_80,c_367])).

tff(c_518,plain,(
    ! [B_138,A_139,C_140] :
      ( k1_xboole_0 = B_138
      | k1_relset_1(A_139,B_138,C_140) = A_139
      | ~ v1_funct_2(C_140,A_139,B_138)
      | ~ m1_subset_1(C_140,k1_zfmisc_1(k2_zfmisc_1(A_139,B_138))) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_524,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_3') = k1_tarski('#skF_1')
    | ~ v1_funct_2('#skF_3',k1_tarski('#skF_1'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_80,c_518])).

tff(c_538,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_tarski('#skF_1') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_385,c_524])).

tff(c_539,plain,(
    k1_tarski('#skF_1') = k1_relat_1('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_538])).

tff(c_28,plain,(
    ! [A_16,B_18] :
      ( k9_relat_1(A_16,k1_tarski(B_18)) = k11_relat_1(A_16,B_18)
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_661,plain,(
    ! [A_149] :
      ( k9_relat_1(A_149,k1_relat_1('#skF_3')) = k11_relat_1(A_149,'#skF_1')
      | ~ v1_relat_1(A_149) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_539,c_28])).

tff(c_40,plain,(
    ! [A_25] :
      ( k9_relat_1(A_25,k1_relat_1(A_25)) = k2_relat_1(A_25)
      | ~ v1_relat_1(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_668,plain,
    ( k11_relat_1('#skF_3','#skF_1') = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_661,c_40])).

tff(c_678,plain,(
    k11_relat_1('#skF_3','#skF_1') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_173,c_173,c_668])).

tff(c_42,plain,(
    ! [A_26,B_27] :
      ( r2_hidden(A_26,k1_relat_1(B_27))
      | k11_relat_1(B_27,A_26) = k1_xboole_0
      | ~ v1_relat_1(B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_411,plain,(
    ! [B_124,A_125] :
      ( k1_tarski(k1_funct_1(B_124,A_125)) = k11_relat_1(B_124,A_125)
      | ~ r2_hidden(A_125,k1_relat_1(B_124))
      | ~ v1_funct_1(B_124)
      | ~ v1_relat_1(B_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_688,plain,(
    ! [B_152,A_153] :
      ( k1_tarski(k1_funct_1(B_152,A_153)) = k11_relat_1(B_152,A_153)
      | ~ v1_funct_1(B_152)
      | k11_relat_1(B_152,A_153) = k1_xboole_0
      | ~ v1_relat_1(B_152) ) ),
    inference(resolution,[status(thm)],[c_42,c_411])).

tff(c_323,plain,(
    ! [A_106,B_107,C_108] :
      ( k2_relset_1(A_106,B_107,C_108) = k2_relat_1(C_108)
      | ~ m1_subset_1(C_108,k1_zfmisc_1(k2_zfmisc_1(A_106,B_107))) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_341,plain,(
    k2_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_80,c_323])).

tff(c_76,plain,(
    k2_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_3') != k1_tarski(k1_funct_1('#skF_3','#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_343,plain,(
    k1_tarski(k1_funct_1('#skF_3','#skF_1')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_341,c_76])).

tff(c_694,plain,
    ( k11_relat_1('#skF_3','#skF_1') != k2_relat_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | k11_relat_1('#skF_3','#skF_1') = k1_xboole_0
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_688,c_343])).

tff(c_705,plain,(
    k2_relat_1('#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_173,c_678,c_84,c_678,c_694])).

tff(c_70,plain,(
    ! [A_45] :
      ( m1_subset_1(A_45,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_45),k2_relat_1(A_45))))
      | ~ v1_funct_1(A_45)
      | ~ v1_relat_1(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_725,plain,
    ( m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k1_xboole_0)))
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_705,c_70])).

tff(c_749,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_173,c_84,c_20,c_725])).

tff(c_72,plain,(
    ! [A_45] :
      ( v1_funct_2(A_45,k1_relat_1(A_45),k2_relat_1(A_45))
      | ~ v1_funct_1(A_45)
      | ~ v1_relat_1(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_728,plain,
    ( v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k1_xboole_0)
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_705,c_72])).

tff(c_751,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_173,c_84,c_728])).

tff(c_60,plain,(
    ! [C_44,A_42] :
      ( k1_xboole_0 = C_44
      | ~ v1_funct_2(C_44,A_42,k1_xboole_0)
      | k1_xboole_0 = A_42
      | ~ m1_subset_1(C_44,k1_zfmisc_1(k2_zfmisc_1(A_42,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_89,plain,(
    ! [C_44,A_42] :
      ( k1_xboole_0 = C_44
      | ~ v1_funct_2(C_44,A_42,k1_xboole_0)
      | k1_xboole_0 = A_42
      | ~ m1_subset_1(C_44,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_60])).

tff(c_811,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_3') = k1_xboole_0
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_751,c_89])).

tff(c_814,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_749,c_811])).

tff(c_841,plain,(
    k1_relat_1('#skF_3') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_814])).

tff(c_16,plain,(
    ! [A_9] : ~ v1_xboole_0(k1_tarski(A_9)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_554,plain,(
    ~ v1_xboole_0(k1_relat_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_539,c_16])).

tff(c_849,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_841,c_554])).

tff(c_856,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_849])).

tff(c_857,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_814])).

tff(c_858,plain,(
    k1_relat_1('#skF_3') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_814])).

tff(c_963,plain,(
    k1_relat_1('#skF_3') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_857,c_858])).

tff(c_190,plain,(
    ! [C_66,A_67,B_68] :
      ( v4_relat_1(C_66,A_67)
      | ~ m1_subset_1(C_66,k1_zfmisc_1(k2_zfmisc_1(A_67,B_68))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_203,plain,(
    ! [C_66,A_10] :
      ( v4_relat_1(C_66,A_10)
      | ~ m1_subset_1(C_66,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_190])).

tff(c_791,plain,(
    ! [A_10] : v4_relat_1('#skF_3',A_10) ),
    inference(resolution,[status(thm)],[c_749,c_203])).

tff(c_22,plain,(
    ! [B_11] : k2_zfmisc_1(k1_xboole_0,B_11) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_220,plain,(
    ! [C_75,B_76,A_77] :
      ( v5_relat_1(C_75,B_76)
      | ~ m1_subset_1(C_75,k1_zfmisc_1(k2_zfmisc_1(A_77,B_76))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_230,plain,(
    ! [C_75,B_11] :
      ( v5_relat_1(C_75,B_11)
      | ~ m1_subset_1(C_75,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_220])).

tff(c_790,plain,(
    ! [B_11] : v5_relat_1('#skF_3',B_11) ),
    inference(resolution,[status(thm)],[c_749,c_230])).

tff(c_867,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_857,c_705])).

tff(c_36,plain,(
    ! [B_22,A_21] :
      ( r1_tarski(k2_relat_1(B_22),A_21)
      | ~ v5_relat_1(B_22,A_21)
      | ~ v1_relat_1(B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_935,plain,(
    ! [A_21] :
      ( r1_tarski('#skF_3',A_21)
      | ~ v5_relat_1('#skF_3',A_21)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_867,c_36])).

tff(c_964,plain,(
    ! [A_162] : r1_tarski('#skF_3',A_162) ),
    inference(demodulation,[status(thm),theory(equality)],[c_173,c_790,c_935])).

tff(c_259,plain,(
    ! [B_85,A_86] :
      ( r1_tarski(k1_relat_1(B_85),A_86)
      | ~ v4_relat_1(B_85,A_86)
      | ~ v1_relat_1(B_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_266,plain,(
    ! [B_85,A_86] :
      ( k1_relat_1(B_85) = A_86
      | ~ r1_tarski(A_86,k1_relat_1(B_85))
      | ~ v4_relat_1(B_85,A_86)
      | ~ v1_relat_1(B_85) ) ),
    inference(resolution,[status(thm)],[c_259,c_4])).

tff(c_1278,plain,(
    ! [B_193] :
      ( k1_relat_1(B_193) = '#skF_3'
      | ~ v4_relat_1(B_193,'#skF_3')
      | ~ v1_relat_1(B_193) ) ),
    inference(resolution,[status(thm)],[c_964,c_266])).

tff(c_1282,plain,
    ( k1_relat_1('#skF_3') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_791,c_1278])).

tff(c_1285,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_173,c_1282])).

tff(c_1287,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_963,c_1285])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.11  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.32  % Computer   : n003.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % DateTime   : Tue Dec  1 19:04:42 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.17/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.69/1.64  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.69/1.65  
% 3.69/1.65  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.69/1.65  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.69/1.65  
% 3.69/1.65  %Foreground sorts:
% 3.69/1.65  
% 3.69/1.65  
% 3.69/1.65  %Background operators:
% 3.69/1.65  
% 3.69/1.65  
% 3.69/1.65  %Foreground operators:
% 3.69/1.65  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.69/1.65  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.69/1.65  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.69/1.65  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.69/1.65  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.69/1.65  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.69/1.65  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.69/1.65  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.69/1.65  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.69/1.65  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.69/1.65  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.69/1.65  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 3.69/1.65  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.69/1.65  tff('#skF_2', type, '#skF_2': $i).
% 3.69/1.65  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.69/1.65  tff('#skF_3', type, '#skF_3': $i).
% 3.69/1.65  tff('#skF_1', type, '#skF_1': $i).
% 3.69/1.65  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.69/1.65  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.69/1.65  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.69/1.65  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.69/1.65  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.69/1.65  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.69/1.65  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.69/1.65  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.69/1.65  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.69/1.65  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.69/1.65  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.69/1.65  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.69/1.65  
% 3.69/1.67  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.69/1.67  tff(f_151, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => (k2_relset_1(k1_tarski(A), B, C) = k1_tarski(k1_funct_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_funct_2)).
% 3.69/1.67  tff(f_97, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.69/1.67  tff(f_47, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 3.69/1.67  tff(f_107, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.69/1.67  tff(f_129, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 3.69/1.67  tff(f_60, axiom, (![A]: (v1_relat_1(A) => (![B]: (k11_relat_1(A, B) = k9_relat_1(A, k1_tarski(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d16_relat_1)).
% 3.69/1.67  tff(f_78, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_relat_1)).
% 3.69/1.67  tff(f_85, axiom, (![A, B]: (v1_relat_1(B) => (r2_hidden(A, k1_relat_1(B)) <=> ~(k11_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t205_relat_1)).
% 3.69/1.67  tff(f_93, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => (k11_relat_1(B, A) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t117_funct_1)).
% 3.69/1.67  tff(f_111, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.69/1.67  tff(f_139, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_funct_2)).
% 3.69/1.67  tff(f_41, axiom, (![A]: ~v1_xboole_0(k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_xboole_0)).
% 3.69/1.67  tff(f_103, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.69/1.67  tff(f_72, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 3.69/1.67  tff(f_66, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 3.69/1.67  tff(f_32, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.69/1.67  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 3.69/1.67  tff(c_80, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_151])).
% 3.69/1.67  tff(c_161, plain, (![C_60, A_61, B_62]: (v1_relat_1(C_60) | ~m1_subset_1(C_60, k1_zfmisc_1(k2_zfmisc_1(A_61, B_62))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.69/1.67  tff(c_173, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_80, c_161])).
% 3.69/1.67  tff(c_84, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_151])).
% 3.69/1.67  tff(c_20, plain, (![A_10]: (k2_zfmisc_1(A_10, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.69/1.67  tff(c_78, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_151])).
% 3.69/1.67  tff(c_82, plain, (v1_funct_2('#skF_3', k1_tarski('#skF_1'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_151])).
% 3.69/1.67  tff(c_367, plain, (![A_115, B_116, C_117]: (k1_relset_1(A_115, B_116, C_117)=k1_relat_1(C_117) | ~m1_subset_1(C_117, k1_zfmisc_1(k2_zfmisc_1(A_115, B_116))))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.69/1.67  tff(c_385, plain, (k1_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_80, c_367])).
% 3.69/1.67  tff(c_518, plain, (![B_138, A_139, C_140]: (k1_xboole_0=B_138 | k1_relset_1(A_139, B_138, C_140)=A_139 | ~v1_funct_2(C_140, A_139, B_138) | ~m1_subset_1(C_140, k1_zfmisc_1(k2_zfmisc_1(A_139, B_138))))), inference(cnfTransformation, [status(thm)], [f_129])).
% 3.69/1.67  tff(c_524, plain, (k1_xboole_0='#skF_2' | k1_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_3')=k1_tarski('#skF_1') | ~v1_funct_2('#skF_3', k1_tarski('#skF_1'), '#skF_2')), inference(resolution, [status(thm)], [c_80, c_518])).
% 3.69/1.67  tff(c_538, plain, (k1_xboole_0='#skF_2' | k1_tarski('#skF_1')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_385, c_524])).
% 3.69/1.67  tff(c_539, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_78, c_538])).
% 3.69/1.67  tff(c_28, plain, (![A_16, B_18]: (k9_relat_1(A_16, k1_tarski(B_18))=k11_relat_1(A_16, B_18) | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.69/1.67  tff(c_661, plain, (![A_149]: (k9_relat_1(A_149, k1_relat_1('#skF_3'))=k11_relat_1(A_149, '#skF_1') | ~v1_relat_1(A_149))), inference(superposition, [status(thm), theory('equality')], [c_539, c_28])).
% 3.69/1.67  tff(c_40, plain, (![A_25]: (k9_relat_1(A_25, k1_relat_1(A_25))=k2_relat_1(A_25) | ~v1_relat_1(A_25))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.69/1.67  tff(c_668, plain, (k11_relat_1('#skF_3', '#skF_1')=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_661, c_40])).
% 3.69/1.67  tff(c_678, plain, (k11_relat_1('#skF_3', '#skF_1')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_173, c_173, c_668])).
% 3.69/1.67  tff(c_42, plain, (![A_26, B_27]: (r2_hidden(A_26, k1_relat_1(B_27)) | k11_relat_1(B_27, A_26)=k1_xboole_0 | ~v1_relat_1(B_27))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.69/1.67  tff(c_411, plain, (![B_124, A_125]: (k1_tarski(k1_funct_1(B_124, A_125))=k11_relat_1(B_124, A_125) | ~r2_hidden(A_125, k1_relat_1(B_124)) | ~v1_funct_1(B_124) | ~v1_relat_1(B_124))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.69/1.67  tff(c_688, plain, (![B_152, A_153]: (k1_tarski(k1_funct_1(B_152, A_153))=k11_relat_1(B_152, A_153) | ~v1_funct_1(B_152) | k11_relat_1(B_152, A_153)=k1_xboole_0 | ~v1_relat_1(B_152))), inference(resolution, [status(thm)], [c_42, c_411])).
% 3.69/1.67  tff(c_323, plain, (![A_106, B_107, C_108]: (k2_relset_1(A_106, B_107, C_108)=k2_relat_1(C_108) | ~m1_subset_1(C_108, k1_zfmisc_1(k2_zfmisc_1(A_106, B_107))))), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.69/1.67  tff(c_341, plain, (k2_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_80, c_323])).
% 3.69/1.67  tff(c_76, plain, (k2_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_3')!=k1_tarski(k1_funct_1('#skF_3', '#skF_1'))), inference(cnfTransformation, [status(thm)], [f_151])).
% 3.69/1.67  tff(c_343, plain, (k1_tarski(k1_funct_1('#skF_3', '#skF_1'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_341, c_76])).
% 3.69/1.67  tff(c_694, plain, (k11_relat_1('#skF_3', '#skF_1')!=k2_relat_1('#skF_3') | ~v1_funct_1('#skF_3') | k11_relat_1('#skF_3', '#skF_1')=k1_xboole_0 | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_688, c_343])).
% 3.69/1.67  tff(c_705, plain, (k2_relat_1('#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_173, c_678, c_84, c_678, c_694])).
% 3.69/1.67  tff(c_70, plain, (![A_45]: (m1_subset_1(A_45, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_45), k2_relat_1(A_45)))) | ~v1_funct_1(A_45) | ~v1_relat_1(A_45))), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.69/1.67  tff(c_725, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k1_xboole_0))) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_705, c_70])).
% 3.69/1.67  tff(c_749, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_173, c_84, c_20, c_725])).
% 3.69/1.67  tff(c_72, plain, (![A_45]: (v1_funct_2(A_45, k1_relat_1(A_45), k2_relat_1(A_45)) | ~v1_funct_1(A_45) | ~v1_relat_1(A_45))), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.69/1.67  tff(c_728, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k1_xboole_0) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_705, c_72])).
% 3.69/1.67  tff(c_751, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_173, c_84, c_728])).
% 3.69/1.67  tff(c_60, plain, (![C_44, A_42]: (k1_xboole_0=C_44 | ~v1_funct_2(C_44, A_42, k1_xboole_0) | k1_xboole_0=A_42 | ~m1_subset_1(C_44, k1_zfmisc_1(k2_zfmisc_1(A_42, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_129])).
% 3.69/1.67  tff(c_89, plain, (![C_44, A_42]: (k1_xboole_0=C_44 | ~v1_funct_2(C_44, A_42, k1_xboole_0) | k1_xboole_0=A_42 | ~m1_subset_1(C_44, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_60])).
% 3.69/1.67  tff(c_811, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_3')=k1_xboole_0 | ~m1_subset_1('#skF_3', k1_zfmisc_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_751, c_89])).
% 3.69/1.67  tff(c_814, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_749, c_811])).
% 3.69/1.67  tff(c_841, plain, (k1_relat_1('#skF_3')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_814])).
% 3.69/1.67  tff(c_16, plain, (![A_9]: (~v1_xboole_0(k1_tarski(A_9)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.69/1.67  tff(c_554, plain, (~v1_xboole_0(k1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_539, c_16])).
% 3.69/1.67  tff(c_849, plain, (~v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_841, c_554])).
% 3.69/1.67  tff(c_856, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_849])).
% 3.69/1.67  tff(c_857, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_814])).
% 3.69/1.67  tff(c_858, plain, (k1_relat_1('#skF_3')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_814])).
% 3.69/1.67  tff(c_963, plain, (k1_relat_1('#skF_3')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_857, c_858])).
% 3.69/1.67  tff(c_190, plain, (![C_66, A_67, B_68]: (v4_relat_1(C_66, A_67) | ~m1_subset_1(C_66, k1_zfmisc_1(k2_zfmisc_1(A_67, B_68))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.69/1.67  tff(c_203, plain, (![C_66, A_10]: (v4_relat_1(C_66, A_10) | ~m1_subset_1(C_66, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_190])).
% 3.69/1.67  tff(c_791, plain, (![A_10]: (v4_relat_1('#skF_3', A_10))), inference(resolution, [status(thm)], [c_749, c_203])).
% 3.69/1.67  tff(c_22, plain, (![B_11]: (k2_zfmisc_1(k1_xboole_0, B_11)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.69/1.67  tff(c_220, plain, (![C_75, B_76, A_77]: (v5_relat_1(C_75, B_76) | ~m1_subset_1(C_75, k1_zfmisc_1(k2_zfmisc_1(A_77, B_76))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.69/1.67  tff(c_230, plain, (![C_75, B_11]: (v5_relat_1(C_75, B_11) | ~m1_subset_1(C_75, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_220])).
% 3.69/1.67  tff(c_790, plain, (![B_11]: (v5_relat_1('#skF_3', B_11))), inference(resolution, [status(thm)], [c_749, c_230])).
% 3.69/1.67  tff(c_867, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_857, c_705])).
% 3.69/1.67  tff(c_36, plain, (![B_22, A_21]: (r1_tarski(k2_relat_1(B_22), A_21) | ~v5_relat_1(B_22, A_21) | ~v1_relat_1(B_22))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.69/1.67  tff(c_935, plain, (![A_21]: (r1_tarski('#skF_3', A_21) | ~v5_relat_1('#skF_3', A_21) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_867, c_36])).
% 3.69/1.67  tff(c_964, plain, (![A_162]: (r1_tarski('#skF_3', A_162))), inference(demodulation, [status(thm), theory('equality')], [c_173, c_790, c_935])).
% 3.69/1.67  tff(c_259, plain, (![B_85, A_86]: (r1_tarski(k1_relat_1(B_85), A_86) | ~v4_relat_1(B_85, A_86) | ~v1_relat_1(B_85))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.69/1.67  tff(c_4, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.69/1.67  tff(c_266, plain, (![B_85, A_86]: (k1_relat_1(B_85)=A_86 | ~r1_tarski(A_86, k1_relat_1(B_85)) | ~v4_relat_1(B_85, A_86) | ~v1_relat_1(B_85))), inference(resolution, [status(thm)], [c_259, c_4])).
% 3.69/1.67  tff(c_1278, plain, (![B_193]: (k1_relat_1(B_193)='#skF_3' | ~v4_relat_1(B_193, '#skF_3') | ~v1_relat_1(B_193))), inference(resolution, [status(thm)], [c_964, c_266])).
% 3.69/1.67  tff(c_1282, plain, (k1_relat_1('#skF_3')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_791, c_1278])).
% 3.69/1.67  tff(c_1285, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_173, c_1282])).
% 3.69/1.67  tff(c_1287, plain, $false, inference(negUnitSimplification, [status(thm)], [c_963, c_1285])).
% 3.69/1.67  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.69/1.67  
% 3.69/1.67  Inference rules
% 3.69/1.67  ----------------------
% 3.69/1.67  #Ref     : 0
% 3.69/1.67  #Sup     : 245
% 3.69/1.67  #Fact    : 0
% 3.69/1.67  #Define  : 0
% 3.69/1.67  #Split   : 2
% 3.69/1.67  #Chain   : 0
% 3.69/1.67  #Close   : 0
% 3.69/1.67  
% 3.69/1.67  Ordering : KBO
% 3.69/1.67  
% 3.69/1.67  Simplification rules
% 3.69/1.67  ----------------------
% 3.69/1.67  #Subsume      : 29
% 3.69/1.67  #Demod        : 270
% 3.69/1.67  #Tautology    : 172
% 3.69/1.67  #SimpNegUnit  : 6
% 3.69/1.67  #BackRed      : 59
% 3.69/1.67  
% 3.69/1.67  #Partial instantiations: 0
% 3.69/1.67  #Strategies tried      : 1
% 3.69/1.67  
% 3.69/1.67  Timing (in seconds)
% 3.69/1.67  ----------------------
% 3.69/1.68  Preprocessing        : 0.52
% 3.69/1.68  Parsing              : 0.30
% 3.69/1.68  CNF conversion       : 0.03
% 3.69/1.68  Main loop            : 0.45
% 3.69/1.68  Inferencing          : 0.15
% 3.69/1.68  Reduction            : 0.16
% 3.69/1.68  Demodulation         : 0.11
% 3.69/1.68  BG Simplification    : 0.03
% 3.69/1.68  Subsumption          : 0.08
% 3.69/1.68  Abstraction          : 0.02
% 3.69/1.68  MUC search           : 0.00
% 3.69/1.68  Cooper               : 0.00
% 3.69/1.68  Total                : 1.01
% 3.69/1.68  Index Insertion      : 0.00
% 3.69/1.68  Index Deletion       : 0.00
% 3.69/1.68  Index Matching       : 0.00
% 3.69/1.68  BG Taut test         : 0.00
%------------------------------------------------------------------------------
