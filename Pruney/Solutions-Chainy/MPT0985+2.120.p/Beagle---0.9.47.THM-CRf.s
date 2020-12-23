%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:45 EST 2020

% Result     : Theorem 4.74s
% Output     : CNFRefutation 4.82s
% Verified   : 
% Statistics : Number of formulae       :  186 (1027 expanded)
%              Number of leaves         :   44 ( 355 expanded)
%              Depth                    :   13
%              Number of atoms          :  322 (2842 expanded)
%              Number of equality atoms :   89 ( 619 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v5_ordinal1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v5_ordinal1,type,(
    v5_ordinal1: $i > $o )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

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

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_156,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ( v2_funct_1(C)
            & k2_relset_1(A,B,C) = B )
         => ( v1_funct_1(k2_funct_1(C))
            & v1_funct_2(k2_funct_1(C),B,A)
            & m1_subset_1(k2_funct_1(C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).

tff(f_91,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_34,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_99,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_77,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_67,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_95,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_117,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_48,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_139,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(k2_relat_1(B),A)
       => ( v1_funct_1(B)
          & v1_funct_2(B,k1_relat_1(B),A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_127,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_42,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_58,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_59,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_79,axiom,(
    ! [A] : k2_funct_1(k6_relat_1(A)) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_funct_1)).

tff(c_82,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_180,plain,(
    ! [C_41,A_42,B_43] :
      ( v1_relat_1(C_41)
      | ~ m1_subset_1(C_41,k1_zfmisc_1(k2_zfmisc_1(A_42,B_43))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_188,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_82,c_180])).

tff(c_86,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_4,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_80,plain,(
    v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_78,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_1773,plain,(
    ! [A_163,B_164,C_165] :
      ( k2_relset_1(A_163,B_164,C_165) = k2_relat_1(C_165)
      | ~ m1_subset_1(C_165,k1_zfmisc_1(k2_zfmisc_1(A_163,B_164))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_1782,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_82,c_1773])).

tff(c_1792,plain,(
    k2_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_1782])).

tff(c_34,plain,(
    ! [A_12] :
      ( k1_relat_1(k2_funct_1(A_12)) = k2_relat_1(A_12)
      | ~ v2_funct_1(A_12)
      | ~ v1_funct_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_10,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_28,plain,(
    ! [A_11] :
      ( v1_funct_1(k2_funct_1(A_11))
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_76,plain,
    ( ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_213,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_76])).

tff(c_216,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_213])).

tff(c_220,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_188,c_86,c_216])).

tff(c_221,plain,
    ( ~ v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_2')
    | ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_391,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_221])).

tff(c_84,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_458,plain,(
    ! [A_79,B_80,C_81] :
      ( k1_relset_1(A_79,B_80,C_81) = k1_relat_1(C_81)
      | ~ m1_subset_1(C_81,k1_zfmisc_1(k2_zfmisc_1(A_79,B_80))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_468,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_82,c_458])).

tff(c_761,plain,(
    ! [B_106,A_107,C_108] :
      ( k1_xboole_0 = B_106
      | k1_relset_1(A_107,B_106,C_108) = A_107
      | ~ v1_funct_2(C_108,A_107,B_106)
      | ~ m1_subset_1(C_108,k1_zfmisc_1(k2_zfmisc_1(A_107,B_106))) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_773,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_82,c_761])).

tff(c_787,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_468,c_773])).

tff(c_789,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_787])).

tff(c_32,plain,(
    ! [A_12] :
      ( k2_relat_1(k2_funct_1(A_12)) = k1_relat_1(A_12)
      | ~ v2_funct_1(A_12)
      | ~ v1_funct_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_30,plain,(
    ! [A_11] :
      ( v1_relat_1(k2_funct_1(A_11))
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_222,plain,(
    v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_16,plain,(
    ! [A_6] : k2_zfmisc_1(A_6,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_691,plain,(
    ! [B_100,A_101] :
      ( m1_subset_1(B_100,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_100),A_101)))
      | ~ r1_tarski(k2_relat_1(B_100),A_101)
      | ~ v1_funct_1(B_100)
      | ~ v1_relat_1(B_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_20,plain,(
    ! [C_10,B_9,A_8] :
      ( ~ v1_xboole_0(C_10)
      | ~ m1_subset_1(B_9,k1_zfmisc_1(C_10))
      | ~ r2_hidden(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_937,plain,(
    ! [B_119,A_120,A_121] :
      ( ~ v1_xboole_0(k2_zfmisc_1(k1_relat_1(B_119),A_120))
      | ~ r2_hidden(A_121,B_119)
      | ~ r1_tarski(k2_relat_1(B_119),A_120)
      | ~ v1_funct_1(B_119)
      | ~ v1_relat_1(B_119) ) ),
    inference(resolution,[status(thm)],[c_691,c_20])).

tff(c_944,plain,(
    ! [A_121,B_119] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(A_121,B_119)
      | ~ r1_tarski(k2_relat_1(B_119),k1_xboole_0)
      | ~ v1_funct_1(B_119)
      | ~ v1_relat_1(B_119) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_937])).

tff(c_953,plain,(
    ! [A_122,B_123] :
      ( ~ r2_hidden(A_122,B_123)
      | ~ r1_tarski(k2_relat_1(B_123),k1_xboole_0)
      | ~ v1_funct_1(B_123)
      | ~ v1_relat_1(B_123) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_944])).

tff(c_957,plain,(
    ! [A_124] :
      ( ~ r1_tarski(k2_relat_1(A_124),k1_xboole_0)
      | ~ v1_funct_1(A_124)
      | ~ v1_relat_1(A_124)
      | k1_xboole_0 = A_124 ) ),
    inference(resolution,[status(thm)],[c_4,c_953])).

tff(c_972,plain,(
    ! [A_125] :
      ( ~ r1_tarski(k1_relat_1(A_125),k1_xboole_0)
      | ~ v1_funct_1(k2_funct_1(A_125))
      | ~ v1_relat_1(k2_funct_1(A_125))
      | k2_funct_1(A_125) = k1_xboole_0
      | ~ v2_funct_1(A_125)
      | ~ v1_funct_1(A_125)
      | ~ v1_relat_1(A_125) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_957])).

tff(c_975,plain,
    ( ~ r1_tarski('#skF_2',k1_xboole_0)
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | k2_funct_1('#skF_4') = k1_xboole_0
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_789,c_972])).

tff(c_983,plain,
    ( ~ r1_tarski('#skF_2',k1_xboole_0)
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | k2_funct_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_188,c_86,c_80,c_222,c_975])).

tff(c_986,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_983])).

tff(c_989,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_986])).

tff(c_993,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_188,c_86,c_989])).

tff(c_995,plain,(
    v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_983])).

tff(c_392,plain,(
    ! [A_68,B_69,C_70] :
      ( k2_relset_1(A_68,B_69,C_70) = k2_relat_1(C_70)
      | ~ m1_subset_1(C_70,k1_zfmisc_1(k2_zfmisc_1(A_68,B_69))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_395,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_82,c_392])).

tff(c_403,plain,(
    k2_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_395])).

tff(c_485,plain,(
    ! [A_85] :
      ( m1_subset_1(A_85,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_85),k2_relat_1(A_85))))
      | ~ v1_funct_1(A_85)
      | ~ v1_relat_1(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_1126,plain,(
    ! [A_131] :
      ( m1_subset_1(k2_funct_1(A_131),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_131),k2_relat_1(k2_funct_1(A_131)))))
      | ~ v1_funct_1(k2_funct_1(A_131))
      | ~ v1_relat_1(k2_funct_1(A_131))
      | ~ v2_funct_1(A_131)
      | ~ v1_funct_1(A_131)
      | ~ v1_relat_1(A_131) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_485])).

tff(c_1146,plain,
    ( m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3',k2_relat_1(k2_funct_1('#skF_4')))))
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_403,c_1126])).

tff(c_1175,plain,(
    m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3',k2_relat_1(k2_funct_1('#skF_4'))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_188,c_86,c_80,c_995,c_222,c_1146])).

tff(c_1203,plain,
    ( m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3',k1_relat_1('#skF_4'))))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_1175])).

tff(c_1215,plain,(
    m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_188,c_86,c_80,c_789,c_1203])).

tff(c_1217,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_391,c_1215])).

tff(c_1218,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_787])).

tff(c_746,plain,(
    ! [B_105] :
      ( m1_subset_1(B_105,k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski(k2_relat_1(B_105),k1_xboole_0)
      | ~ v1_funct_1(B_105)
      | ~ v1_relat_1(B_105) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_691])).

tff(c_749,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(k1_xboole_0))
    | ~ r1_tarski('#skF_3',k1_xboole_0)
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_403,c_746])).

tff(c_757,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(k1_xboole_0))
    | ~ r1_tarski('#skF_3',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_188,c_86,c_749])).

tff(c_760,plain,(
    ~ r1_tarski('#skF_3',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_757])).

tff(c_1221,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1218,c_760])).

tff(c_1257,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_1221])).

tff(c_1259,plain,(
    r1_tarski('#skF_3',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_757])).

tff(c_12,plain,(
    ! [A_5] : r1_tarski(k1_xboole_0,A_5) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_189,plain,(
    ! [B_44,A_45] :
      ( B_44 = A_45
      | ~ r1_tarski(B_44,A_45)
      | ~ r1_tarski(A_45,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_194,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ r1_tarski(A_5,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_12,c_189])).

tff(c_1293,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_1259,c_194])).

tff(c_1329,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1293,c_2])).

tff(c_1322,plain,(
    ! [A_6] : k2_zfmisc_1(A_6,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1293,c_1293,c_16])).

tff(c_499,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_3')))
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_403,c_485])).

tff(c_517,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_188,c_86,c_499])).

tff(c_536,plain,(
    ! [A_8] :
      ( ~ v1_xboole_0(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_3'))
      | ~ r2_hidden(A_8,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_517,c_20])).

tff(c_547,plain,(
    ~ v1_xboole_0(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_536])).

tff(c_1472,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1322,c_547])).

tff(c_1478,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1329,c_1472])).

tff(c_1481,plain,(
    ! [A_142] : ~ r2_hidden(A_142,'#skF_4') ),
    inference(splitRight,[status(thm)],[c_536])).

tff(c_1486,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_4,c_1481])).

tff(c_1511,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1486,c_2])).

tff(c_1504,plain,(
    ! [A_6] : k2_zfmisc_1(A_6,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1486,c_1486,c_16])).

tff(c_22,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1509,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1486,c_1486,c_22])).

tff(c_1555,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1509,c_403])).

tff(c_223,plain,(
    ! [C_48,B_49,A_50] :
      ( ~ v1_xboole_0(C_48)
      | ~ m1_subset_1(B_49,k1_zfmisc_1(C_48))
      | ~ r2_hidden(A_50,B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_226,plain,(
    ! [A_50] :
      ( ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3'))
      | ~ r2_hidden(A_50,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_82,c_223])).

tff(c_227,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_226])).

tff(c_1578,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1555,c_227])).

tff(c_1666,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1511,c_1504,c_1578])).

tff(c_1667,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_221])).

tff(c_1668,plain,(
    m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_221])).

tff(c_1677,plain,(
    ! [A_151,B_152,C_153] :
      ( k1_relset_1(A_151,B_152,C_153) = k1_relat_1(C_153)
      | ~ m1_subset_1(C_153,k1_zfmisc_1(k2_zfmisc_1(A_151,B_152))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_1690,plain,(
    k1_relset_1('#skF_3','#skF_2',k2_funct_1('#skF_4')) = k1_relat_1(k2_funct_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_1668,c_1677])).

tff(c_2117,plain,(
    ! [B_189,C_190,A_191] :
      ( k1_xboole_0 = B_189
      | v1_funct_2(C_190,A_191,B_189)
      | k1_relset_1(A_191,B_189,C_190) != A_191
      | ~ m1_subset_1(C_190,k1_zfmisc_1(k2_zfmisc_1(A_191,B_189))) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_2126,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_2')
    | k1_relset_1('#skF_3','#skF_2',k2_funct_1('#skF_4')) != '#skF_3' ),
    inference(resolution,[status(thm)],[c_1668,c_2117])).

tff(c_2139,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_2')
    | k1_relat_1(k2_funct_1('#skF_4')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1690,c_2126])).

tff(c_2140,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1(k2_funct_1('#skF_4')) != '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_1667,c_2139])).

tff(c_2145,plain,(
    k1_relat_1(k2_funct_1('#skF_4')) != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_2140])).

tff(c_2148,plain,
    ( k2_relat_1('#skF_4') != '#skF_3'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_2145])).

tff(c_2151,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_188,c_86,c_80,c_1792,c_2148])).

tff(c_2152,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_2140])).

tff(c_2186,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2152,c_2])).

tff(c_18,plain,(
    ! [B_7] : k2_zfmisc_1(k1_xboole_0,B_7) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_2178,plain,(
    ! [B_7] : k2_zfmisc_1('#skF_2',B_7) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2152,c_2152,c_18])).

tff(c_2350,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2178,c_227])).

tff(c_2354,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2186,c_2350])).

tff(c_2357,plain,(
    ! [A_195] : ~ r2_hidden(A_195,'#skF_4') ),
    inference(splitRight,[status(thm)],[c_226])).

tff(c_2362,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_4,c_2357])).

tff(c_2383,plain,(
    ! [A_5] : r1_tarski('#skF_4',A_5) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2362,c_12])).

tff(c_2385,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2362,c_2362,c_22])).

tff(c_24,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_2381,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2362,c_2362,c_24])).

tff(c_3161,plain,(
    ! [B_262,A_263] :
      ( v1_funct_2(B_262,k1_relat_1(B_262),A_263)
      | ~ r1_tarski(k2_relat_1(B_262),A_263)
      | ~ v1_funct_1(B_262)
      | ~ v1_relat_1(B_262) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_3170,plain,(
    ! [A_263] :
      ( v1_funct_2('#skF_4','#skF_4',A_263)
      | ~ r1_tarski(k2_relat_1('#skF_4'),A_263)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2381,c_3161])).

tff(c_3173,plain,(
    ! [A_263] : v1_funct_2('#skF_4','#skF_4',A_263) ),
    inference(demodulation,[status(thm),theory(equality)],[c_188,c_86,c_2383,c_2385,c_3170])).

tff(c_3035,plain,(
    ! [A_250,B_251,C_252] :
      ( k2_relset_1(A_250,B_251,C_252) = k2_relat_1(C_252)
      | ~ m1_subset_1(C_252,k1_zfmisc_1(k2_zfmisc_1(A_250,B_251))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_3050,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_82,c_3035])).

tff(c_3055,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_2385,c_3050])).

tff(c_26,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_133,plain,(
    ! [A_35] : k2_funct_1(k6_relat_1(A_35)) = k6_relat_1(A_35) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_142,plain,(
    k6_relat_1(k1_xboole_0) = k2_funct_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_133])).

tff(c_145,plain,(
    k2_funct_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_142])).

tff(c_2378,plain,(
    k2_funct_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2362,c_2362,c_145])).

tff(c_52,plain,(
    ! [A_24] :
      ( v1_funct_2(k1_xboole_0,A_24,k1_xboole_0)
      | k1_xboole_0 = A_24
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_24,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_89,plain,(
    ! [A_24] :
      ( v1_funct_2(k1_xboole_0,A_24,k1_xboole_0)
      | k1_xboole_0 = A_24
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_52])).

tff(c_2507,plain,(
    ! [A_24] :
      ( v1_funct_2('#skF_4',A_24,'#skF_4')
      | A_24 = '#skF_4'
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2362,c_2362,c_2362,c_2362,c_2362,c_89])).

tff(c_2508,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_2507])).

tff(c_2380,plain,(
    ! [A_6] : k2_zfmisc_1(A_6,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2362,c_2362,c_16])).

tff(c_2549,plain,(
    ! [A_208] :
      ( m1_subset_1(A_208,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_208),k2_relat_1(A_208))))
      | ~ v1_funct_1(A_208)
      | ~ v1_relat_1(A_208) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_2563,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_4')))
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2385,c_2549])).

tff(c_2570,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_188,c_86,c_2380,c_2381,c_2563])).

tff(c_2572,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2508,c_2570])).

tff(c_2574,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_2507])).

tff(c_2379,plain,(
    ! [B_7] : k2_zfmisc_1('#skF_4',B_7) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2362,c_2362,c_18])).

tff(c_2650,plain,(
    ! [A_216,B_217,C_218] :
      ( k2_relset_1(A_216,B_217,C_218) = k2_relat_1(C_218)
      | ~ m1_subset_1(C_218,k1_zfmisc_1(k2_zfmisc_1(A_216,B_217))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_2662,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_82,c_2650])).

tff(c_2665,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_2385,c_2662])).

tff(c_2396,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_221])).

tff(c_2436,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2378,c_2396])).

tff(c_2667,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2665,c_2436])).

tff(c_2674,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2574,c_2379,c_2667])).

tff(c_2675,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_221])).

tff(c_2715,plain,(
    ~ v1_funct_2('#skF_4','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2378,c_2675])).

tff(c_3059,plain,(
    ~ v1_funct_2('#skF_4','#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3055,c_2715])).

tff(c_3177,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3173,c_3059])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:47:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.74/1.82  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.82/1.84  
% 4.82/1.84  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.82/1.84  %$ v1_funct_2 > v5_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v5_ordinal1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 4.82/1.84  
% 4.82/1.84  %Foreground sorts:
% 4.82/1.84  
% 4.82/1.84  
% 4.82/1.84  %Background operators:
% 4.82/1.84  
% 4.82/1.84  
% 4.82/1.84  %Foreground operators:
% 4.82/1.84  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.82/1.84  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.82/1.84  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 4.82/1.84  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 4.82/1.84  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.82/1.84  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.82/1.84  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.82/1.84  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.82/1.84  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.82/1.84  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.82/1.84  tff(v5_ordinal1, type, v5_ordinal1: $i > $o).
% 4.82/1.84  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.82/1.84  tff('#skF_2', type, '#skF_2': $i).
% 4.82/1.84  tff('#skF_3', type, '#skF_3': $i).
% 4.82/1.84  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.82/1.84  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.82/1.84  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.82/1.84  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.82/1.84  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.82/1.84  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.82/1.84  tff('#skF_4', type, '#skF_4': $i).
% 4.82/1.84  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 4.82/1.84  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.82/1.84  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.82/1.84  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.82/1.84  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.82/1.84  
% 4.82/1.86  tff(f_156, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_funct_2)).
% 4.82/1.86  tff(f_91, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.82/1.86  tff(f_34, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 4.82/1.86  tff(f_99, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 4.82/1.86  tff(f_77, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 4.82/1.86  tff(f_40, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.82/1.86  tff(f_67, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 4.82/1.86  tff(f_95, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.82/1.86  tff(f_117, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 4.82/1.86  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 4.82/1.86  tff(f_48, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 4.82/1.86  tff(f_139, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_funct_2)).
% 4.82/1.86  tff(f_55, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 4.82/1.86  tff(f_127, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_funct_2)).
% 4.82/1.86  tff(f_42, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 4.82/1.86  tff(f_58, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 4.82/1.86  tff(f_59, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_relat_1)).
% 4.82/1.86  tff(f_79, axiom, (![A]: (k2_funct_1(k6_relat_1(A)) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_funct_1)).
% 4.82/1.86  tff(c_82, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_156])).
% 4.82/1.86  tff(c_180, plain, (![C_41, A_42, B_43]: (v1_relat_1(C_41) | ~m1_subset_1(C_41, k1_zfmisc_1(k2_zfmisc_1(A_42, B_43))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.82/1.86  tff(c_188, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_82, c_180])).
% 4.82/1.86  tff(c_86, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_156])).
% 4.82/1.86  tff(c_4, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.82/1.86  tff(c_80, plain, (v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_156])).
% 4.82/1.86  tff(c_78, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_3'), inference(cnfTransformation, [status(thm)], [f_156])).
% 4.82/1.86  tff(c_1773, plain, (![A_163, B_164, C_165]: (k2_relset_1(A_163, B_164, C_165)=k2_relat_1(C_165) | ~m1_subset_1(C_165, k1_zfmisc_1(k2_zfmisc_1(A_163, B_164))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 4.82/1.86  tff(c_1782, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_82, c_1773])).
% 4.82/1.86  tff(c_1792, plain, (k2_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_78, c_1782])).
% 4.82/1.86  tff(c_34, plain, (![A_12]: (k1_relat_1(k2_funct_1(A_12))=k2_relat_1(A_12) | ~v2_funct_1(A_12) | ~v1_funct_1(A_12) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.82/1.86  tff(c_10, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.82/1.86  tff(c_28, plain, (![A_11]: (v1_funct_1(k2_funct_1(A_11)) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.82/1.86  tff(c_76, plain, (~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_156])).
% 4.82/1.86  tff(c_213, plain, (~v1_funct_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_76])).
% 4.82/1.86  tff(c_216, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_28, c_213])).
% 4.82/1.86  tff(c_220, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_188, c_86, c_216])).
% 4.82/1.86  tff(c_221, plain, (~v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_2') | ~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_76])).
% 4.82/1.86  tff(c_391, plain, (~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitLeft, [status(thm)], [c_221])).
% 4.82/1.86  tff(c_84, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_156])).
% 4.82/1.86  tff(c_458, plain, (![A_79, B_80, C_81]: (k1_relset_1(A_79, B_80, C_81)=k1_relat_1(C_81) | ~m1_subset_1(C_81, k1_zfmisc_1(k2_zfmisc_1(A_79, B_80))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 4.82/1.86  tff(c_468, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_82, c_458])).
% 4.82/1.86  tff(c_761, plain, (![B_106, A_107, C_108]: (k1_xboole_0=B_106 | k1_relset_1(A_107, B_106, C_108)=A_107 | ~v1_funct_2(C_108, A_107, B_106) | ~m1_subset_1(C_108, k1_zfmisc_1(k2_zfmisc_1(A_107, B_106))))), inference(cnfTransformation, [status(thm)], [f_117])).
% 4.82/1.86  tff(c_773, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_82, c_761])).
% 4.82/1.86  tff(c_787, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_84, c_468, c_773])).
% 4.82/1.86  tff(c_789, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(splitLeft, [status(thm)], [c_787])).
% 4.82/1.86  tff(c_32, plain, (![A_12]: (k2_relat_1(k2_funct_1(A_12))=k1_relat_1(A_12) | ~v2_funct_1(A_12) | ~v1_funct_1(A_12) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.82/1.86  tff(c_30, plain, (![A_11]: (v1_relat_1(k2_funct_1(A_11)) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.82/1.86  tff(c_222, plain, (v1_funct_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_76])).
% 4.82/1.86  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 4.82/1.86  tff(c_16, plain, (![A_6]: (k2_zfmisc_1(A_6, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.82/1.87  tff(c_691, plain, (![B_100, A_101]: (m1_subset_1(B_100, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_100), A_101))) | ~r1_tarski(k2_relat_1(B_100), A_101) | ~v1_funct_1(B_100) | ~v1_relat_1(B_100))), inference(cnfTransformation, [status(thm)], [f_139])).
% 4.82/1.87  tff(c_20, plain, (![C_10, B_9, A_8]: (~v1_xboole_0(C_10) | ~m1_subset_1(B_9, k1_zfmisc_1(C_10)) | ~r2_hidden(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.82/1.87  tff(c_937, plain, (![B_119, A_120, A_121]: (~v1_xboole_0(k2_zfmisc_1(k1_relat_1(B_119), A_120)) | ~r2_hidden(A_121, B_119) | ~r1_tarski(k2_relat_1(B_119), A_120) | ~v1_funct_1(B_119) | ~v1_relat_1(B_119))), inference(resolution, [status(thm)], [c_691, c_20])).
% 4.82/1.87  tff(c_944, plain, (![A_121, B_119]: (~v1_xboole_0(k1_xboole_0) | ~r2_hidden(A_121, B_119) | ~r1_tarski(k2_relat_1(B_119), k1_xboole_0) | ~v1_funct_1(B_119) | ~v1_relat_1(B_119))), inference(superposition, [status(thm), theory('equality')], [c_16, c_937])).
% 4.82/1.87  tff(c_953, plain, (![A_122, B_123]: (~r2_hidden(A_122, B_123) | ~r1_tarski(k2_relat_1(B_123), k1_xboole_0) | ~v1_funct_1(B_123) | ~v1_relat_1(B_123))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_944])).
% 4.82/1.87  tff(c_957, plain, (![A_124]: (~r1_tarski(k2_relat_1(A_124), k1_xboole_0) | ~v1_funct_1(A_124) | ~v1_relat_1(A_124) | k1_xboole_0=A_124)), inference(resolution, [status(thm)], [c_4, c_953])).
% 4.82/1.87  tff(c_972, plain, (![A_125]: (~r1_tarski(k1_relat_1(A_125), k1_xboole_0) | ~v1_funct_1(k2_funct_1(A_125)) | ~v1_relat_1(k2_funct_1(A_125)) | k2_funct_1(A_125)=k1_xboole_0 | ~v2_funct_1(A_125) | ~v1_funct_1(A_125) | ~v1_relat_1(A_125))), inference(superposition, [status(thm), theory('equality')], [c_32, c_957])).
% 4.82/1.87  tff(c_975, plain, (~r1_tarski('#skF_2', k1_xboole_0) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | k2_funct_1('#skF_4')=k1_xboole_0 | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_789, c_972])).
% 4.82/1.87  tff(c_983, plain, (~r1_tarski('#skF_2', k1_xboole_0) | ~v1_relat_1(k2_funct_1('#skF_4')) | k2_funct_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_188, c_86, c_80, c_222, c_975])).
% 4.82/1.87  tff(c_986, plain, (~v1_relat_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_983])).
% 4.82/1.87  tff(c_989, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_30, c_986])).
% 4.82/1.87  tff(c_993, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_188, c_86, c_989])).
% 4.82/1.87  tff(c_995, plain, (v1_relat_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_983])).
% 4.82/1.87  tff(c_392, plain, (![A_68, B_69, C_70]: (k2_relset_1(A_68, B_69, C_70)=k2_relat_1(C_70) | ~m1_subset_1(C_70, k1_zfmisc_1(k2_zfmisc_1(A_68, B_69))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 4.82/1.87  tff(c_395, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_82, c_392])).
% 4.82/1.87  tff(c_403, plain, (k2_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_78, c_395])).
% 4.82/1.87  tff(c_485, plain, (![A_85]: (m1_subset_1(A_85, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_85), k2_relat_1(A_85)))) | ~v1_funct_1(A_85) | ~v1_relat_1(A_85))), inference(cnfTransformation, [status(thm)], [f_127])).
% 4.82/1.87  tff(c_1126, plain, (![A_131]: (m1_subset_1(k2_funct_1(A_131), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_131), k2_relat_1(k2_funct_1(A_131))))) | ~v1_funct_1(k2_funct_1(A_131)) | ~v1_relat_1(k2_funct_1(A_131)) | ~v2_funct_1(A_131) | ~v1_funct_1(A_131) | ~v1_relat_1(A_131))), inference(superposition, [status(thm), theory('equality')], [c_34, c_485])).
% 4.82/1.87  tff(c_1146, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', k2_relat_1(k2_funct_1('#skF_4'))))) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_403, c_1126])).
% 4.82/1.87  tff(c_1175, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', k2_relat_1(k2_funct_1('#skF_4')))))), inference(demodulation, [status(thm), theory('equality')], [c_188, c_86, c_80, c_995, c_222, c_1146])).
% 4.82/1.87  tff(c_1203, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', k1_relat_1('#skF_4')))) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_32, c_1175])).
% 4.82/1.87  tff(c_1215, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_188, c_86, c_80, c_789, c_1203])).
% 4.82/1.87  tff(c_1217, plain, $false, inference(negUnitSimplification, [status(thm)], [c_391, c_1215])).
% 4.82/1.87  tff(c_1218, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_787])).
% 4.82/1.87  tff(c_746, plain, (![B_105]: (m1_subset_1(B_105, k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k2_relat_1(B_105), k1_xboole_0) | ~v1_funct_1(B_105) | ~v1_relat_1(B_105))), inference(superposition, [status(thm), theory('equality')], [c_16, c_691])).
% 4.82/1.87  tff(c_749, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski('#skF_3', k1_xboole_0) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_403, c_746])).
% 4.82/1.87  tff(c_757, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski('#skF_3', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_188, c_86, c_749])).
% 4.82/1.87  tff(c_760, plain, (~r1_tarski('#skF_3', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_757])).
% 4.82/1.87  tff(c_1221, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1218, c_760])).
% 4.82/1.87  tff(c_1257, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10, c_1221])).
% 4.82/1.87  tff(c_1259, plain, (r1_tarski('#skF_3', k1_xboole_0)), inference(splitRight, [status(thm)], [c_757])).
% 4.82/1.87  tff(c_12, plain, (![A_5]: (r1_tarski(k1_xboole_0, A_5))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.82/1.87  tff(c_189, plain, (![B_44, A_45]: (B_44=A_45 | ~r1_tarski(B_44, A_45) | ~r1_tarski(A_45, B_44))), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.82/1.87  tff(c_194, plain, (![A_5]: (k1_xboole_0=A_5 | ~r1_tarski(A_5, k1_xboole_0))), inference(resolution, [status(thm)], [c_12, c_189])).
% 4.82/1.87  tff(c_1293, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_1259, c_194])).
% 4.82/1.87  tff(c_1329, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1293, c_2])).
% 4.82/1.87  tff(c_1322, plain, (![A_6]: (k2_zfmisc_1(A_6, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1293, c_1293, c_16])).
% 4.82/1.87  tff(c_499, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_3'))) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_403, c_485])).
% 4.82/1.87  tff(c_517, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_188, c_86, c_499])).
% 4.82/1.87  tff(c_536, plain, (![A_8]: (~v1_xboole_0(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_3')) | ~r2_hidden(A_8, '#skF_4'))), inference(resolution, [status(thm)], [c_517, c_20])).
% 4.82/1.87  tff(c_547, plain, (~v1_xboole_0(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_3'))), inference(splitLeft, [status(thm)], [c_536])).
% 4.82/1.87  tff(c_1472, plain, (~v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1322, c_547])).
% 4.82/1.87  tff(c_1478, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1329, c_1472])).
% 4.82/1.87  tff(c_1481, plain, (![A_142]: (~r2_hidden(A_142, '#skF_4'))), inference(splitRight, [status(thm)], [c_536])).
% 4.82/1.87  tff(c_1486, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_4, c_1481])).
% 4.82/1.87  tff(c_1511, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1486, c_2])).
% 4.82/1.87  tff(c_1504, plain, (![A_6]: (k2_zfmisc_1(A_6, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1486, c_1486, c_16])).
% 4.82/1.87  tff(c_22, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.82/1.87  tff(c_1509, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1486, c_1486, c_22])).
% 4.82/1.87  tff(c_1555, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1509, c_403])).
% 4.82/1.87  tff(c_223, plain, (![C_48, B_49, A_50]: (~v1_xboole_0(C_48) | ~m1_subset_1(B_49, k1_zfmisc_1(C_48)) | ~r2_hidden(A_50, B_49))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.82/1.87  tff(c_226, plain, (![A_50]: (~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3')) | ~r2_hidden(A_50, '#skF_4'))), inference(resolution, [status(thm)], [c_82, c_223])).
% 4.82/1.87  tff(c_227, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_226])).
% 4.82/1.87  tff(c_1578, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1555, c_227])).
% 4.82/1.87  tff(c_1666, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1511, c_1504, c_1578])).
% 4.82/1.87  tff(c_1667, plain, (~v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_221])).
% 4.82/1.87  tff(c_1668, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_221])).
% 4.82/1.87  tff(c_1677, plain, (![A_151, B_152, C_153]: (k1_relset_1(A_151, B_152, C_153)=k1_relat_1(C_153) | ~m1_subset_1(C_153, k1_zfmisc_1(k2_zfmisc_1(A_151, B_152))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 4.82/1.87  tff(c_1690, plain, (k1_relset_1('#skF_3', '#skF_2', k2_funct_1('#skF_4'))=k1_relat_1(k2_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_1668, c_1677])).
% 4.82/1.87  tff(c_2117, plain, (![B_189, C_190, A_191]: (k1_xboole_0=B_189 | v1_funct_2(C_190, A_191, B_189) | k1_relset_1(A_191, B_189, C_190)!=A_191 | ~m1_subset_1(C_190, k1_zfmisc_1(k2_zfmisc_1(A_191, B_189))))), inference(cnfTransformation, [status(thm)], [f_117])).
% 4.82/1.87  tff(c_2126, plain, (k1_xboole_0='#skF_2' | v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_2') | k1_relset_1('#skF_3', '#skF_2', k2_funct_1('#skF_4'))!='#skF_3'), inference(resolution, [status(thm)], [c_1668, c_2117])).
% 4.82/1.87  tff(c_2139, plain, (k1_xboole_0='#skF_2' | v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_2') | k1_relat_1(k2_funct_1('#skF_4'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1690, c_2126])).
% 4.82/1.87  tff(c_2140, plain, (k1_xboole_0='#skF_2' | k1_relat_1(k2_funct_1('#skF_4'))!='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_1667, c_2139])).
% 4.82/1.87  tff(c_2145, plain, (k1_relat_1(k2_funct_1('#skF_4'))!='#skF_3'), inference(splitLeft, [status(thm)], [c_2140])).
% 4.82/1.87  tff(c_2148, plain, (k2_relat_1('#skF_4')!='#skF_3' | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_34, c_2145])).
% 4.82/1.87  tff(c_2151, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_188, c_86, c_80, c_1792, c_2148])).
% 4.82/1.87  tff(c_2152, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_2140])).
% 4.82/1.87  tff(c_2186, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2152, c_2])).
% 4.82/1.87  tff(c_18, plain, (![B_7]: (k2_zfmisc_1(k1_xboole_0, B_7)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.82/1.87  tff(c_2178, plain, (![B_7]: (k2_zfmisc_1('#skF_2', B_7)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2152, c_2152, c_18])).
% 4.82/1.87  tff(c_2350, plain, (~v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2178, c_227])).
% 4.82/1.87  tff(c_2354, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2186, c_2350])).
% 4.82/1.87  tff(c_2357, plain, (![A_195]: (~r2_hidden(A_195, '#skF_4'))), inference(splitRight, [status(thm)], [c_226])).
% 4.82/1.87  tff(c_2362, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_4, c_2357])).
% 4.82/1.87  tff(c_2383, plain, (![A_5]: (r1_tarski('#skF_4', A_5))), inference(demodulation, [status(thm), theory('equality')], [c_2362, c_12])).
% 4.82/1.87  tff(c_2385, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2362, c_2362, c_22])).
% 4.82/1.87  tff(c_24, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.82/1.87  tff(c_2381, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2362, c_2362, c_24])).
% 4.82/1.87  tff(c_3161, plain, (![B_262, A_263]: (v1_funct_2(B_262, k1_relat_1(B_262), A_263) | ~r1_tarski(k2_relat_1(B_262), A_263) | ~v1_funct_1(B_262) | ~v1_relat_1(B_262))), inference(cnfTransformation, [status(thm)], [f_139])).
% 4.82/1.87  tff(c_3170, plain, (![A_263]: (v1_funct_2('#skF_4', '#skF_4', A_263) | ~r1_tarski(k2_relat_1('#skF_4'), A_263) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_2381, c_3161])).
% 4.82/1.87  tff(c_3173, plain, (![A_263]: (v1_funct_2('#skF_4', '#skF_4', A_263))), inference(demodulation, [status(thm), theory('equality')], [c_188, c_86, c_2383, c_2385, c_3170])).
% 4.82/1.87  tff(c_3035, plain, (![A_250, B_251, C_252]: (k2_relset_1(A_250, B_251, C_252)=k2_relat_1(C_252) | ~m1_subset_1(C_252, k1_zfmisc_1(k2_zfmisc_1(A_250, B_251))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 4.82/1.87  tff(c_3050, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_82, c_3035])).
% 4.82/1.87  tff(c_3055, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_78, c_2385, c_3050])).
% 4.82/1.87  tff(c_26, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.82/1.87  tff(c_133, plain, (![A_35]: (k2_funct_1(k6_relat_1(A_35))=k6_relat_1(A_35))), inference(cnfTransformation, [status(thm)], [f_79])).
% 4.82/1.87  tff(c_142, plain, (k6_relat_1(k1_xboole_0)=k2_funct_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_26, c_133])).
% 4.82/1.87  tff(c_145, plain, (k2_funct_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_26, c_142])).
% 4.82/1.87  tff(c_2378, plain, (k2_funct_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2362, c_2362, c_145])).
% 4.82/1.87  tff(c_52, plain, (![A_24]: (v1_funct_2(k1_xboole_0, A_24, k1_xboole_0) | k1_xboole_0=A_24 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_24, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_117])).
% 4.82/1.87  tff(c_89, plain, (![A_24]: (v1_funct_2(k1_xboole_0, A_24, k1_xboole_0) | k1_xboole_0=A_24 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_52])).
% 4.82/1.87  tff(c_2507, plain, (![A_24]: (v1_funct_2('#skF_4', A_24, '#skF_4') | A_24='#skF_4' | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_2362, c_2362, c_2362, c_2362, c_2362, c_89])).
% 4.82/1.87  tff(c_2508, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_2507])).
% 4.82/1.87  tff(c_2380, plain, (![A_6]: (k2_zfmisc_1(A_6, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2362, c_2362, c_16])).
% 4.82/1.87  tff(c_2549, plain, (![A_208]: (m1_subset_1(A_208, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_208), k2_relat_1(A_208)))) | ~v1_funct_1(A_208) | ~v1_relat_1(A_208))), inference(cnfTransformation, [status(thm)], [f_127])).
% 4.82/1.87  tff(c_2563, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_4'))) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2385, c_2549])).
% 4.82/1.87  tff(c_2570, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_188, c_86, c_2380, c_2381, c_2563])).
% 4.82/1.87  tff(c_2572, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2508, c_2570])).
% 4.82/1.87  tff(c_2574, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(splitRight, [status(thm)], [c_2507])).
% 4.82/1.87  tff(c_2379, plain, (![B_7]: (k2_zfmisc_1('#skF_4', B_7)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2362, c_2362, c_18])).
% 4.82/1.87  tff(c_2650, plain, (![A_216, B_217, C_218]: (k2_relset_1(A_216, B_217, C_218)=k2_relat_1(C_218) | ~m1_subset_1(C_218, k1_zfmisc_1(k2_zfmisc_1(A_216, B_217))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 4.82/1.87  tff(c_2662, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_82, c_2650])).
% 4.82/1.87  tff(c_2665, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_78, c_2385, c_2662])).
% 4.82/1.87  tff(c_2396, plain, (~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitLeft, [status(thm)], [c_221])).
% 4.82/1.87  tff(c_2436, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_2378, c_2396])).
% 4.82/1.87  tff(c_2667, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_2665, c_2436])).
% 4.82/1.87  tff(c_2674, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2574, c_2379, c_2667])).
% 4.82/1.87  tff(c_2675, plain, (~v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_221])).
% 4.82/1.87  tff(c_2715, plain, (~v1_funct_2('#skF_4', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2378, c_2675])).
% 4.82/1.87  tff(c_3059, plain, (~v1_funct_2('#skF_4', '#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3055, c_2715])).
% 4.82/1.87  tff(c_3177, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3173, c_3059])).
% 4.82/1.87  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.82/1.87  
% 4.82/1.87  Inference rules
% 4.82/1.87  ----------------------
% 4.82/1.87  #Ref     : 0
% 4.82/1.87  #Sup     : 683
% 4.82/1.87  #Fact    : 0
% 4.82/1.87  #Define  : 0
% 4.82/1.87  #Split   : 19
% 4.82/1.87  #Chain   : 0
% 4.82/1.87  #Close   : 0
% 4.82/1.87  
% 4.82/1.87  Ordering : KBO
% 4.82/1.87  
% 4.82/1.87  Simplification rules
% 4.82/1.87  ----------------------
% 4.82/1.87  #Subsume      : 65
% 4.82/1.87  #Demod        : 1240
% 4.82/1.87  #Tautology    : 400
% 4.82/1.87  #SimpNegUnit  : 5
% 4.82/1.87  #BackRed      : 196
% 4.82/1.87  
% 4.82/1.87  #Partial instantiations: 0
% 4.82/1.87  #Strategies tried      : 1
% 4.82/1.87  
% 4.82/1.87  Timing (in seconds)
% 4.82/1.87  ----------------------
% 4.82/1.87  Preprocessing        : 0.35
% 4.82/1.87  Parsing              : 0.18
% 4.82/1.87  CNF conversion       : 0.02
% 4.82/1.87  Main loop            : 0.75
% 4.82/1.87  Inferencing          : 0.25
% 4.82/1.87  Reduction            : 0.28
% 4.82/1.87  Demodulation         : 0.20
% 4.82/1.87  BG Simplification    : 0.03
% 4.82/1.87  Subsumption          : 0.12
% 4.82/1.87  Abstraction          : 0.03
% 4.82/1.87  MUC search           : 0.00
% 4.82/1.87  Cooper               : 0.00
% 4.82/1.87  Total                : 1.15
% 4.82/1.87  Index Insertion      : 0.00
% 4.82/1.87  Index Deletion       : 0.00
% 4.82/1.87  Index Matching       : 0.00
% 4.82/1.87  BG Taut test         : 0.00
%------------------------------------------------------------------------------
