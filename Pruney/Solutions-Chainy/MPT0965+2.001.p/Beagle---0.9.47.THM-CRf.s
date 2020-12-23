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
% DateTime   : Thu Dec  3 10:11:00 EST 2020

% Result     : Theorem 2.78s
% Output     : CNFRefutation 3.22s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 194 expanded)
%              Number of leaves         :   33 (  81 expanded)
%              Depth                    :   11
%              Number of atoms          :  162 ( 459 expanded)
%              Number of equality atoms :   32 (  74 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4

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

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_105,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( r2_hidden(C,A)
         => ( B = k1_xboole_0
            | r2_hidden(k1_funct_1(D,C),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_funct_2)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_92,axiom,(
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

tff(f_62,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => r2_hidden(k1_funct_1(B,A),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_funct_1)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_44,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

tff(c_38,plain,(
    r2_hidden('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_45,plain,(
    ! [B_30,A_31] :
      ( ~ r2_hidden(B_30,A_31)
      | ~ v1_xboole_0(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_49,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_45])).

tff(c_36,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_42,plain,(
    v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_40,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_564,plain,(
    ! [A_159,B_160,C_161] :
      ( k1_relset_1(A_159,B_160,C_161) = k1_relat_1(C_161)
      | ~ m1_subset_1(C_161,k1_zfmisc_1(k2_zfmisc_1(A_159,B_160))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_568,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_564])).

tff(c_727,plain,(
    ! [B_192,A_193,C_194] :
      ( k1_xboole_0 = B_192
      | k1_relset_1(A_193,B_192,C_194) = A_193
      | ~ v1_funct_2(C_194,A_193,B_192)
      | ~ m1_subset_1(C_194,k1_zfmisc_1(k2_zfmisc_1(A_193,B_192))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_734,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_727])).

tff(c_738,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_568,c_734])).

tff(c_739,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_738])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_538,plain,(
    ! [C_146,A_147,B_148] :
      ( v1_relat_1(C_146)
      | ~ m1_subset_1(C_146,k1_zfmisc_1(k2_zfmisc_1(A_147,B_148))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_542,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_538])).

tff(c_44,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_12,plain,(
    ! [B_14,A_13] :
      ( r2_hidden(k1_funct_1(B_14,A_13),k2_relat_1(B_14))
      | ~ r2_hidden(A_13,k1_relat_1(B_14))
      | ~ v1_funct_1(B_14)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_555,plain,(
    ! [A_156,B_157,C_158] :
      ( k2_relset_1(A_156,B_157,C_158) = k2_relat_1(C_158)
      | ~ m1_subset_1(C_158,k1_zfmisc_1(k2_zfmisc_1(A_156,B_157))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_559,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_555])).

tff(c_573,plain,(
    ! [A_162,B_163,C_164] :
      ( m1_subset_1(k2_relset_1(A_162,B_163,C_164),k1_zfmisc_1(B_163))
      | ~ m1_subset_1(C_164,k1_zfmisc_1(k2_zfmisc_1(A_162,B_163))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_593,plain,
    ( m1_subset_1(k2_relat_1('#skF_5'),k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_559,c_573])).

tff(c_600,plain,(
    m1_subset_1(k2_relat_1('#skF_5'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_593])).

tff(c_10,plain,(
    ! [A_10,C_12,B_11] :
      ( m1_subset_1(A_10,C_12)
      | ~ m1_subset_1(B_11,k1_zfmisc_1(C_12))
      | ~ r2_hidden(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_615,plain,(
    ! [A_167] :
      ( m1_subset_1(A_167,'#skF_3')
      | ~ r2_hidden(A_167,k2_relat_1('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_600,c_10])).

tff(c_619,plain,(
    ! [A_13] :
      ( m1_subset_1(k1_funct_1('#skF_5',A_13),'#skF_3')
      | ~ r2_hidden(A_13,k1_relat_1('#skF_5'))
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_12,c_615])).

tff(c_635,plain,(
    ! [A_168] :
      ( m1_subset_1(k1_funct_1('#skF_5',A_168),'#skF_3')
      | ~ r2_hidden(A_168,k1_relat_1('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_542,c_44,c_619])).

tff(c_645,plain,
    ( m1_subset_1(k1_funct_1('#skF_5','#skF_1'(k1_relat_1('#skF_5'))),'#skF_3')
    | v1_xboole_0(k1_relat_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_4,c_635])).

tff(c_646,plain,(
    v1_xboole_0(k1_relat_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_645])).

tff(c_740,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_739,c_646])).

tff(c_744,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_49,c_740])).

tff(c_746,plain,(
    ~ v1_xboole_0(k1_relat_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_645])).

tff(c_91,plain,(
    ! [A_48,B_49,C_50] :
      ( k1_relset_1(A_48,B_49,C_50) = k1_relat_1(C_50)
      | ~ m1_subset_1(C_50,k1_zfmisc_1(k2_zfmisc_1(A_48,B_49))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_95,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_91])).

tff(c_484,plain,(
    ! [B_139,A_140,C_141] :
      ( k1_xboole_0 = B_139
      | k1_relset_1(A_140,B_139,C_141) = A_140
      | ~ v1_funct_2(C_141,A_140,B_139)
      | ~ m1_subset_1(C_141,k1_zfmisc_1(k2_zfmisc_1(A_140,B_139))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_491,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_484])).

tff(c_495,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_95,c_491])).

tff(c_496,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_495])).

tff(c_65,plain,(
    ! [C_35,A_36,B_37] :
      ( v1_relat_1(C_35)
      | ~ m1_subset_1(C_35,k1_zfmisc_1(k2_zfmisc_1(A_36,B_37))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_69,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_65])).

tff(c_82,plain,(
    ! [A_45,B_46,C_47] :
      ( k2_relset_1(A_45,B_46,C_47) = k2_relat_1(C_47)
      | ~ m1_subset_1(C_47,k1_zfmisc_1(k2_zfmisc_1(A_45,B_46))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_86,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_82])).

tff(c_100,plain,(
    ! [A_51,B_52,C_53] :
      ( m1_subset_1(k2_relset_1(A_51,B_52,C_53),k1_zfmisc_1(B_52))
      | ~ m1_subset_1(C_53,k1_zfmisc_1(k2_zfmisc_1(A_51,B_52))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_120,plain,
    ( m1_subset_1(k2_relat_1('#skF_5'),k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_86,c_100])).

tff(c_127,plain,(
    m1_subset_1(k2_relat_1('#skF_5'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_120])).

tff(c_141,plain,(
    ! [A_56] :
      ( m1_subset_1(A_56,'#skF_3')
      | ~ r2_hidden(A_56,k2_relat_1('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_127,c_10])).

tff(c_145,plain,(
    ! [A_13] :
      ( m1_subset_1(k1_funct_1('#skF_5',A_13),'#skF_3')
      | ~ r2_hidden(A_13,k1_relat_1('#skF_5'))
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_12,c_141])).

tff(c_156,plain,(
    ! [A_13] :
      ( m1_subset_1(k1_funct_1('#skF_5',A_13),'#skF_3')
      | ~ r2_hidden(A_13,k1_relat_1('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_44,c_145])).

tff(c_528,plain,(
    ! [A_145] :
      ( m1_subset_1(k1_funct_1('#skF_5',A_145),'#skF_3')
      | ~ r2_hidden(A_145,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_496,c_156])).

tff(c_55,plain,(
    ! [A_33,B_34] :
      ( r2_hidden(A_33,B_34)
      | v1_xboole_0(B_34)
      | ~ m1_subset_1(A_33,B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_34,plain,(
    ~ r2_hidden(k1_funct_1('#skF_5','#skF_4'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_62,plain,
    ( v1_xboole_0('#skF_3')
    | ~ m1_subset_1(k1_funct_1('#skF_5','#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_55,c_34])).

tff(c_64,plain,(
    ~ m1_subset_1(k1_funct_1('#skF_5','#skF_4'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_531,plain,(
    ~ r2_hidden('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_528,c_64])).

tff(c_535,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_531])).

tff(c_536,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_6,plain,(
    ! [B_7,A_5] :
      ( v1_xboole_0(B_7)
      | ~ m1_subset_1(B_7,k1_zfmisc_1(A_5))
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_605,plain,
    ( v1_xboole_0(k2_relat_1('#skF_5'))
    | ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_600,c_6])).

tff(c_609,plain,(
    v1_xboole_0(k2_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_536,c_605])).

tff(c_610,plain,(
    ! [B_165,A_166] :
      ( r2_hidden(k1_funct_1(B_165,A_166),k2_relat_1(B_165))
      | ~ r2_hidden(A_166,k1_relat_1(B_165))
      | ~ v1_funct_1(B_165)
      | ~ v1_relat_1(B_165) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_753,plain,(
    ! [B_197,A_198] :
      ( ~ v1_xboole_0(k2_relat_1(B_197))
      | ~ r2_hidden(A_198,k1_relat_1(B_197))
      | ~ v1_funct_1(B_197)
      | ~ v1_relat_1(B_197) ) ),
    inference(resolution,[status(thm)],[c_610,c_2])).

tff(c_764,plain,(
    ! [B_199] :
      ( ~ v1_xboole_0(k2_relat_1(B_199))
      | ~ v1_funct_1(B_199)
      | ~ v1_relat_1(B_199)
      | v1_xboole_0(k1_relat_1(B_199)) ) ),
    inference(resolution,[status(thm)],[c_4,c_753])).

tff(c_767,plain,
    ( ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5')
    | v1_xboole_0(k1_relat_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_609,c_764])).

tff(c_770,plain,(
    v1_xboole_0(k1_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_542,c_44,c_767])).

tff(c_772,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_746,c_770])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n011.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 11:17:42 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.78/1.45  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.78/1.46  
% 2.78/1.46  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.22/1.47  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 3.22/1.47  
% 3.22/1.47  %Foreground sorts:
% 3.22/1.47  
% 3.22/1.47  
% 3.22/1.47  %Background operators:
% 3.22/1.47  
% 3.22/1.47  
% 3.22/1.47  %Foreground operators:
% 3.22/1.47  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.22/1.47  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.22/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.22/1.47  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.22/1.47  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.22/1.47  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.22/1.47  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.22/1.47  tff('#skF_5', type, '#skF_5': $i).
% 3.22/1.47  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.22/1.47  tff('#skF_2', type, '#skF_2': $i).
% 3.22/1.47  tff('#skF_3', type, '#skF_3': $i).
% 3.22/1.47  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.22/1.47  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.22/1.47  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.22/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.22/1.47  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.22/1.47  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.22/1.47  tff('#skF_4', type, '#skF_4': $i).
% 3.22/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.22/1.47  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.22/1.47  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.22/1.47  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.22/1.47  
% 3.22/1.48  tff(f_105, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_funct_2)).
% 3.22/1.48  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.22/1.48  tff(f_70, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.22/1.48  tff(f_92, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 3.22/1.48  tff(f_62, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.22/1.48  tff(f_58, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, A), k2_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_funct_1)).
% 3.22/1.48  tff(f_74, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.22/1.48  tff(f_66, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 3.22/1.48  tff(f_50, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 3.22/1.48  tff(f_44, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 3.22/1.48  tff(f_38, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 3.22/1.48  tff(c_38, plain, (r2_hidden('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.22/1.48  tff(c_45, plain, (![B_30, A_31]: (~r2_hidden(B_30, A_31) | ~v1_xboole_0(A_31))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.22/1.48  tff(c_49, plain, (~v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_38, c_45])).
% 3.22/1.48  tff(c_36, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.22/1.48  tff(c_42, plain, (v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.22/1.48  tff(c_40, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.22/1.48  tff(c_564, plain, (![A_159, B_160, C_161]: (k1_relset_1(A_159, B_160, C_161)=k1_relat_1(C_161) | ~m1_subset_1(C_161, k1_zfmisc_1(k2_zfmisc_1(A_159, B_160))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.22/1.48  tff(c_568, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_40, c_564])).
% 3.22/1.48  tff(c_727, plain, (![B_192, A_193, C_194]: (k1_xboole_0=B_192 | k1_relset_1(A_193, B_192, C_194)=A_193 | ~v1_funct_2(C_194, A_193, B_192) | ~m1_subset_1(C_194, k1_zfmisc_1(k2_zfmisc_1(A_193, B_192))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.22/1.48  tff(c_734, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_40, c_727])).
% 3.22/1.48  tff(c_738, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_568, c_734])).
% 3.22/1.48  tff(c_739, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_36, c_738])).
% 3.22/1.48  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.22/1.48  tff(c_538, plain, (![C_146, A_147, B_148]: (v1_relat_1(C_146) | ~m1_subset_1(C_146, k1_zfmisc_1(k2_zfmisc_1(A_147, B_148))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.22/1.48  tff(c_542, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_40, c_538])).
% 3.22/1.48  tff(c_44, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.22/1.48  tff(c_12, plain, (![B_14, A_13]: (r2_hidden(k1_funct_1(B_14, A_13), k2_relat_1(B_14)) | ~r2_hidden(A_13, k1_relat_1(B_14)) | ~v1_funct_1(B_14) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.22/1.48  tff(c_555, plain, (![A_156, B_157, C_158]: (k2_relset_1(A_156, B_157, C_158)=k2_relat_1(C_158) | ~m1_subset_1(C_158, k1_zfmisc_1(k2_zfmisc_1(A_156, B_157))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.22/1.48  tff(c_559, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_40, c_555])).
% 3.22/1.48  tff(c_573, plain, (![A_162, B_163, C_164]: (m1_subset_1(k2_relset_1(A_162, B_163, C_164), k1_zfmisc_1(B_163)) | ~m1_subset_1(C_164, k1_zfmisc_1(k2_zfmisc_1(A_162, B_163))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.22/1.48  tff(c_593, plain, (m1_subset_1(k2_relat_1('#skF_5'), k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_559, c_573])).
% 3.22/1.48  tff(c_600, plain, (m1_subset_1(k2_relat_1('#skF_5'), k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_593])).
% 3.22/1.48  tff(c_10, plain, (![A_10, C_12, B_11]: (m1_subset_1(A_10, C_12) | ~m1_subset_1(B_11, k1_zfmisc_1(C_12)) | ~r2_hidden(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.22/1.48  tff(c_615, plain, (![A_167]: (m1_subset_1(A_167, '#skF_3') | ~r2_hidden(A_167, k2_relat_1('#skF_5')))), inference(resolution, [status(thm)], [c_600, c_10])).
% 3.22/1.48  tff(c_619, plain, (![A_13]: (m1_subset_1(k1_funct_1('#skF_5', A_13), '#skF_3') | ~r2_hidden(A_13, k1_relat_1('#skF_5')) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_12, c_615])).
% 3.22/1.48  tff(c_635, plain, (![A_168]: (m1_subset_1(k1_funct_1('#skF_5', A_168), '#skF_3') | ~r2_hidden(A_168, k1_relat_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_542, c_44, c_619])).
% 3.22/1.48  tff(c_645, plain, (m1_subset_1(k1_funct_1('#skF_5', '#skF_1'(k1_relat_1('#skF_5'))), '#skF_3') | v1_xboole_0(k1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_4, c_635])).
% 3.22/1.48  tff(c_646, plain, (v1_xboole_0(k1_relat_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_645])).
% 3.22/1.48  tff(c_740, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_739, c_646])).
% 3.22/1.48  tff(c_744, plain, $false, inference(negUnitSimplification, [status(thm)], [c_49, c_740])).
% 3.22/1.48  tff(c_746, plain, (~v1_xboole_0(k1_relat_1('#skF_5'))), inference(splitRight, [status(thm)], [c_645])).
% 3.22/1.48  tff(c_91, plain, (![A_48, B_49, C_50]: (k1_relset_1(A_48, B_49, C_50)=k1_relat_1(C_50) | ~m1_subset_1(C_50, k1_zfmisc_1(k2_zfmisc_1(A_48, B_49))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.22/1.48  tff(c_95, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_40, c_91])).
% 3.22/1.48  tff(c_484, plain, (![B_139, A_140, C_141]: (k1_xboole_0=B_139 | k1_relset_1(A_140, B_139, C_141)=A_140 | ~v1_funct_2(C_141, A_140, B_139) | ~m1_subset_1(C_141, k1_zfmisc_1(k2_zfmisc_1(A_140, B_139))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.22/1.48  tff(c_491, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_40, c_484])).
% 3.22/1.48  tff(c_495, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_95, c_491])).
% 3.22/1.48  tff(c_496, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_36, c_495])).
% 3.22/1.48  tff(c_65, plain, (![C_35, A_36, B_37]: (v1_relat_1(C_35) | ~m1_subset_1(C_35, k1_zfmisc_1(k2_zfmisc_1(A_36, B_37))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.22/1.48  tff(c_69, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_40, c_65])).
% 3.22/1.48  tff(c_82, plain, (![A_45, B_46, C_47]: (k2_relset_1(A_45, B_46, C_47)=k2_relat_1(C_47) | ~m1_subset_1(C_47, k1_zfmisc_1(k2_zfmisc_1(A_45, B_46))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.22/1.48  tff(c_86, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_40, c_82])).
% 3.22/1.48  tff(c_100, plain, (![A_51, B_52, C_53]: (m1_subset_1(k2_relset_1(A_51, B_52, C_53), k1_zfmisc_1(B_52)) | ~m1_subset_1(C_53, k1_zfmisc_1(k2_zfmisc_1(A_51, B_52))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.22/1.48  tff(c_120, plain, (m1_subset_1(k2_relat_1('#skF_5'), k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_86, c_100])).
% 3.22/1.48  tff(c_127, plain, (m1_subset_1(k2_relat_1('#skF_5'), k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_120])).
% 3.22/1.48  tff(c_141, plain, (![A_56]: (m1_subset_1(A_56, '#skF_3') | ~r2_hidden(A_56, k2_relat_1('#skF_5')))), inference(resolution, [status(thm)], [c_127, c_10])).
% 3.22/1.48  tff(c_145, plain, (![A_13]: (m1_subset_1(k1_funct_1('#skF_5', A_13), '#skF_3') | ~r2_hidden(A_13, k1_relat_1('#skF_5')) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_12, c_141])).
% 3.22/1.48  tff(c_156, plain, (![A_13]: (m1_subset_1(k1_funct_1('#skF_5', A_13), '#skF_3') | ~r2_hidden(A_13, k1_relat_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_69, c_44, c_145])).
% 3.22/1.48  tff(c_528, plain, (![A_145]: (m1_subset_1(k1_funct_1('#skF_5', A_145), '#skF_3') | ~r2_hidden(A_145, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_496, c_156])).
% 3.22/1.48  tff(c_55, plain, (![A_33, B_34]: (r2_hidden(A_33, B_34) | v1_xboole_0(B_34) | ~m1_subset_1(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.22/1.48  tff(c_34, plain, (~r2_hidden(k1_funct_1('#skF_5', '#skF_4'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.22/1.48  tff(c_62, plain, (v1_xboole_0('#skF_3') | ~m1_subset_1(k1_funct_1('#skF_5', '#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_55, c_34])).
% 3.22/1.48  tff(c_64, plain, (~m1_subset_1(k1_funct_1('#skF_5', '#skF_4'), '#skF_3')), inference(splitLeft, [status(thm)], [c_62])).
% 3.22/1.48  tff(c_531, plain, (~r2_hidden('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_528, c_64])).
% 3.22/1.48  tff(c_535, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_531])).
% 3.22/1.48  tff(c_536, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_62])).
% 3.22/1.48  tff(c_6, plain, (![B_7, A_5]: (v1_xboole_0(B_7) | ~m1_subset_1(B_7, k1_zfmisc_1(A_5)) | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.22/1.48  tff(c_605, plain, (v1_xboole_0(k2_relat_1('#skF_5')) | ~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_600, c_6])).
% 3.22/1.48  tff(c_609, plain, (v1_xboole_0(k2_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_536, c_605])).
% 3.22/1.48  tff(c_610, plain, (![B_165, A_166]: (r2_hidden(k1_funct_1(B_165, A_166), k2_relat_1(B_165)) | ~r2_hidden(A_166, k1_relat_1(B_165)) | ~v1_funct_1(B_165) | ~v1_relat_1(B_165))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.22/1.48  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.22/1.48  tff(c_753, plain, (![B_197, A_198]: (~v1_xboole_0(k2_relat_1(B_197)) | ~r2_hidden(A_198, k1_relat_1(B_197)) | ~v1_funct_1(B_197) | ~v1_relat_1(B_197))), inference(resolution, [status(thm)], [c_610, c_2])).
% 3.22/1.48  tff(c_764, plain, (![B_199]: (~v1_xboole_0(k2_relat_1(B_199)) | ~v1_funct_1(B_199) | ~v1_relat_1(B_199) | v1_xboole_0(k1_relat_1(B_199)))), inference(resolution, [status(thm)], [c_4, c_753])).
% 3.22/1.48  tff(c_767, plain, (~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5') | v1_xboole_0(k1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_609, c_764])).
% 3.22/1.48  tff(c_770, plain, (v1_xboole_0(k1_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_542, c_44, c_767])).
% 3.22/1.48  tff(c_772, plain, $false, inference(negUnitSimplification, [status(thm)], [c_746, c_770])).
% 3.22/1.48  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.22/1.48  
% 3.22/1.48  Inference rules
% 3.22/1.48  ----------------------
% 3.22/1.48  #Ref     : 0
% 3.22/1.48  #Sup     : 130
% 3.22/1.48  #Fact    : 0
% 3.22/1.48  #Define  : 0
% 3.22/1.48  #Split   : 9
% 3.22/1.48  #Chain   : 0
% 3.22/1.48  #Close   : 0
% 3.22/1.48  
% 3.22/1.48  Ordering : KBO
% 3.22/1.48  
% 3.22/1.48  Simplification rules
% 3.22/1.48  ----------------------
% 3.22/1.48  #Subsume      : 14
% 3.22/1.48  #Demod        : 67
% 3.22/1.48  #Tautology    : 27
% 3.22/1.48  #SimpNegUnit  : 18
% 3.22/1.48  #BackRed      : 15
% 3.22/1.48  
% 3.22/1.48  #Partial instantiations: 0
% 3.22/1.48  #Strategies tried      : 1
% 3.22/1.48  
% 3.22/1.48  Timing (in seconds)
% 3.22/1.48  ----------------------
% 3.22/1.49  Preprocessing        : 0.32
% 3.22/1.49  Parsing              : 0.17
% 3.22/1.49  CNF conversion       : 0.02
% 3.22/1.49  Main loop            : 0.40
% 3.22/1.49  Inferencing          : 0.15
% 3.22/1.49  Reduction            : 0.11
% 3.22/1.49  Demodulation         : 0.07
% 3.22/1.49  BG Simplification    : 0.02
% 3.22/1.49  Subsumption          : 0.07
% 3.22/1.49  Abstraction          : 0.02
% 3.22/1.49  MUC search           : 0.00
% 3.22/1.49  Cooper               : 0.00
% 3.22/1.49  Total                : 0.76
% 3.22/1.49  Index Insertion      : 0.00
% 3.22/1.49  Index Deletion       : 0.00
% 3.22/1.49  Index Matching       : 0.00
% 3.22/1.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
