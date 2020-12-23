%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:47 EST 2020

% Result     : Theorem 9.16s
% Output     : CNFRefutation 9.61s
% Verified   : 
% Statistics : Number of formulae       :  325 (23976 expanded)
%              Number of leaves         :   41 (7925 expanded)
%              Depth                    :   24
%              Number of atoms          :  592 (60769 expanded)
%              Number of equality atoms :  159 (11125 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2

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

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_148,negated_conjecture,(
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

tff(f_82,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_40,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k2_zfmisc_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_zfmisc_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_90,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_78,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_64,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_86,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_108,axiom,(
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

tff(f_131,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_42,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_121,axiom,(
    ! [A,B] :
    ? [C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
      & v1_relat_1(C)
      & v4_relat_1(C,A)
      & v5_relat_1(C,B)
      & v1_funct_1(C)
      & v1_funct_2(C,A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_funct_2)).

tff(c_74,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_16697,plain,(
    ! [C_827,A_828,B_829] :
      ( v1_relat_1(C_827)
      | ~ m1_subset_1(C_827,k1_zfmisc_1(k2_zfmisc_1(A_828,B_829))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_16711,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_74,c_16697])).

tff(c_78,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_72,plain,(
    v2_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( v1_xboole_0(k2_zfmisc_1(A_6,B_7))
      | ~ v1_xboole_0(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_16736,plain,(
    ! [C_834,B_835,A_836] :
      ( ~ v1_xboole_0(C_834)
      | ~ m1_subset_1(B_835,k1_zfmisc_1(C_834))
      | ~ r2_hidden(A_836,B_835) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_16752,plain,(
    ! [A_836] :
      ( ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4'))
      | ~ r2_hidden(A_836,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_74,c_16736])).

tff(c_16822,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_16752])).

tff(c_16826,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_10,c_16822])).

tff(c_70,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_17946,plain,(
    ! [A_941,B_942,C_943] :
      ( k2_relset_1(A_941,B_942,C_943) = k2_relat_1(C_943)
      | ~ m1_subset_1(C_943,k1_zfmisc_1(k2_zfmisc_1(A_941,B_942))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_17967,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_74,c_17946])).

tff(c_17976,plain,(
    k2_relat_1('#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_17967])).

tff(c_30,plain,(
    ! [A_17] :
      ( k1_relat_1(k2_funct_1(A_17)) = k2_relat_1(A_17)
      | ~ v2_funct_1(A_17)
      | ~ v1_funct_1(A_17)
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_225,plain,(
    ! [C_81,B_82,A_83] :
      ( ~ v1_xboole_0(C_81)
      | ~ m1_subset_1(B_82,k1_zfmisc_1(C_81))
      | ~ r2_hidden(A_83,B_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_238,plain,(
    ! [A_83] :
      ( ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4'))
      | ~ r2_hidden(A_83,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_74,c_225])).

tff(c_248,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_238])).

tff(c_252,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_10,c_248])).

tff(c_76,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_140,plain,(
    ! [A_58] :
      ( v1_funct_1(k2_funct_1(A_58))
      | ~ v1_funct_1(A_58)
      | ~ v1_relat_1(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_68,plain,
    ( ~ m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3')))
    | ~ v1_funct_2(k2_funct_1('#skF_5'),'#skF_4','#skF_3')
    | ~ v1_funct_1(k2_funct_1('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_112,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_68])).

tff(c_143,plain,
    ( ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_140,c_112])).

tff(c_146,plain,(
    ~ v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_143])).

tff(c_152,plain,(
    ! [C_62,A_63,B_64] :
      ( v1_relat_1(C_62)
      | ~ m1_subset_1(C_62,k1_zfmisc_1(k2_zfmisc_1(A_63,B_64))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_160,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_74,c_152])).

tff(c_170,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_146,c_160])).

tff(c_171,plain,
    ( ~ v1_funct_2(k2_funct_1('#skF_5'),'#skF_4','#skF_3')
    | ~ m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_200,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_171])).

tff(c_207,plain,(
    ! [C_78,A_79,B_80] :
      ( v1_relat_1(C_78)
      | ~ m1_subset_1(C_78,k1_zfmisc_1(k2_zfmisc_1(A_79,B_80))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_222,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_74,c_207])).

tff(c_729,plain,(
    ! [A_144,B_145,C_146] :
      ( k2_relset_1(A_144,B_145,C_146) = k2_relat_1(C_146)
      | ~ m1_subset_1(C_146,k1_zfmisc_1(k2_zfmisc_1(A_144,B_145))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_744,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_74,c_729])).

tff(c_751,plain,(
    k2_relat_1('#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_744])).

tff(c_22,plain,(
    ! [A_15] :
      ( v1_relat_1(k2_funct_1(A_15))
      | ~ v1_funct_1(A_15)
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_172,plain,(
    v1_funct_1(k2_funct_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_665,plain,(
    ! [A_133,B_134,C_135] :
      ( k1_relset_1(A_133,B_134,C_135) = k1_relat_1(C_135)
      | ~ m1_subset_1(C_135,k1_zfmisc_1(k2_zfmisc_1(A_133,B_134))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_686,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_74,c_665])).

tff(c_1394,plain,(
    ! [B_188,A_189,C_190] :
      ( k1_xboole_0 = B_188
      | k1_relset_1(A_189,B_188,C_190) = A_189
      | ~ v1_funct_2(C_190,A_189,B_188)
      | ~ m1_subset_1(C_190,k1_zfmisc_1(k2_zfmisc_1(A_189,B_188))) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_1415,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_3'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_74,c_1394])).

tff(c_1429,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_686,c_1415])).

tff(c_1432,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_1429])).

tff(c_421,plain,(
    ! [A_112] :
      ( k2_relat_1(k2_funct_1(A_112)) = k1_relat_1(A_112)
      | ~ v2_funct_1(A_112)
      | ~ v1_funct_1(A_112)
      | ~ v1_relat_1(A_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_64,plain,(
    ! [A_33] :
      ( v1_funct_2(A_33,k1_relat_1(A_33),k2_relat_1(A_33))
      | ~ v1_funct_1(A_33)
      | ~ v1_relat_1(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_4794,plain,(
    ! [A_295] :
      ( v1_funct_2(k2_funct_1(A_295),k1_relat_1(k2_funct_1(A_295)),k1_relat_1(A_295))
      | ~ v1_funct_1(k2_funct_1(A_295))
      | ~ v1_relat_1(k2_funct_1(A_295))
      | ~ v2_funct_1(A_295)
      | ~ v1_funct_1(A_295)
      | ~ v1_relat_1(A_295) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_421,c_64])).

tff(c_4809,plain,
    ( v1_funct_2(k2_funct_1('#skF_5'),k1_relat_1(k2_funct_1('#skF_5')),'#skF_3')
    | ~ v1_funct_1(k2_funct_1('#skF_5'))
    | ~ v1_relat_1(k2_funct_1('#skF_5'))
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1432,c_4794])).

tff(c_4831,plain,
    ( v1_funct_2(k2_funct_1('#skF_5'),k1_relat_1(k2_funct_1('#skF_5')),'#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_222,c_78,c_72,c_172,c_4809])).

tff(c_4836,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_4831])).

tff(c_4839,plain,
    ( ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_22,c_4836])).

tff(c_4843,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_222,c_78,c_4839])).

tff(c_4845,plain,(
    v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_4831])).

tff(c_28,plain,(
    ! [A_17] :
      ( k2_relat_1(k2_funct_1(A_17)) = k1_relat_1(A_17)
      | ~ v2_funct_1(A_17)
      | ~ v1_funct_1(A_17)
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_769,plain,(
    ! [A_149] :
      ( m1_subset_1(A_149,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_149),k2_relat_1(A_149))))
      | ~ v1_funct_1(A_149)
      | ~ v1_relat_1(A_149) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_7089,plain,(
    ! [A_354] :
      ( m1_subset_1(k2_funct_1(A_354),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(A_354)),k1_relat_1(A_354))))
      | ~ v1_funct_1(k2_funct_1(A_354))
      | ~ v1_relat_1(k2_funct_1(A_354))
      | ~ v2_funct_1(A_354)
      | ~ v1_funct_1(A_354)
      | ~ v1_relat_1(A_354) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_769])).

tff(c_7132,plain,
    ( m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_5')),'#skF_3')))
    | ~ v1_funct_1(k2_funct_1('#skF_5'))
    | ~ v1_relat_1(k2_funct_1('#skF_5'))
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1432,c_7089])).

tff(c_7167,plain,(
    m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_5')),'#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_222,c_78,c_72,c_4845,c_172,c_7132])).

tff(c_7193,plain,
    ( m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_5'),'#skF_3')))
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_7167])).

tff(c_7206,plain,(
    m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_222,c_78,c_72,c_751,c_7193])).

tff(c_7208,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_200,c_7206])).

tff(c_7209,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1429])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_7253,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7209,c_6])).

tff(c_12,plain,(
    ! [A_8] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_173,plain,(
    ! [A_65,B_66] :
      ( v1_xboole_0(k2_zfmisc_1(A_65,B_66))
      | ~ v1_xboole_0(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_8,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_180,plain,(
    ! [A_70,B_71] :
      ( k2_zfmisc_1(A_70,B_71) = k1_xboole_0
      | ~ v1_xboole_0(A_70) ) ),
    inference(resolution,[status(thm)],[c_173,c_8])).

tff(c_186,plain,(
    ! [B_71] : k2_zfmisc_1(k1_xboole_0,B_71) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_180])).

tff(c_202,plain,(
    ! [A_75,B_76] : m1_subset_1('#skF_2'(A_75,B_76),k1_zfmisc_1(k2_zfmisc_1(A_75,B_76))) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_205,plain,(
    ! [B_71] : m1_subset_1('#skF_2'(k1_xboole_0,B_71),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_186,c_202])).

tff(c_227,plain,(
    ! [A_83,B_71] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(A_83,'#skF_2'(k1_xboole_0,B_71)) ) ),
    inference(resolution,[status(thm)],[c_205,c_225])).

tff(c_253,plain,(
    ! [A_85,B_86] : ~ r2_hidden(A_85,'#skF_2'(k1_xboole_0,B_86)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_227])).

tff(c_259,plain,(
    ! [B_87] : v1_xboole_0('#skF_2'(k1_xboole_0,B_87)) ),
    inference(resolution,[status(thm)],[c_4,c_253])).

tff(c_266,plain,(
    ! [B_87] : '#skF_2'(k1_xboole_0,B_87) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_259,c_8])).

tff(c_687,plain,(
    ! [A_133,B_134] : k1_relset_1(A_133,B_134,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_12,c_665])).

tff(c_50,plain,(
    ! [A_30,B_31] : v1_funct_2('#skF_2'(A_30,B_31),A_30,B_31) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_46,plain,(
    ! [B_28,C_29] :
      ( k1_relset_1(k1_xboole_0,B_28,C_29) = k1_xboole_0
      | ~ v1_funct_2(C_29,k1_xboole_0,B_28)
      | ~ m1_subset_1(C_29,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_28))) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_1172,plain,(
    ! [B_174,C_175] :
      ( k1_relset_1(k1_xboole_0,B_174,C_175) = k1_xboole_0
      | ~ v1_funct_2(C_175,k1_xboole_0,B_174)
      | ~ m1_subset_1(C_175,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_186,c_46])).

tff(c_1180,plain,(
    ! [B_31] :
      ( k1_relset_1(k1_xboole_0,B_31,'#skF_2'(k1_xboole_0,B_31)) = k1_xboole_0
      | ~ m1_subset_1('#skF_2'(k1_xboole_0,B_31),k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_50,c_1172])).

tff(c_1190,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_266,c_687,c_266,c_1180])).

tff(c_7219,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7209,c_7209,c_1190])).

tff(c_40,plain,(
    ! [C_29,A_27] :
      ( k1_xboole_0 = C_29
      | ~ v1_funct_2(C_29,A_27,k1_xboole_0)
      | k1_xboole_0 = A_27
      | ~ m1_subset_1(C_29,k1_zfmisc_1(k2_zfmisc_1(A_27,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_9060,plain,(
    ! [C_444,A_445] :
      ( C_444 = '#skF_4'
      | ~ v1_funct_2(C_444,A_445,'#skF_4')
      | A_445 = '#skF_4'
      | ~ m1_subset_1(C_444,k1_zfmisc_1(k2_zfmisc_1(A_445,'#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7209,c_7209,c_7209,c_7209,c_40])).

tff(c_9090,plain,
    ( '#skF_5' = '#skF_4'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4')
    | '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_74,c_9060])).

tff(c_9101,plain,
    ( '#skF_5' = '#skF_4'
    | '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_9090])).

tff(c_9102,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_9101])).

tff(c_9106,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9102,c_252])).

tff(c_9114,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7253,c_9106])).

tff(c_9115,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_9101])).

tff(c_785,plain,
    ( m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'),'#skF_4')))
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_751,c_769])).

tff(c_798,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'),'#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_222,c_78,c_785])).

tff(c_16,plain,(
    ! [C_14,B_13,A_12] :
      ( ~ v1_xboole_0(C_14)
      | ~ m1_subset_1(B_13,k1_zfmisc_1(C_14))
      | ~ r2_hidden(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_816,plain,(
    ! [A_12] :
      ( ~ v1_xboole_0(k2_zfmisc_1(k1_relat_1('#skF_5'),'#skF_4'))
      | ~ r2_hidden(A_12,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_798,c_16])).

tff(c_827,plain,(
    ~ v1_xboole_0(k2_zfmisc_1(k1_relat_1('#skF_5'),'#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_816])).

tff(c_831,plain,(
    ~ v1_xboole_0(k1_relat_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_10,c_827])).

tff(c_9120,plain,(
    ~ v1_xboole_0(k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9115,c_831])).

tff(c_9140,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7253,c_7219,c_9120])).

tff(c_9144,plain,(
    ! [A_447] : ~ r2_hidden(A_447,'#skF_5') ),
    inference(splitRight,[status(thm)],[c_816])).

tff(c_9149,plain,(
    v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_4,c_9144])).

tff(c_9159,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_9149,c_8])).

tff(c_9510,plain,(
    ! [A_466,B_467] : k1_relset_1(A_466,B_467,'#skF_5') = k1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9159,c_9159,c_687])).

tff(c_9180,plain,(
    ! [A_8] : m1_subset_1('#skF_5',k1_zfmisc_1(A_8)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9159,c_12])).

tff(c_60,plain,(
    ! [A_30,B_31] : m1_subset_1('#skF_2'(A_30,B_31),k1_zfmisc_1(k2_zfmisc_1(A_30,B_31))) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_350,plain,(
    ! [A_99,B_100,A_101] :
      ( ~ v1_xboole_0(k2_zfmisc_1(A_99,B_100))
      | ~ r2_hidden(A_101,'#skF_2'(A_99,B_100)) ) ),
    inference(resolution,[status(thm)],[c_60,c_225])).

tff(c_361,plain,(
    ! [A_102,B_103] :
      ( ~ v1_xboole_0(k2_zfmisc_1(A_102,B_103))
      | v1_xboole_0('#skF_2'(A_102,B_103)) ) ),
    inference(resolution,[status(thm)],[c_4,c_350])).

tff(c_377,plain,(
    ! [A_105,B_106] :
      ( v1_xboole_0('#skF_2'(A_105,B_106))
      | ~ v1_xboole_0(A_105) ) ),
    inference(resolution,[status(thm)],[c_10,c_361])).

tff(c_387,plain,(
    ! [A_105,B_106] :
      ( '#skF_2'(A_105,B_106) = k1_xboole_0
      | ~ v1_xboole_0(A_105) ) ),
    inference(resolution,[status(thm)],[c_377,c_8])).

tff(c_9157,plain,(
    ! [B_106] : '#skF_2'('#skF_5',B_106) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_9149,c_387])).

tff(c_9282,plain,(
    ! [B_106] : '#skF_2'('#skF_5',B_106) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9159,c_9157])).

tff(c_9177,plain,(
    ! [B_71] : k2_zfmisc_1('#skF_5',B_71) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9159,c_9159,c_186])).

tff(c_9464,plain,(
    ! [B_460,C_461] :
      ( k1_relset_1('#skF_5',B_460,C_461) = '#skF_5'
      | ~ v1_funct_2(C_461,'#skF_5',B_460)
      | ~ m1_subset_1(C_461,k1_zfmisc_1('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9177,c_9159,c_9159,c_9159,c_9159,c_46])).

tff(c_9469,plain,(
    ! [B_31] :
      ( k1_relset_1('#skF_5',B_31,'#skF_2'('#skF_5',B_31)) = '#skF_5'
      | ~ m1_subset_1('#skF_2'('#skF_5',B_31),k1_zfmisc_1('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_50,c_9464])).

tff(c_9475,plain,(
    ! [B_31] : k1_relset_1('#skF_5',B_31,'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9180,c_9282,c_9282,c_9469])).

tff(c_9515,plain,(
    k1_relat_1('#skF_5') = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_9510,c_9475])).

tff(c_9162,plain,(
    ! [A_133,B_134] : k1_relset_1(A_133,B_134,'#skF_5') = k1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9159,c_9159,c_687])).

tff(c_9522,plain,(
    ! [A_133,B_134] : k1_relset_1(A_133,B_134,'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9515,c_9162])).

tff(c_48,plain,(
    ! [B_28,A_27,C_29] :
      ( k1_xboole_0 = B_28
      | k1_relset_1(A_27,B_28,C_29) = A_27
      | ~ v1_funct_2(C_29,A_27,B_28)
      | ~ m1_subset_1(C_29,k1_zfmisc_1(k2_zfmisc_1(A_27,B_28))) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_9555,plain,(
    ! [B_470,A_471,C_472] :
      ( B_470 = '#skF_5'
      | k1_relset_1(A_471,B_470,C_472) = A_471
      | ~ v1_funct_2(C_472,A_471,B_470)
      | ~ m1_subset_1(C_472,k1_zfmisc_1(k2_zfmisc_1(A_471,B_470))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9159,c_48])).

tff(c_9559,plain,(
    ! [B_470,A_471] :
      ( B_470 = '#skF_5'
      | k1_relset_1(A_471,B_470,'#skF_5') = A_471
      | ~ v1_funct_2('#skF_5',A_471,B_470) ) ),
    inference(resolution,[status(thm)],[c_9180,c_9555])).

tff(c_10169,plain,(
    ! [B_513,A_514] :
      ( B_513 = '#skF_5'
      | A_514 = '#skF_5'
      | ~ v1_funct_2('#skF_5',A_514,B_513) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9522,c_9559])).

tff(c_10198,plain,
    ( '#skF_5' = '#skF_4'
    | '#skF_5' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_76,c_10169])).

tff(c_10199,plain,(
    '#skF_5' = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_10198])).

tff(c_10236,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10199,c_9149])).

tff(c_10246,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_252,c_10236])).

tff(c_10247,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_10198])).

tff(c_10278,plain,(
    ! [B_71] : k2_zfmisc_1('#skF_4',B_71) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10247,c_10247,c_9177])).

tff(c_10289,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10247,c_200])).

tff(c_10570,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10278,c_10289])).

tff(c_10288,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10247,c_222])).

tff(c_10293,plain,(
    v1_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10247,c_78])).

tff(c_10292,plain,(
    v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10247,c_72])).

tff(c_10290,plain,(
    v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10247,c_172])).

tff(c_10287,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10247,c_751])).

tff(c_554,plain,(
    ! [A_124] :
      ( k1_relat_1(k2_funct_1(A_124)) = k2_relat_1(A_124)
      | ~ v2_funct_1(A_124)
      | ~ v1_funct_1(A_124)
      | ~ v1_relat_1(A_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_10757,plain,(
    ! [A_544] :
      ( v1_funct_2(k2_funct_1(A_544),k2_relat_1(A_544),k2_relat_1(k2_funct_1(A_544)))
      | ~ v1_funct_1(k2_funct_1(A_544))
      | ~ v1_relat_1(k2_funct_1(A_544))
      | ~ v2_funct_1(A_544)
      | ~ v1_funct_1(A_544)
      | ~ v1_relat_1(A_544) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_554,c_64])).

tff(c_10760,plain,
    ( v1_funct_2(k2_funct_1('#skF_4'),'#skF_4',k2_relat_1(k2_funct_1('#skF_4')))
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_10287,c_10757])).

tff(c_10768,plain,
    ( v1_funct_2(k2_funct_1('#skF_4'),'#skF_4',k2_relat_1(k2_funct_1('#skF_4')))
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10288,c_10293,c_10292,c_10290,c_10760])).

tff(c_10887,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_10768])).

tff(c_10890,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_22,c_10887])).

tff(c_10894,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10288,c_10293,c_10890])).

tff(c_10896,plain,(
    v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_10768])).

tff(c_11086,plain,(
    ! [A_564] :
      ( m1_subset_1(k2_funct_1(A_564),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_564),k2_relat_1(k2_funct_1(A_564)))))
      | ~ v1_funct_1(k2_funct_1(A_564))
      | ~ v1_relat_1(k2_funct_1(A_564))
      | ~ v2_funct_1(A_564)
      | ~ v1_funct_1(A_564)
      | ~ v1_relat_1(A_564) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_769])).

tff(c_11105,plain,
    ( m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_4',k2_relat_1(k2_funct_1('#skF_4')))))
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_10287,c_11086])).

tff(c_11120,plain,(
    m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10288,c_10293,c_10292,c_10896,c_10290,c_10278,c_11105])).

tff(c_11122,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10570,c_11120])).

tff(c_11124,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_238])).

tff(c_11125,plain,(
    ! [A_565] : ~ r2_hidden(A_565,'#skF_5') ),
    inference(splitRight,[status(thm)],[c_238])).

tff(c_11130,plain,(
    v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_4,c_11125])).

tff(c_11137,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_11130,c_8])).

tff(c_11195,plain,(
    ! [A_568] :
      ( A_568 = '#skF_5'
      | ~ v1_xboole_0(A_568) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11137,c_8])).

tff(c_11205,plain,(
    k2_zfmisc_1('#skF_3','#skF_4') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_11124,c_11195])).

tff(c_44,plain,(
    ! [B_28,C_29,A_27] :
      ( k1_xboole_0 = B_28
      | v1_funct_2(C_29,A_27,B_28)
      | k1_relset_1(A_27,B_28,C_29) != A_27
      | ~ m1_subset_1(C_29,k1_zfmisc_1(k2_zfmisc_1(A_27,B_28))) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_13607,plain,(
    ! [B_711,C_712,A_713] :
      ( B_711 = '#skF_5'
      | v1_funct_2(C_712,A_713,B_711)
      | k1_relset_1(A_713,B_711,C_712) != A_713
      | ~ m1_subset_1(C_712,k1_zfmisc_1(k2_zfmisc_1(A_713,B_711))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11137,c_44])).

tff(c_13625,plain,(
    ! [C_712] :
      ( '#skF_5' = '#skF_4'
      | v1_funct_2(C_712,'#skF_3','#skF_4')
      | k1_relset_1('#skF_3','#skF_4',C_712) != '#skF_3'
      | ~ m1_subset_1(C_712,k1_zfmisc_1('#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11205,c_13607])).

tff(c_13719,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_13625])).

tff(c_11140,plain,(
    ! [B_71] : k2_zfmisc_1('#skF_5',B_71) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11137,c_11137,c_186])).

tff(c_13774,plain,(
    ! [B_71] : k2_zfmisc_1('#skF_4',B_71) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13719,c_13719,c_11140])).

tff(c_13781,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13719,c_200])).

tff(c_13980,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13774,c_13781])).

tff(c_13780,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13719,c_222])).

tff(c_13785,plain,(
    v1_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13719,c_78])).

tff(c_13784,plain,(
    v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13719,c_72])).

tff(c_13782,plain,(
    v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13719,c_172])).

tff(c_11143,plain,(
    ! [A_8] : m1_subset_1('#skF_5',k1_zfmisc_1(A_8)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11137,c_12])).

tff(c_11741,plain,(
    ! [A_620,B_621,C_622] :
      ( k2_relset_1(A_620,B_621,C_622) = k2_relat_1(C_622)
      | ~ m1_subset_1(C_622,k1_zfmisc_1(k2_zfmisc_1(A_620,B_621))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_11763,plain,(
    ! [A_623,B_624] : k2_relset_1(A_623,B_624,'#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_11143,c_11741])).

tff(c_11767,plain,(
    k2_relat_1('#skF_5') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_11763,c_70])).

tff(c_13756,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13719,c_11767])).

tff(c_11453,plain,(
    ! [A_595] :
      ( k1_relat_1(k2_funct_1(A_595)) = k2_relat_1(A_595)
      | ~ v2_funct_1(A_595)
      | ~ v1_funct_1(A_595)
      | ~ v1_relat_1(A_595) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_14447,plain,(
    ! [A_748] :
      ( v1_funct_2(k2_funct_1(A_748),k2_relat_1(A_748),k2_relat_1(k2_funct_1(A_748)))
      | ~ v1_funct_1(k2_funct_1(A_748))
      | ~ v1_relat_1(k2_funct_1(A_748))
      | ~ v2_funct_1(A_748)
      | ~ v1_funct_1(A_748)
      | ~ v1_relat_1(A_748) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11453,c_64])).

tff(c_14450,plain,
    ( v1_funct_2(k2_funct_1('#skF_4'),'#skF_4',k2_relat_1(k2_funct_1('#skF_4')))
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_13756,c_14447])).

tff(c_14464,plain,
    ( v1_funct_2(k2_funct_1('#skF_4'),'#skF_4',k2_relat_1(k2_funct_1('#skF_4')))
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13780,c_13785,c_13784,c_13782,c_14450])).

tff(c_14487,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_14464])).

tff(c_14490,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_22,c_14487])).

tff(c_14494,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_13780,c_13785,c_14490])).

tff(c_14496,plain,(
    v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_14464])).

tff(c_11829,plain,(
    ! [A_632] :
      ( m1_subset_1(A_632,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_632),k2_relat_1(A_632))))
      | ~ v1_funct_1(A_632)
      | ~ v1_relat_1(A_632) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_14613,plain,(
    ! [A_755] :
      ( m1_subset_1(k2_funct_1(A_755),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_755),k2_relat_1(k2_funct_1(A_755)))))
      | ~ v1_funct_1(k2_funct_1(A_755))
      | ~ v1_relat_1(k2_funct_1(A_755))
      | ~ v2_funct_1(A_755)
      | ~ v1_funct_1(A_755)
      | ~ v1_relat_1(A_755) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_11829])).

tff(c_14635,plain,
    ( m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_4',k2_relat_1(k2_funct_1('#skF_4')))))
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_13756,c_14613])).

tff(c_14657,plain,(
    m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13780,c_13785,c_13784,c_14496,c_13782,c_13774,c_14635])).

tff(c_14659,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_13980,c_14657])).

tff(c_14661,plain,(
    '#skF_5' != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_13625])).

tff(c_236,plain,(
    ! [A_83,B_71] : ~ r2_hidden(A_83,'#skF_2'(k1_xboole_0,B_71)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_227])).

tff(c_11232,plain,(
    ! [A_572,B_573] : ~ r2_hidden(A_572,'#skF_2'('#skF_5',B_573)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11137,c_236])).

tff(c_11238,plain,(
    ! [B_574] : v1_xboole_0('#skF_2'('#skF_5',B_574)) ),
    inference(resolution,[status(thm)],[c_4,c_11232])).

tff(c_11144,plain,(
    ! [A_5] :
      ( A_5 = '#skF_5'
      | ~ v1_xboole_0(A_5) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11137,c_8])).

tff(c_11242,plain,(
    ! [B_574] : '#skF_2'('#skF_5',B_574) = '#skF_5' ),
    inference(resolution,[status(thm)],[c_11238,c_11144])).

tff(c_11540,plain,(
    ! [A_604,B_605,C_606] :
      ( k1_relset_1(A_604,B_605,C_606) = k1_relat_1(C_606)
      | ~ m1_subset_1(C_606,k1_zfmisc_1(k2_zfmisc_1(A_604,B_605))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_11560,plain,(
    ! [A_604,B_605] : k1_relset_1(A_604,B_605,'#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_11143,c_11540])).

tff(c_12544,plain,(
    ! [B_675,C_676] :
      ( k1_relset_1('#skF_5',B_675,C_676) = '#skF_5'
      | ~ v1_funct_2(C_676,'#skF_5',B_675)
      | ~ m1_subset_1(C_676,k1_zfmisc_1('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11140,c_11137,c_11137,c_11137,c_11137,c_46])).

tff(c_12552,plain,(
    ! [B_31] :
      ( k1_relset_1('#skF_5',B_31,'#skF_2'('#skF_5',B_31)) = '#skF_5'
      | ~ m1_subset_1('#skF_2'('#skF_5',B_31),k1_zfmisc_1('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_50,c_12544])).

tff(c_12562,plain,(
    k1_relat_1('#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11143,c_11242,c_11560,c_11242,c_12552])).

tff(c_11223,plain,(
    m1_subset_1('#skF_2'('#skF_3','#skF_4'),k1_zfmisc_1('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_11205,c_60])).

tff(c_11299,plain,(
    ! [A_12] :
      ( ~ v1_xboole_0('#skF_5')
      | ~ r2_hidden(A_12,'#skF_2'('#skF_3','#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_11223,c_16])).

tff(c_11306,plain,(
    ! [A_583] : ~ r2_hidden(A_583,'#skF_2'('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11130,c_11299])).

tff(c_11311,plain,(
    v1_xboole_0('#skF_2'('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_4,c_11306])).

tff(c_11318,plain,(
    '#skF_2'('#skF_3','#skF_4') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_11311,c_11144])).

tff(c_11561,plain,(
    ! [A_30,B_31] : k1_relset_1(A_30,B_31,'#skF_2'(A_30,B_31)) = k1_relat_1('#skF_2'(A_30,B_31)) ),
    inference(resolution,[status(thm)],[c_60,c_11540])).

tff(c_15496,plain,(
    ! [B_782,A_783,C_784] :
      ( B_782 = '#skF_5'
      | k1_relset_1(A_783,B_782,C_784) = A_783
      | ~ v1_funct_2(C_784,A_783,B_782)
      | ~ m1_subset_1(C_784,k1_zfmisc_1(k2_zfmisc_1(A_783,B_782))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11137,c_48])).

tff(c_15527,plain,(
    ! [B_31,A_30] :
      ( B_31 = '#skF_5'
      | k1_relset_1(A_30,B_31,'#skF_2'(A_30,B_31)) = A_30
      | ~ v1_funct_2('#skF_2'(A_30,B_31),A_30,B_31) ) ),
    inference(resolution,[status(thm)],[c_60,c_15496])).

tff(c_15537,plain,(
    ! [B_785,A_786] :
      ( B_785 = '#skF_5'
      | k1_relat_1('#skF_2'(A_786,B_785)) = A_786 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_11561,c_15527])).

tff(c_15598,plain,
    ( '#skF_5' = '#skF_4'
    | k1_relat_1('#skF_5') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_11318,c_15537])).

tff(c_15617,plain,
    ( '#skF_5' = '#skF_4'
    | '#skF_5' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12562,c_15598])).

tff(c_15618,plain,(
    '#skF_5' = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_14661,c_15617])).

tff(c_15690,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15618,c_200])).

tff(c_15689,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_15618,c_222])).

tff(c_15694,plain,(
    v1_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_15618,c_78])).

tff(c_15693,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_15618,c_72])).

tff(c_15648,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15618,c_15618,c_12562])).

tff(c_15691,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15618,c_172])).

tff(c_15665,plain,(
    k2_relat_1('#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15618,c_11767])).

tff(c_16355,plain,(
    ! [A_813] :
      ( v1_funct_2(k2_funct_1(A_813),k2_relat_1(A_813),k2_relat_1(k2_funct_1(A_813)))
      | ~ v1_funct_1(k2_funct_1(A_813))
      | ~ v1_relat_1(k2_funct_1(A_813))
      | ~ v2_funct_1(A_813)
      | ~ v1_funct_1(A_813)
      | ~ v1_relat_1(A_813) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11453,c_64])).

tff(c_16358,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_4',k2_relat_1(k2_funct_1('#skF_3')))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_15665,c_16355])).

tff(c_16372,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_4',k2_relat_1(k2_funct_1('#skF_3')))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15689,c_15694,c_15693,c_15691,c_16358])).

tff(c_16525,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_16372])).

tff(c_16528,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_16525])).

tff(c_16532,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_15689,c_15694,c_16528])).

tff(c_16534,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_16372])).

tff(c_16618,plain,(
    ! [A_825] :
      ( m1_subset_1(k2_funct_1(A_825),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_825),k2_relat_1(k2_funct_1(A_825)))))
      | ~ v1_funct_1(k2_funct_1(A_825))
      | ~ v1_relat_1(k2_funct_1(A_825))
      | ~ v2_funct_1(A_825)
      | ~ v1_funct_1(A_825)
      | ~ v1_relat_1(A_825) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_11829])).

tff(c_16637,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_4',k2_relat_1(k2_funct_1('#skF_3')))))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_15665,c_16618])).

tff(c_16658,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_4',k2_relat_1(k2_funct_1('#skF_3'))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15689,c_15694,c_15693,c_16534,c_15691,c_16637])).

tff(c_16683,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_4',k1_relat_1('#skF_3'))))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_16658])).

tff(c_16691,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15689,c_15694,c_15693,c_15648,c_16683])).

tff(c_16693,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_15690,c_16691])).

tff(c_16694,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_5'),'#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_171])).

tff(c_16695,plain,(
    m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_171])).

tff(c_17857,plain,(
    ! [A_930,B_931,C_932] :
      ( k1_relset_1(A_930,B_931,C_932) = k1_relat_1(C_932)
      | ~ m1_subset_1(C_932,k1_zfmisc_1(k2_zfmisc_1(A_930,B_931))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_17885,plain,(
    k1_relset_1('#skF_4','#skF_3',k2_funct_1('#skF_5')) = k1_relat_1(k2_funct_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_16695,c_17857])).

tff(c_18979,plain,(
    ! [B_990,C_991,A_992] :
      ( k1_xboole_0 = B_990
      | v1_funct_2(C_991,A_992,B_990)
      | k1_relset_1(A_992,B_990,C_991) != A_992
      | ~ m1_subset_1(C_991,k1_zfmisc_1(k2_zfmisc_1(A_992,B_990))) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_18997,plain,
    ( k1_xboole_0 = '#skF_3'
    | v1_funct_2(k2_funct_1('#skF_5'),'#skF_4','#skF_3')
    | k1_relset_1('#skF_4','#skF_3',k2_funct_1('#skF_5')) != '#skF_4' ),
    inference(resolution,[status(thm)],[c_16695,c_18979])).

tff(c_19012,plain,
    ( k1_xboole_0 = '#skF_3'
    | v1_funct_2(k2_funct_1('#skF_5'),'#skF_4','#skF_3')
    | k1_relat_1(k2_funct_1('#skF_5')) != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_17885,c_18997])).

tff(c_19013,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1(k2_funct_1('#skF_5')) != '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_16694,c_19012])).

tff(c_19019,plain,(
    k1_relat_1(k2_funct_1('#skF_5')) != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_19013])).

tff(c_19022,plain,
    ( k2_relat_1('#skF_5') != '#skF_4'
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_19019])).

tff(c_19025,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16711,c_78,c_72,c_17976,c_19022])).

tff(c_19026,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_19013])).

tff(c_19073,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_19026,c_6])).

tff(c_19075,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_16826,c_19073])).

tff(c_19079,plain,(
    ! [A_994] : ~ r2_hidden(A_994,'#skF_5') ),
    inference(splitRight,[status(thm)],[c_16752])).

tff(c_19084,plain,(
    v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_4,c_19079])).

tff(c_19091,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_19084,c_8])).

tff(c_19101,plain,(
    ! [A_8] : m1_subset_1('#skF_5',k1_zfmisc_1(A_8)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_19091,c_12])).

tff(c_20132,plain,(
    ! [A_1069,B_1070,C_1071] :
      ( k2_relset_1(A_1069,B_1070,C_1071) = k2_relat_1(C_1071)
      | ~ m1_subset_1(C_1071,k1_zfmisc_1(k2_zfmisc_1(A_1069,B_1070))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_20155,plain,(
    ! [A_1072,B_1073] : k2_relset_1(A_1072,B_1073,'#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_19101,c_20132])).

tff(c_20159,plain,(
    k2_relat_1('#skF_5') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_20155,c_70])).

tff(c_19326,plain,(
    ! [A_1010,B_1011,C_1012] :
      ( k1_relset_1(A_1010,B_1011,C_1012) = k1_relat_1(C_1012)
      | ~ m1_subset_1(C_1012,k1_zfmisc_1(k2_zfmisc_1(A_1010,B_1011))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_19345,plain,(
    k1_relset_1('#skF_4','#skF_3',k2_funct_1('#skF_5')) = k1_relat_1(k2_funct_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_16695,c_19326])).

tff(c_21013,plain,(
    ! [B_1134,C_1135,A_1136] :
      ( B_1134 = '#skF_5'
      | v1_funct_2(C_1135,A_1136,B_1134)
      | k1_relset_1(A_1136,B_1134,C_1135) != A_1136
      | ~ m1_subset_1(C_1135,k1_zfmisc_1(k2_zfmisc_1(A_1136,B_1134))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_19091,c_44])).

tff(c_21038,plain,
    ( '#skF_5' = '#skF_3'
    | v1_funct_2(k2_funct_1('#skF_5'),'#skF_4','#skF_3')
    | k1_relset_1('#skF_4','#skF_3',k2_funct_1('#skF_5')) != '#skF_4' ),
    inference(resolution,[status(thm)],[c_16695,c_21013])).

tff(c_21045,plain,
    ( '#skF_5' = '#skF_3'
    | v1_funct_2(k2_funct_1('#skF_5'),'#skF_4','#skF_3')
    | k1_relat_1(k2_funct_1('#skF_5')) != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_19345,c_21038])).

tff(c_21046,plain,
    ( '#skF_5' = '#skF_3'
    | k1_relat_1(k2_funct_1('#skF_5')) != '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_16694,c_21045])).

tff(c_21047,plain,(
    k1_relat_1(k2_funct_1('#skF_5')) != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_21046])).

tff(c_21050,plain,
    ( k2_relat_1('#skF_5') != '#skF_4'
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_21047])).

tff(c_21053,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16711,c_78,c_72,c_20159,c_21050])).

tff(c_21054,plain,(
    '#skF_5' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_21046])).

tff(c_21105,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_21054,c_16694])).

tff(c_21103,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_21054,c_16711])).

tff(c_21109,plain,(
    v1_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_21054,c_78])).

tff(c_21108,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_21054,c_72])).

tff(c_16714,plain,(
    ! [A_830,B_831] : m1_subset_1('#skF_2'(A_830,B_831),k1_zfmisc_1(k2_zfmisc_1(A_830,B_831))) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_16720,plain,(
    ! [B_71] : m1_subset_1('#skF_2'(k1_xboole_0,B_71),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_186,c_16714])).

tff(c_16738,plain,(
    ! [A_836,B_71] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(A_836,'#skF_2'(k1_xboole_0,B_71)) ) ),
    inference(resolution,[status(thm)],[c_16720,c_16736])).

tff(c_16762,plain,(
    ! [A_838,B_839] : ~ r2_hidden(A_838,'#skF_2'(k1_xboole_0,B_839)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_16738])).

tff(c_16768,plain,(
    ! [B_840] : v1_xboole_0('#skF_2'(k1_xboole_0,B_840)) ),
    inference(resolution,[status(thm)],[c_4,c_16762])).

tff(c_16775,plain,(
    ! [B_840] : '#skF_2'(k1_xboole_0,B_840) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_16768,c_8])).

tff(c_19095,plain,(
    ! [B_840] : '#skF_2'('#skF_5',B_840) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_19091,c_19091,c_16775])).

tff(c_19343,plain,(
    ! [A_1010,B_1011] : k1_relset_1(A_1010,B_1011,'#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_19101,c_19326])).

tff(c_19098,plain,(
    ! [B_71] : k2_zfmisc_1('#skF_5',B_71) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_19091,c_19091,c_186])).

tff(c_20882,plain,(
    ! [B_1128,C_1129] :
      ( k1_relset_1('#skF_5',B_1128,C_1129) = '#skF_5'
      | ~ v1_funct_2(C_1129,'#skF_5',B_1128)
      | ~ m1_subset_1(C_1129,k1_zfmisc_1('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_19098,c_19091,c_19091,c_19091,c_19091,c_46])).

tff(c_20890,plain,(
    ! [B_31] :
      ( k1_relset_1('#skF_5',B_31,'#skF_2'('#skF_5',B_31)) = '#skF_5'
      | ~ m1_subset_1('#skF_2'('#skF_5',B_31),k1_zfmisc_1('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_50,c_20882])).

tff(c_20900,plain,(
    k1_relat_1('#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_19101,c_19095,c_19343,c_19095,c_20890])).

tff(c_21060,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_21054,c_21054,c_20900])).

tff(c_16710,plain,(
    v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_16695,c_16697])).

tff(c_21102,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_21054,c_16710])).

tff(c_21106,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_21054,c_172])).

tff(c_21079,plain,(
    k2_relat_1('#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_21054,c_20159])).

tff(c_19257,plain,(
    ! [A_1008] :
      ( k1_relat_1(k2_funct_1(A_1008)) = k2_relat_1(A_1008)
      | ~ v2_funct_1(A_1008)
      | ~ v1_funct_1(A_1008)
      | ~ v1_relat_1(A_1008) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_21654,plain,(
    ! [A_1166] :
      ( v1_funct_2(k2_funct_1(A_1166),k2_relat_1(A_1166),k2_relat_1(k2_funct_1(A_1166)))
      | ~ v1_funct_1(k2_funct_1(A_1166))
      | ~ v1_relat_1(k2_funct_1(A_1166))
      | ~ v2_funct_1(A_1166)
      | ~ v1_funct_1(A_1166)
      | ~ v1_relat_1(A_1166) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_19257,c_64])).

tff(c_21657,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_4',k2_relat_1(k2_funct_1('#skF_3')))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_21079,c_21654])).

tff(c_21665,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),'#skF_4',k2_relat_1(k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_21103,c_21109,c_21108,c_21102,c_21106,c_21657])).

tff(c_21669,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_4',k1_relat_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_21665])).

tff(c_21671,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),'#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_21103,c_21109,c_21108,c_21060,c_21669])).

tff(c_21673,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_21105,c_21671])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:11:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.16/3.37  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.61/3.43  
% 9.61/3.43  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.61/3.43  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2
% 9.61/3.43  
% 9.61/3.43  %Foreground sorts:
% 9.61/3.43  
% 9.61/3.43  
% 9.61/3.43  %Background operators:
% 9.61/3.43  
% 9.61/3.43  
% 9.61/3.43  %Foreground operators:
% 9.61/3.43  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 9.61/3.43  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 9.61/3.43  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 9.61/3.43  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 9.61/3.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.61/3.43  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.61/3.43  tff('#skF_1', type, '#skF_1': $i > $i).
% 9.61/3.43  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.61/3.43  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 9.61/3.43  tff('#skF_5', type, '#skF_5': $i).
% 9.61/3.43  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 9.61/3.43  tff('#skF_3', type, '#skF_3': $i).
% 9.61/3.43  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 9.61/3.43  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 9.61/3.43  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.61/3.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.61/3.43  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 9.61/3.43  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 9.61/3.43  tff('#skF_4', type, '#skF_4': $i).
% 9.61/3.43  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 9.61/3.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.61/3.43  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 9.61/3.43  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 9.61/3.43  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 9.61/3.43  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 9.61/3.43  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.61/3.43  
% 9.61/3.47  tff(f_148, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_funct_2)).
% 9.61/3.47  tff(f_82, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 9.61/3.47  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 9.61/3.47  tff(f_40, axiom, (![A, B]: (v1_xboole_0(A) => v1_xboole_0(k2_zfmisc_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_zfmisc_1)).
% 9.61/3.47  tff(f_55, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 9.61/3.47  tff(f_90, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 9.61/3.47  tff(f_78, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 9.61/3.47  tff(f_64, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 9.61/3.47  tff(f_86, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 9.61/3.47  tff(f_108, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 9.61/3.47  tff(f_131, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_funct_2)).
% 9.61/3.47  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 9.61/3.47  tff(f_42, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 9.61/3.47  tff(f_36, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 9.61/3.47  tff(f_121, axiom, (![A, B]: (?[C]: (((((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & v1_relat_1(C)) & v4_relat_1(C, A)) & v5_relat_1(C, B)) & v1_funct_1(C)) & v1_funct_2(C, A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc1_funct_2)).
% 9.61/3.47  tff(c_74, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_148])).
% 9.61/3.47  tff(c_16697, plain, (![C_827, A_828, B_829]: (v1_relat_1(C_827) | ~m1_subset_1(C_827, k1_zfmisc_1(k2_zfmisc_1(A_828, B_829))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 9.61/3.47  tff(c_16711, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_74, c_16697])).
% 9.61/3.47  tff(c_78, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_148])).
% 9.61/3.47  tff(c_72, plain, (v2_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_148])).
% 9.61/3.47  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.61/3.47  tff(c_10, plain, (![A_6, B_7]: (v1_xboole_0(k2_zfmisc_1(A_6, B_7)) | ~v1_xboole_0(A_6))), inference(cnfTransformation, [status(thm)], [f_40])).
% 9.61/3.47  tff(c_16736, plain, (![C_834, B_835, A_836]: (~v1_xboole_0(C_834) | ~m1_subset_1(B_835, k1_zfmisc_1(C_834)) | ~r2_hidden(A_836, B_835))), inference(cnfTransformation, [status(thm)], [f_55])).
% 9.61/3.47  tff(c_16752, plain, (![A_836]: (~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4')) | ~r2_hidden(A_836, '#skF_5'))), inference(resolution, [status(thm)], [c_74, c_16736])).
% 9.61/3.47  tff(c_16822, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_16752])).
% 9.61/3.47  tff(c_16826, plain, (~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_10, c_16822])).
% 9.61/3.47  tff(c_70, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_4'), inference(cnfTransformation, [status(thm)], [f_148])).
% 9.61/3.47  tff(c_17946, plain, (![A_941, B_942, C_943]: (k2_relset_1(A_941, B_942, C_943)=k2_relat_1(C_943) | ~m1_subset_1(C_943, k1_zfmisc_1(k2_zfmisc_1(A_941, B_942))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 9.61/3.47  tff(c_17967, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_74, c_17946])).
% 9.61/3.47  tff(c_17976, plain, (k2_relat_1('#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_17967])).
% 9.61/3.47  tff(c_30, plain, (![A_17]: (k1_relat_1(k2_funct_1(A_17))=k2_relat_1(A_17) | ~v2_funct_1(A_17) | ~v1_funct_1(A_17) | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_78])).
% 9.61/3.47  tff(c_225, plain, (![C_81, B_82, A_83]: (~v1_xboole_0(C_81) | ~m1_subset_1(B_82, k1_zfmisc_1(C_81)) | ~r2_hidden(A_83, B_82))), inference(cnfTransformation, [status(thm)], [f_55])).
% 9.61/3.47  tff(c_238, plain, (![A_83]: (~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4')) | ~r2_hidden(A_83, '#skF_5'))), inference(resolution, [status(thm)], [c_74, c_225])).
% 9.61/3.47  tff(c_248, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_238])).
% 9.61/3.47  tff(c_252, plain, (~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_10, c_248])).
% 9.61/3.47  tff(c_76, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_148])).
% 9.61/3.47  tff(c_140, plain, (![A_58]: (v1_funct_1(k2_funct_1(A_58)) | ~v1_funct_1(A_58) | ~v1_relat_1(A_58))), inference(cnfTransformation, [status(thm)], [f_64])).
% 9.61/3.47  tff(c_68, plain, (~m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3'))) | ~v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', '#skF_3') | ~v1_funct_1(k2_funct_1('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_148])).
% 9.61/3.47  tff(c_112, plain, (~v1_funct_1(k2_funct_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_68])).
% 9.61/3.47  tff(c_143, plain, (~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_140, c_112])).
% 9.61/3.47  tff(c_146, plain, (~v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_143])).
% 9.61/3.47  tff(c_152, plain, (![C_62, A_63, B_64]: (v1_relat_1(C_62) | ~m1_subset_1(C_62, k1_zfmisc_1(k2_zfmisc_1(A_63, B_64))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 9.61/3.47  tff(c_160, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_74, c_152])).
% 9.61/3.47  tff(c_170, plain, $false, inference(negUnitSimplification, [status(thm)], [c_146, c_160])).
% 9.61/3.47  tff(c_171, plain, (~v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', '#skF_3') | ~m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(splitRight, [status(thm)], [c_68])).
% 9.61/3.47  tff(c_200, plain, (~m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(splitLeft, [status(thm)], [c_171])).
% 9.61/3.47  tff(c_207, plain, (![C_78, A_79, B_80]: (v1_relat_1(C_78) | ~m1_subset_1(C_78, k1_zfmisc_1(k2_zfmisc_1(A_79, B_80))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 9.61/3.47  tff(c_222, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_74, c_207])).
% 9.61/3.47  tff(c_729, plain, (![A_144, B_145, C_146]: (k2_relset_1(A_144, B_145, C_146)=k2_relat_1(C_146) | ~m1_subset_1(C_146, k1_zfmisc_1(k2_zfmisc_1(A_144, B_145))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 9.61/3.47  tff(c_744, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_74, c_729])).
% 9.61/3.47  tff(c_751, plain, (k2_relat_1('#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_744])).
% 9.61/3.47  tff(c_22, plain, (![A_15]: (v1_relat_1(k2_funct_1(A_15)) | ~v1_funct_1(A_15) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_64])).
% 9.61/3.47  tff(c_172, plain, (v1_funct_1(k2_funct_1('#skF_5'))), inference(splitRight, [status(thm)], [c_68])).
% 9.61/3.47  tff(c_665, plain, (![A_133, B_134, C_135]: (k1_relset_1(A_133, B_134, C_135)=k1_relat_1(C_135) | ~m1_subset_1(C_135, k1_zfmisc_1(k2_zfmisc_1(A_133, B_134))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 9.61/3.47  tff(c_686, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_74, c_665])).
% 9.61/3.47  tff(c_1394, plain, (![B_188, A_189, C_190]: (k1_xboole_0=B_188 | k1_relset_1(A_189, B_188, C_190)=A_189 | ~v1_funct_2(C_190, A_189, B_188) | ~m1_subset_1(C_190, k1_zfmisc_1(k2_zfmisc_1(A_189, B_188))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 9.61/3.47  tff(c_1415, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_3' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_74, c_1394])).
% 9.61/3.47  tff(c_1429, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_76, c_686, c_1415])).
% 9.61/3.47  tff(c_1432, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(splitLeft, [status(thm)], [c_1429])).
% 9.61/3.47  tff(c_421, plain, (![A_112]: (k2_relat_1(k2_funct_1(A_112))=k1_relat_1(A_112) | ~v2_funct_1(A_112) | ~v1_funct_1(A_112) | ~v1_relat_1(A_112))), inference(cnfTransformation, [status(thm)], [f_78])).
% 9.61/3.47  tff(c_64, plain, (![A_33]: (v1_funct_2(A_33, k1_relat_1(A_33), k2_relat_1(A_33)) | ~v1_funct_1(A_33) | ~v1_relat_1(A_33))), inference(cnfTransformation, [status(thm)], [f_131])).
% 9.61/3.47  tff(c_4794, plain, (![A_295]: (v1_funct_2(k2_funct_1(A_295), k1_relat_1(k2_funct_1(A_295)), k1_relat_1(A_295)) | ~v1_funct_1(k2_funct_1(A_295)) | ~v1_relat_1(k2_funct_1(A_295)) | ~v2_funct_1(A_295) | ~v1_funct_1(A_295) | ~v1_relat_1(A_295))), inference(superposition, [status(thm), theory('equality')], [c_421, c_64])).
% 9.61/3.47  tff(c_4809, plain, (v1_funct_2(k2_funct_1('#skF_5'), k1_relat_1(k2_funct_1('#skF_5')), '#skF_3') | ~v1_funct_1(k2_funct_1('#skF_5')) | ~v1_relat_1(k2_funct_1('#skF_5')) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1432, c_4794])).
% 9.61/3.47  tff(c_4831, plain, (v1_funct_2(k2_funct_1('#skF_5'), k1_relat_1(k2_funct_1('#skF_5')), '#skF_3') | ~v1_relat_1(k2_funct_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_222, c_78, c_72, c_172, c_4809])).
% 9.61/3.47  tff(c_4836, plain, (~v1_relat_1(k2_funct_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_4831])).
% 9.61/3.47  tff(c_4839, plain, (~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_22, c_4836])).
% 9.61/3.47  tff(c_4843, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_222, c_78, c_4839])).
% 9.61/3.47  tff(c_4845, plain, (v1_relat_1(k2_funct_1('#skF_5'))), inference(splitRight, [status(thm)], [c_4831])).
% 9.61/3.47  tff(c_28, plain, (![A_17]: (k2_relat_1(k2_funct_1(A_17))=k1_relat_1(A_17) | ~v2_funct_1(A_17) | ~v1_funct_1(A_17) | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_78])).
% 9.61/3.47  tff(c_769, plain, (![A_149]: (m1_subset_1(A_149, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_149), k2_relat_1(A_149)))) | ~v1_funct_1(A_149) | ~v1_relat_1(A_149))), inference(cnfTransformation, [status(thm)], [f_131])).
% 9.61/3.47  tff(c_7089, plain, (![A_354]: (m1_subset_1(k2_funct_1(A_354), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(A_354)), k1_relat_1(A_354)))) | ~v1_funct_1(k2_funct_1(A_354)) | ~v1_relat_1(k2_funct_1(A_354)) | ~v2_funct_1(A_354) | ~v1_funct_1(A_354) | ~v1_relat_1(A_354))), inference(superposition, [status(thm), theory('equality')], [c_28, c_769])).
% 9.61/3.47  tff(c_7132, plain, (m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_5')), '#skF_3'))) | ~v1_funct_1(k2_funct_1('#skF_5')) | ~v1_relat_1(k2_funct_1('#skF_5')) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1432, c_7089])).
% 9.61/3.47  tff(c_7167, plain, (m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_5')), '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_222, c_78, c_72, c_4845, c_172, c_7132])).
% 9.61/3.47  tff(c_7193, plain, (m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_5'), '#skF_3'))) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_30, c_7167])).
% 9.61/3.47  tff(c_7206, plain, (m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_222, c_78, c_72, c_751, c_7193])).
% 9.61/3.47  tff(c_7208, plain, $false, inference(negUnitSimplification, [status(thm)], [c_200, c_7206])).
% 9.61/3.47  tff(c_7209, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_1429])).
% 9.61/3.47  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 9.61/3.47  tff(c_7253, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_7209, c_6])).
% 9.61/3.47  tff(c_12, plain, (![A_8]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 9.61/3.47  tff(c_173, plain, (![A_65, B_66]: (v1_xboole_0(k2_zfmisc_1(A_65, B_66)) | ~v1_xboole_0(A_65))), inference(cnfTransformation, [status(thm)], [f_40])).
% 9.61/3.47  tff(c_8, plain, (![A_5]: (k1_xboole_0=A_5 | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_36])).
% 9.61/3.47  tff(c_180, plain, (![A_70, B_71]: (k2_zfmisc_1(A_70, B_71)=k1_xboole_0 | ~v1_xboole_0(A_70))), inference(resolution, [status(thm)], [c_173, c_8])).
% 9.61/3.47  tff(c_186, plain, (![B_71]: (k2_zfmisc_1(k1_xboole_0, B_71)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_180])).
% 9.61/3.47  tff(c_202, plain, (![A_75, B_76]: (m1_subset_1('#skF_2'(A_75, B_76), k1_zfmisc_1(k2_zfmisc_1(A_75, B_76))))), inference(cnfTransformation, [status(thm)], [f_121])).
% 9.61/3.47  tff(c_205, plain, (![B_71]: (m1_subset_1('#skF_2'(k1_xboole_0, B_71), k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_186, c_202])).
% 9.61/3.47  tff(c_227, plain, (![A_83, B_71]: (~v1_xboole_0(k1_xboole_0) | ~r2_hidden(A_83, '#skF_2'(k1_xboole_0, B_71)))), inference(resolution, [status(thm)], [c_205, c_225])).
% 9.61/3.47  tff(c_253, plain, (![A_85, B_86]: (~r2_hidden(A_85, '#skF_2'(k1_xboole_0, B_86)))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_227])).
% 9.61/3.47  tff(c_259, plain, (![B_87]: (v1_xboole_0('#skF_2'(k1_xboole_0, B_87)))), inference(resolution, [status(thm)], [c_4, c_253])).
% 9.61/3.47  tff(c_266, plain, (![B_87]: ('#skF_2'(k1_xboole_0, B_87)=k1_xboole_0)), inference(resolution, [status(thm)], [c_259, c_8])).
% 9.61/3.47  tff(c_687, plain, (![A_133, B_134]: (k1_relset_1(A_133, B_134, k1_xboole_0)=k1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_12, c_665])).
% 9.61/3.47  tff(c_50, plain, (![A_30, B_31]: (v1_funct_2('#skF_2'(A_30, B_31), A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_121])).
% 9.61/3.47  tff(c_46, plain, (![B_28, C_29]: (k1_relset_1(k1_xboole_0, B_28, C_29)=k1_xboole_0 | ~v1_funct_2(C_29, k1_xboole_0, B_28) | ~m1_subset_1(C_29, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_28))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 9.61/3.47  tff(c_1172, plain, (![B_174, C_175]: (k1_relset_1(k1_xboole_0, B_174, C_175)=k1_xboole_0 | ~v1_funct_2(C_175, k1_xboole_0, B_174) | ~m1_subset_1(C_175, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_186, c_46])).
% 9.61/3.47  tff(c_1180, plain, (![B_31]: (k1_relset_1(k1_xboole_0, B_31, '#skF_2'(k1_xboole_0, B_31))=k1_xboole_0 | ~m1_subset_1('#skF_2'(k1_xboole_0, B_31), k1_zfmisc_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_50, c_1172])).
% 9.61/3.47  tff(c_1190, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_12, c_266, c_687, c_266, c_1180])).
% 9.61/3.47  tff(c_7219, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_7209, c_7209, c_1190])).
% 9.61/3.47  tff(c_40, plain, (![C_29, A_27]: (k1_xboole_0=C_29 | ~v1_funct_2(C_29, A_27, k1_xboole_0) | k1_xboole_0=A_27 | ~m1_subset_1(C_29, k1_zfmisc_1(k2_zfmisc_1(A_27, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 9.61/3.47  tff(c_9060, plain, (![C_444, A_445]: (C_444='#skF_4' | ~v1_funct_2(C_444, A_445, '#skF_4') | A_445='#skF_4' | ~m1_subset_1(C_444, k1_zfmisc_1(k2_zfmisc_1(A_445, '#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_7209, c_7209, c_7209, c_7209, c_40])).
% 9.61/3.47  tff(c_9090, plain, ('#skF_5'='#skF_4' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4') | '#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_74, c_9060])).
% 9.61/3.47  tff(c_9101, plain, ('#skF_5'='#skF_4' | '#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_76, c_9090])).
% 9.61/3.47  tff(c_9102, plain, ('#skF_3'='#skF_4'), inference(splitLeft, [status(thm)], [c_9101])).
% 9.61/3.47  tff(c_9106, plain, (~v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_9102, c_252])).
% 9.61/3.47  tff(c_9114, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7253, c_9106])).
% 9.61/3.47  tff(c_9115, plain, ('#skF_5'='#skF_4'), inference(splitRight, [status(thm)], [c_9101])).
% 9.61/3.47  tff(c_785, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'), '#skF_4'))) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_751, c_769])).
% 9.61/3.47  tff(c_798, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'), '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_222, c_78, c_785])).
% 9.61/3.47  tff(c_16, plain, (![C_14, B_13, A_12]: (~v1_xboole_0(C_14) | ~m1_subset_1(B_13, k1_zfmisc_1(C_14)) | ~r2_hidden(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_55])).
% 9.61/3.47  tff(c_816, plain, (![A_12]: (~v1_xboole_0(k2_zfmisc_1(k1_relat_1('#skF_5'), '#skF_4')) | ~r2_hidden(A_12, '#skF_5'))), inference(resolution, [status(thm)], [c_798, c_16])).
% 9.61/3.47  tff(c_827, plain, (~v1_xboole_0(k2_zfmisc_1(k1_relat_1('#skF_5'), '#skF_4'))), inference(splitLeft, [status(thm)], [c_816])).
% 9.61/3.47  tff(c_831, plain, (~v1_xboole_0(k1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_10, c_827])).
% 9.61/3.47  tff(c_9120, plain, (~v1_xboole_0(k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_9115, c_831])).
% 9.61/3.47  tff(c_9140, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7253, c_7219, c_9120])).
% 9.61/3.47  tff(c_9144, plain, (![A_447]: (~r2_hidden(A_447, '#skF_5'))), inference(splitRight, [status(thm)], [c_816])).
% 9.61/3.47  tff(c_9149, plain, (v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_4, c_9144])).
% 9.61/3.47  tff(c_9159, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_9149, c_8])).
% 9.61/3.47  tff(c_9510, plain, (![A_466, B_467]: (k1_relset_1(A_466, B_467, '#skF_5')=k1_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_9159, c_9159, c_687])).
% 9.61/3.47  tff(c_9180, plain, (![A_8]: (m1_subset_1('#skF_5', k1_zfmisc_1(A_8)))), inference(demodulation, [status(thm), theory('equality')], [c_9159, c_12])).
% 9.61/3.47  tff(c_60, plain, (![A_30, B_31]: (m1_subset_1('#skF_2'(A_30, B_31), k1_zfmisc_1(k2_zfmisc_1(A_30, B_31))))), inference(cnfTransformation, [status(thm)], [f_121])).
% 9.61/3.47  tff(c_350, plain, (![A_99, B_100, A_101]: (~v1_xboole_0(k2_zfmisc_1(A_99, B_100)) | ~r2_hidden(A_101, '#skF_2'(A_99, B_100)))), inference(resolution, [status(thm)], [c_60, c_225])).
% 9.61/3.47  tff(c_361, plain, (![A_102, B_103]: (~v1_xboole_0(k2_zfmisc_1(A_102, B_103)) | v1_xboole_0('#skF_2'(A_102, B_103)))), inference(resolution, [status(thm)], [c_4, c_350])).
% 9.61/3.47  tff(c_377, plain, (![A_105, B_106]: (v1_xboole_0('#skF_2'(A_105, B_106)) | ~v1_xboole_0(A_105))), inference(resolution, [status(thm)], [c_10, c_361])).
% 9.61/3.47  tff(c_387, plain, (![A_105, B_106]: ('#skF_2'(A_105, B_106)=k1_xboole_0 | ~v1_xboole_0(A_105))), inference(resolution, [status(thm)], [c_377, c_8])).
% 9.61/3.47  tff(c_9157, plain, (![B_106]: ('#skF_2'('#skF_5', B_106)=k1_xboole_0)), inference(resolution, [status(thm)], [c_9149, c_387])).
% 9.61/3.47  tff(c_9282, plain, (![B_106]: ('#skF_2'('#skF_5', B_106)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_9159, c_9157])).
% 9.61/3.47  tff(c_9177, plain, (![B_71]: (k2_zfmisc_1('#skF_5', B_71)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_9159, c_9159, c_186])).
% 9.61/3.47  tff(c_9464, plain, (![B_460, C_461]: (k1_relset_1('#skF_5', B_460, C_461)='#skF_5' | ~v1_funct_2(C_461, '#skF_5', B_460) | ~m1_subset_1(C_461, k1_zfmisc_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_9177, c_9159, c_9159, c_9159, c_9159, c_46])).
% 9.61/3.47  tff(c_9469, plain, (![B_31]: (k1_relset_1('#skF_5', B_31, '#skF_2'('#skF_5', B_31))='#skF_5' | ~m1_subset_1('#skF_2'('#skF_5', B_31), k1_zfmisc_1('#skF_5')))), inference(resolution, [status(thm)], [c_50, c_9464])).
% 9.61/3.47  tff(c_9475, plain, (![B_31]: (k1_relset_1('#skF_5', B_31, '#skF_5')='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_9180, c_9282, c_9282, c_9469])).
% 9.61/3.47  tff(c_9515, plain, (k1_relat_1('#skF_5')='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_9510, c_9475])).
% 9.61/3.47  tff(c_9162, plain, (![A_133, B_134]: (k1_relset_1(A_133, B_134, '#skF_5')=k1_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_9159, c_9159, c_687])).
% 9.61/3.47  tff(c_9522, plain, (![A_133, B_134]: (k1_relset_1(A_133, B_134, '#skF_5')='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_9515, c_9162])).
% 9.61/3.47  tff(c_48, plain, (![B_28, A_27, C_29]: (k1_xboole_0=B_28 | k1_relset_1(A_27, B_28, C_29)=A_27 | ~v1_funct_2(C_29, A_27, B_28) | ~m1_subset_1(C_29, k1_zfmisc_1(k2_zfmisc_1(A_27, B_28))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 9.61/3.47  tff(c_9555, plain, (![B_470, A_471, C_472]: (B_470='#skF_5' | k1_relset_1(A_471, B_470, C_472)=A_471 | ~v1_funct_2(C_472, A_471, B_470) | ~m1_subset_1(C_472, k1_zfmisc_1(k2_zfmisc_1(A_471, B_470))))), inference(demodulation, [status(thm), theory('equality')], [c_9159, c_48])).
% 9.61/3.47  tff(c_9559, plain, (![B_470, A_471]: (B_470='#skF_5' | k1_relset_1(A_471, B_470, '#skF_5')=A_471 | ~v1_funct_2('#skF_5', A_471, B_470))), inference(resolution, [status(thm)], [c_9180, c_9555])).
% 9.61/3.47  tff(c_10169, plain, (![B_513, A_514]: (B_513='#skF_5' | A_514='#skF_5' | ~v1_funct_2('#skF_5', A_514, B_513))), inference(demodulation, [status(thm), theory('equality')], [c_9522, c_9559])).
% 9.61/3.47  tff(c_10198, plain, ('#skF_5'='#skF_4' | '#skF_5'='#skF_3'), inference(resolution, [status(thm)], [c_76, c_10169])).
% 9.61/3.47  tff(c_10199, plain, ('#skF_5'='#skF_3'), inference(splitLeft, [status(thm)], [c_10198])).
% 9.61/3.47  tff(c_10236, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_10199, c_9149])).
% 9.61/3.47  tff(c_10246, plain, $false, inference(negUnitSimplification, [status(thm)], [c_252, c_10236])).
% 9.61/3.47  tff(c_10247, plain, ('#skF_5'='#skF_4'), inference(splitRight, [status(thm)], [c_10198])).
% 9.61/3.47  tff(c_10278, plain, (![B_71]: (k2_zfmisc_1('#skF_4', B_71)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_10247, c_10247, c_9177])).
% 9.61/3.47  tff(c_10289, plain, (~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_10247, c_200])).
% 9.61/3.47  tff(c_10570, plain, (~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_10278, c_10289])).
% 9.61/3.47  tff(c_10288, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_10247, c_222])).
% 9.61/3.47  tff(c_10293, plain, (v1_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_10247, c_78])).
% 9.61/3.47  tff(c_10292, plain, (v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_10247, c_72])).
% 9.61/3.47  tff(c_10290, plain, (v1_funct_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_10247, c_172])).
% 9.61/3.47  tff(c_10287, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_10247, c_751])).
% 9.61/3.47  tff(c_554, plain, (![A_124]: (k1_relat_1(k2_funct_1(A_124))=k2_relat_1(A_124) | ~v2_funct_1(A_124) | ~v1_funct_1(A_124) | ~v1_relat_1(A_124))), inference(cnfTransformation, [status(thm)], [f_78])).
% 9.61/3.47  tff(c_10757, plain, (![A_544]: (v1_funct_2(k2_funct_1(A_544), k2_relat_1(A_544), k2_relat_1(k2_funct_1(A_544))) | ~v1_funct_1(k2_funct_1(A_544)) | ~v1_relat_1(k2_funct_1(A_544)) | ~v2_funct_1(A_544) | ~v1_funct_1(A_544) | ~v1_relat_1(A_544))), inference(superposition, [status(thm), theory('equality')], [c_554, c_64])).
% 9.61/3.47  tff(c_10760, plain, (v1_funct_2(k2_funct_1('#skF_4'), '#skF_4', k2_relat_1(k2_funct_1('#skF_4'))) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_10287, c_10757])).
% 9.61/3.47  tff(c_10768, plain, (v1_funct_2(k2_funct_1('#skF_4'), '#skF_4', k2_relat_1(k2_funct_1('#skF_4'))) | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_10288, c_10293, c_10292, c_10290, c_10760])).
% 9.61/3.47  tff(c_10887, plain, (~v1_relat_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_10768])).
% 9.61/3.47  tff(c_10890, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_22, c_10887])).
% 9.61/3.47  tff(c_10894, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10288, c_10293, c_10890])).
% 9.61/3.47  tff(c_10896, plain, (v1_relat_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_10768])).
% 9.61/3.47  tff(c_11086, plain, (![A_564]: (m1_subset_1(k2_funct_1(A_564), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_564), k2_relat_1(k2_funct_1(A_564))))) | ~v1_funct_1(k2_funct_1(A_564)) | ~v1_relat_1(k2_funct_1(A_564)) | ~v2_funct_1(A_564) | ~v1_funct_1(A_564) | ~v1_relat_1(A_564))), inference(superposition, [status(thm), theory('equality')], [c_30, c_769])).
% 9.61/3.47  tff(c_11105, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', k2_relat_1(k2_funct_1('#skF_4'))))) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_10287, c_11086])).
% 9.61/3.47  tff(c_11120, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_10288, c_10293, c_10292, c_10896, c_10290, c_10278, c_11105])).
% 9.61/3.47  tff(c_11122, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10570, c_11120])).
% 9.61/3.47  tff(c_11124, plain, (v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_238])).
% 9.61/3.47  tff(c_11125, plain, (![A_565]: (~r2_hidden(A_565, '#skF_5'))), inference(splitRight, [status(thm)], [c_238])).
% 9.61/3.47  tff(c_11130, plain, (v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_4, c_11125])).
% 9.61/3.47  tff(c_11137, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_11130, c_8])).
% 9.61/3.47  tff(c_11195, plain, (![A_568]: (A_568='#skF_5' | ~v1_xboole_0(A_568))), inference(demodulation, [status(thm), theory('equality')], [c_11137, c_8])).
% 9.61/3.47  tff(c_11205, plain, (k2_zfmisc_1('#skF_3', '#skF_4')='#skF_5'), inference(resolution, [status(thm)], [c_11124, c_11195])).
% 9.61/3.47  tff(c_44, plain, (![B_28, C_29, A_27]: (k1_xboole_0=B_28 | v1_funct_2(C_29, A_27, B_28) | k1_relset_1(A_27, B_28, C_29)!=A_27 | ~m1_subset_1(C_29, k1_zfmisc_1(k2_zfmisc_1(A_27, B_28))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 9.61/3.47  tff(c_13607, plain, (![B_711, C_712, A_713]: (B_711='#skF_5' | v1_funct_2(C_712, A_713, B_711) | k1_relset_1(A_713, B_711, C_712)!=A_713 | ~m1_subset_1(C_712, k1_zfmisc_1(k2_zfmisc_1(A_713, B_711))))), inference(demodulation, [status(thm), theory('equality')], [c_11137, c_44])).
% 9.61/3.47  tff(c_13625, plain, (![C_712]: ('#skF_5'='#skF_4' | v1_funct_2(C_712, '#skF_3', '#skF_4') | k1_relset_1('#skF_3', '#skF_4', C_712)!='#skF_3' | ~m1_subset_1(C_712, k1_zfmisc_1('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_11205, c_13607])).
% 9.61/3.47  tff(c_13719, plain, ('#skF_5'='#skF_4'), inference(splitLeft, [status(thm)], [c_13625])).
% 9.61/3.47  tff(c_11140, plain, (![B_71]: (k2_zfmisc_1('#skF_5', B_71)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_11137, c_11137, c_186])).
% 9.61/3.47  tff(c_13774, plain, (![B_71]: (k2_zfmisc_1('#skF_4', B_71)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_13719, c_13719, c_11140])).
% 9.61/3.47  tff(c_13781, plain, (~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_13719, c_200])).
% 9.61/3.47  tff(c_13980, plain, (~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_13774, c_13781])).
% 9.61/3.47  tff(c_13780, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_13719, c_222])).
% 9.61/3.47  tff(c_13785, plain, (v1_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_13719, c_78])).
% 9.61/3.47  tff(c_13784, plain, (v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_13719, c_72])).
% 9.61/3.47  tff(c_13782, plain, (v1_funct_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_13719, c_172])).
% 9.61/3.47  tff(c_11143, plain, (![A_8]: (m1_subset_1('#skF_5', k1_zfmisc_1(A_8)))), inference(demodulation, [status(thm), theory('equality')], [c_11137, c_12])).
% 9.61/3.47  tff(c_11741, plain, (![A_620, B_621, C_622]: (k2_relset_1(A_620, B_621, C_622)=k2_relat_1(C_622) | ~m1_subset_1(C_622, k1_zfmisc_1(k2_zfmisc_1(A_620, B_621))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 9.61/3.47  tff(c_11763, plain, (![A_623, B_624]: (k2_relset_1(A_623, B_624, '#skF_5')=k2_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_11143, c_11741])).
% 9.61/3.47  tff(c_11767, plain, (k2_relat_1('#skF_5')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_11763, c_70])).
% 9.61/3.47  tff(c_13756, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_13719, c_11767])).
% 9.61/3.47  tff(c_11453, plain, (![A_595]: (k1_relat_1(k2_funct_1(A_595))=k2_relat_1(A_595) | ~v2_funct_1(A_595) | ~v1_funct_1(A_595) | ~v1_relat_1(A_595))), inference(cnfTransformation, [status(thm)], [f_78])).
% 9.61/3.47  tff(c_14447, plain, (![A_748]: (v1_funct_2(k2_funct_1(A_748), k2_relat_1(A_748), k2_relat_1(k2_funct_1(A_748))) | ~v1_funct_1(k2_funct_1(A_748)) | ~v1_relat_1(k2_funct_1(A_748)) | ~v2_funct_1(A_748) | ~v1_funct_1(A_748) | ~v1_relat_1(A_748))), inference(superposition, [status(thm), theory('equality')], [c_11453, c_64])).
% 9.61/3.47  tff(c_14450, plain, (v1_funct_2(k2_funct_1('#skF_4'), '#skF_4', k2_relat_1(k2_funct_1('#skF_4'))) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_13756, c_14447])).
% 9.61/3.47  tff(c_14464, plain, (v1_funct_2(k2_funct_1('#skF_4'), '#skF_4', k2_relat_1(k2_funct_1('#skF_4'))) | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_13780, c_13785, c_13784, c_13782, c_14450])).
% 9.61/3.47  tff(c_14487, plain, (~v1_relat_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_14464])).
% 9.61/3.47  tff(c_14490, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_22, c_14487])).
% 9.61/3.47  tff(c_14494, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_13780, c_13785, c_14490])).
% 9.61/3.47  tff(c_14496, plain, (v1_relat_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_14464])).
% 9.61/3.47  tff(c_11829, plain, (![A_632]: (m1_subset_1(A_632, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_632), k2_relat_1(A_632)))) | ~v1_funct_1(A_632) | ~v1_relat_1(A_632))), inference(cnfTransformation, [status(thm)], [f_131])).
% 9.61/3.47  tff(c_14613, plain, (![A_755]: (m1_subset_1(k2_funct_1(A_755), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_755), k2_relat_1(k2_funct_1(A_755))))) | ~v1_funct_1(k2_funct_1(A_755)) | ~v1_relat_1(k2_funct_1(A_755)) | ~v2_funct_1(A_755) | ~v1_funct_1(A_755) | ~v1_relat_1(A_755))), inference(superposition, [status(thm), theory('equality')], [c_30, c_11829])).
% 9.61/3.47  tff(c_14635, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', k2_relat_1(k2_funct_1('#skF_4'))))) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_13756, c_14613])).
% 9.61/3.47  tff(c_14657, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_13780, c_13785, c_13784, c_14496, c_13782, c_13774, c_14635])).
% 9.61/3.47  tff(c_14659, plain, $false, inference(negUnitSimplification, [status(thm)], [c_13980, c_14657])).
% 9.61/3.47  tff(c_14661, plain, ('#skF_5'!='#skF_4'), inference(splitRight, [status(thm)], [c_13625])).
% 9.61/3.47  tff(c_236, plain, (![A_83, B_71]: (~r2_hidden(A_83, '#skF_2'(k1_xboole_0, B_71)))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_227])).
% 9.61/3.47  tff(c_11232, plain, (![A_572, B_573]: (~r2_hidden(A_572, '#skF_2'('#skF_5', B_573)))), inference(demodulation, [status(thm), theory('equality')], [c_11137, c_236])).
% 9.61/3.47  tff(c_11238, plain, (![B_574]: (v1_xboole_0('#skF_2'('#skF_5', B_574)))), inference(resolution, [status(thm)], [c_4, c_11232])).
% 9.61/3.47  tff(c_11144, plain, (![A_5]: (A_5='#skF_5' | ~v1_xboole_0(A_5))), inference(demodulation, [status(thm), theory('equality')], [c_11137, c_8])).
% 9.61/3.47  tff(c_11242, plain, (![B_574]: ('#skF_2'('#skF_5', B_574)='#skF_5')), inference(resolution, [status(thm)], [c_11238, c_11144])).
% 9.61/3.47  tff(c_11540, plain, (![A_604, B_605, C_606]: (k1_relset_1(A_604, B_605, C_606)=k1_relat_1(C_606) | ~m1_subset_1(C_606, k1_zfmisc_1(k2_zfmisc_1(A_604, B_605))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 9.61/3.47  tff(c_11560, plain, (![A_604, B_605]: (k1_relset_1(A_604, B_605, '#skF_5')=k1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_11143, c_11540])).
% 9.61/3.47  tff(c_12544, plain, (![B_675, C_676]: (k1_relset_1('#skF_5', B_675, C_676)='#skF_5' | ~v1_funct_2(C_676, '#skF_5', B_675) | ~m1_subset_1(C_676, k1_zfmisc_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_11140, c_11137, c_11137, c_11137, c_11137, c_46])).
% 9.61/3.47  tff(c_12552, plain, (![B_31]: (k1_relset_1('#skF_5', B_31, '#skF_2'('#skF_5', B_31))='#skF_5' | ~m1_subset_1('#skF_2'('#skF_5', B_31), k1_zfmisc_1('#skF_5')))), inference(resolution, [status(thm)], [c_50, c_12544])).
% 9.61/3.47  tff(c_12562, plain, (k1_relat_1('#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_11143, c_11242, c_11560, c_11242, c_12552])).
% 9.61/3.47  tff(c_11223, plain, (m1_subset_1('#skF_2'('#skF_3', '#skF_4'), k1_zfmisc_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_11205, c_60])).
% 9.61/3.47  tff(c_11299, plain, (![A_12]: (~v1_xboole_0('#skF_5') | ~r2_hidden(A_12, '#skF_2'('#skF_3', '#skF_4')))), inference(resolution, [status(thm)], [c_11223, c_16])).
% 9.61/3.47  tff(c_11306, plain, (![A_583]: (~r2_hidden(A_583, '#skF_2'('#skF_3', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_11130, c_11299])).
% 9.61/3.47  tff(c_11311, plain, (v1_xboole_0('#skF_2'('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_4, c_11306])).
% 9.61/3.47  tff(c_11318, plain, ('#skF_2'('#skF_3', '#skF_4')='#skF_5'), inference(resolution, [status(thm)], [c_11311, c_11144])).
% 9.61/3.47  tff(c_11561, plain, (![A_30, B_31]: (k1_relset_1(A_30, B_31, '#skF_2'(A_30, B_31))=k1_relat_1('#skF_2'(A_30, B_31)))), inference(resolution, [status(thm)], [c_60, c_11540])).
% 9.61/3.47  tff(c_15496, plain, (![B_782, A_783, C_784]: (B_782='#skF_5' | k1_relset_1(A_783, B_782, C_784)=A_783 | ~v1_funct_2(C_784, A_783, B_782) | ~m1_subset_1(C_784, k1_zfmisc_1(k2_zfmisc_1(A_783, B_782))))), inference(demodulation, [status(thm), theory('equality')], [c_11137, c_48])).
% 9.61/3.47  tff(c_15527, plain, (![B_31, A_30]: (B_31='#skF_5' | k1_relset_1(A_30, B_31, '#skF_2'(A_30, B_31))=A_30 | ~v1_funct_2('#skF_2'(A_30, B_31), A_30, B_31))), inference(resolution, [status(thm)], [c_60, c_15496])).
% 9.61/3.47  tff(c_15537, plain, (![B_785, A_786]: (B_785='#skF_5' | k1_relat_1('#skF_2'(A_786, B_785))=A_786)), inference(demodulation, [status(thm), theory('equality')], [c_50, c_11561, c_15527])).
% 9.61/3.47  tff(c_15598, plain, ('#skF_5'='#skF_4' | k1_relat_1('#skF_5')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_11318, c_15537])).
% 9.61/3.47  tff(c_15617, plain, ('#skF_5'='#skF_4' | '#skF_5'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_12562, c_15598])).
% 9.61/3.47  tff(c_15618, plain, ('#skF_5'='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_14661, c_15617])).
% 9.61/3.47  tff(c_15690, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_15618, c_200])).
% 9.61/3.47  tff(c_15689, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_15618, c_222])).
% 9.61/3.47  tff(c_15694, plain, (v1_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_15618, c_78])).
% 9.61/3.47  tff(c_15693, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_15618, c_72])).
% 9.61/3.47  tff(c_15648, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_15618, c_15618, c_12562])).
% 9.61/3.47  tff(c_15691, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_15618, c_172])).
% 9.61/3.47  tff(c_15665, plain, (k2_relat_1('#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_15618, c_11767])).
% 9.61/3.47  tff(c_16355, plain, (![A_813]: (v1_funct_2(k2_funct_1(A_813), k2_relat_1(A_813), k2_relat_1(k2_funct_1(A_813))) | ~v1_funct_1(k2_funct_1(A_813)) | ~v1_relat_1(k2_funct_1(A_813)) | ~v2_funct_1(A_813) | ~v1_funct_1(A_813) | ~v1_relat_1(A_813))), inference(superposition, [status(thm), theory('equality')], [c_11453, c_64])).
% 9.61/3.47  tff(c_16358, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_4', k2_relat_1(k2_funct_1('#skF_3'))) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_15665, c_16355])).
% 9.61/3.47  tff(c_16372, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_4', k2_relat_1(k2_funct_1('#skF_3'))) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_15689, c_15694, c_15693, c_15691, c_16358])).
% 9.61/3.47  tff(c_16525, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_16372])).
% 9.61/3.47  tff(c_16528, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_22, c_16525])).
% 9.61/3.47  tff(c_16532, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_15689, c_15694, c_16528])).
% 9.61/3.47  tff(c_16534, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_16372])).
% 9.61/3.47  tff(c_16618, plain, (![A_825]: (m1_subset_1(k2_funct_1(A_825), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_825), k2_relat_1(k2_funct_1(A_825))))) | ~v1_funct_1(k2_funct_1(A_825)) | ~v1_relat_1(k2_funct_1(A_825)) | ~v2_funct_1(A_825) | ~v1_funct_1(A_825) | ~v1_relat_1(A_825))), inference(superposition, [status(thm), theory('equality')], [c_30, c_11829])).
% 9.61/3.47  tff(c_16637, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', k2_relat_1(k2_funct_1('#skF_3'))))) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_15665, c_16618])).
% 9.61/3.47  tff(c_16658, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', k2_relat_1(k2_funct_1('#skF_3')))))), inference(demodulation, [status(thm), theory('equality')], [c_15689, c_15694, c_15693, c_16534, c_15691, c_16637])).
% 9.61/3.47  tff(c_16683, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', k1_relat_1('#skF_3')))) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_28, c_16658])).
% 9.61/3.47  tff(c_16691, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_15689, c_15694, c_15693, c_15648, c_16683])).
% 9.61/3.47  tff(c_16693, plain, $false, inference(negUnitSimplification, [status(thm)], [c_15690, c_16691])).
% 9.61/3.47  tff(c_16694, plain, (~v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_171])).
% 9.61/3.47  tff(c_16695, plain, (m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(splitRight, [status(thm)], [c_171])).
% 9.61/3.47  tff(c_17857, plain, (![A_930, B_931, C_932]: (k1_relset_1(A_930, B_931, C_932)=k1_relat_1(C_932) | ~m1_subset_1(C_932, k1_zfmisc_1(k2_zfmisc_1(A_930, B_931))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 9.61/3.47  tff(c_17885, plain, (k1_relset_1('#skF_4', '#skF_3', k2_funct_1('#skF_5'))=k1_relat_1(k2_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_16695, c_17857])).
% 9.61/3.47  tff(c_18979, plain, (![B_990, C_991, A_992]: (k1_xboole_0=B_990 | v1_funct_2(C_991, A_992, B_990) | k1_relset_1(A_992, B_990, C_991)!=A_992 | ~m1_subset_1(C_991, k1_zfmisc_1(k2_zfmisc_1(A_992, B_990))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 9.61/3.47  tff(c_18997, plain, (k1_xboole_0='#skF_3' | v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', '#skF_3') | k1_relset_1('#skF_4', '#skF_3', k2_funct_1('#skF_5'))!='#skF_4'), inference(resolution, [status(thm)], [c_16695, c_18979])).
% 9.61/3.47  tff(c_19012, plain, (k1_xboole_0='#skF_3' | v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', '#skF_3') | k1_relat_1(k2_funct_1('#skF_5'))!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_17885, c_18997])).
% 9.61/3.47  tff(c_19013, plain, (k1_xboole_0='#skF_3' | k1_relat_1(k2_funct_1('#skF_5'))!='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_16694, c_19012])).
% 9.61/3.47  tff(c_19019, plain, (k1_relat_1(k2_funct_1('#skF_5'))!='#skF_4'), inference(splitLeft, [status(thm)], [c_19013])).
% 9.61/3.47  tff(c_19022, plain, (k2_relat_1('#skF_5')!='#skF_4' | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_30, c_19019])).
% 9.61/3.47  tff(c_19025, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16711, c_78, c_72, c_17976, c_19022])).
% 9.61/3.47  tff(c_19026, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_19013])).
% 9.61/3.47  tff(c_19073, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_19026, c_6])).
% 9.61/3.47  tff(c_19075, plain, $false, inference(negUnitSimplification, [status(thm)], [c_16826, c_19073])).
% 9.61/3.47  tff(c_19079, plain, (![A_994]: (~r2_hidden(A_994, '#skF_5'))), inference(splitRight, [status(thm)], [c_16752])).
% 9.61/3.47  tff(c_19084, plain, (v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_4, c_19079])).
% 9.61/3.47  tff(c_19091, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_19084, c_8])).
% 9.61/3.47  tff(c_19101, plain, (![A_8]: (m1_subset_1('#skF_5', k1_zfmisc_1(A_8)))), inference(demodulation, [status(thm), theory('equality')], [c_19091, c_12])).
% 9.61/3.47  tff(c_20132, plain, (![A_1069, B_1070, C_1071]: (k2_relset_1(A_1069, B_1070, C_1071)=k2_relat_1(C_1071) | ~m1_subset_1(C_1071, k1_zfmisc_1(k2_zfmisc_1(A_1069, B_1070))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 9.61/3.47  tff(c_20155, plain, (![A_1072, B_1073]: (k2_relset_1(A_1072, B_1073, '#skF_5')=k2_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_19101, c_20132])).
% 9.61/3.47  tff(c_20159, plain, (k2_relat_1('#skF_5')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_20155, c_70])).
% 9.61/3.47  tff(c_19326, plain, (![A_1010, B_1011, C_1012]: (k1_relset_1(A_1010, B_1011, C_1012)=k1_relat_1(C_1012) | ~m1_subset_1(C_1012, k1_zfmisc_1(k2_zfmisc_1(A_1010, B_1011))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 9.61/3.47  tff(c_19345, plain, (k1_relset_1('#skF_4', '#skF_3', k2_funct_1('#skF_5'))=k1_relat_1(k2_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_16695, c_19326])).
% 9.61/3.47  tff(c_21013, plain, (![B_1134, C_1135, A_1136]: (B_1134='#skF_5' | v1_funct_2(C_1135, A_1136, B_1134) | k1_relset_1(A_1136, B_1134, C_1135)!=A_1136 | ~m1_subset_1(C_1135, k1_zfmisc_1(k2_zfmisc_1(A_1136, B_1134))))), inference(demodulation, [status(thm), theory('equality')], [c_19091, c_44])).
% 9.61/3.47  tff(c_21038, plain, ('#skF_5'='#skF_3' | v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', '#skF_3') | k1_relset_1('#skF_4', '#skF_3', k2_funct_1('#skF_5'))!='#skF_4'), inference(resolution, [status(thm)], [c_16695, c_21013])).
% 9.61/3.47  tff(c_21045, plain, ('#skF_5'='#skF_3' | v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', '#skF_3') | k1_relat_1(k2_funct_1('#skF_5'))!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_19345, c_21038])).
% 9.61/3.47  tff(c_21046, plain, ('#skF_5'='#skF_3' | k1_relat_1(k2_funct_1('#skF_5'))!='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_16694, c_21045])).
% 9.61/3.47  tff(c_21047, plain, (k1_relat_1(k2_funct_1('#skF_5'))!='#skF_4'), inference(splitLeft, [status(thm)], [c_21046])).
% 9.61/3.47  tff(c_21050, plain, (k2_relat_1('#skF_5')!='#skF_4' | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_30, c_21047])).
% 9.61/3.47  tff(c_21053, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16711, c_78, c_72, c_20159, c_21050])).
% 9.61/3.47  tff(c_21054, plain, ('#skF_5'='#skF_3'), inference(splitRight, [status(thm)], [c_21046])).
% 9.61/3.47  tff(c_21105, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_21054, c_16694])).
% 9.61/3.47  tff(c_21103, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_21054, c_16711])).
% 9.61/3.47  tff(c_21109, plain, (v1_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_21054, c_78])).
% 9.61/3.47  tff(c_21108, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_21054, c_72])).
% 9.61/3.47  tff(c_16714, plain, (![A_830, B_831]: (m1_subset_1('#skF_2'(A_830, B_831), k1_zfmisc_1(k2_zfmisc_1(A_830, B_831))))), inference(cnfTransformation, [status(thm)], [f_121])).
% 9.61/3.47  tff(c_16720, plain, (![B_71]: (m1_subset_1('#skF_2'(k1_xboole_0, B_71), k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_186, c_16714])).
% 9.61/3.47  tff(c_16738, plain, (![A_836, B_71]: (~v1_xboole_0(k1_xboole_0) | ~r2_hidden(A_836, '#skF_2'(k1_xboole_0, B_71)))), inference(resolution, [status(thm)], [c_16720, c_16736])).
% 9.61/3.47  tff(c_16762, plain, (![A_838, B_839]: (~r2_hidden(A_838, '#skF_2'(k1_xboole_0, B_839)))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_16738])).
% 9.61/3.47  tff(c_16768, plain, (![B_840]: (v1_xboole_0('#skF_2'(k1_xboole_0, B_840)))), inference(resolution, [status(thm)], [c_4, c_16762])).
% 9.61/3.47  tff(c_16775, plain, (![B_840]: ('#skF_2'(k1_xboole_0, B_840)=k1_xboole_0)), inference(resolution, [status(thm)], [c_16768, c_8])).
% 9.61/3.47  tff(c_19095, plain, (![B_840]: ('#skF_2'('#skF_5', B_840)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_19091, c_19091, c_16775])).
% 9.61/3.47  tff(c_19343, plain, (![A_1010, B_1011]: (k1_relset_1(A_1010, B_1011, '#skF_5')=k1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_19101, c_19326])).
% 9.61/3.47  tff(c_19098, plain, (![B_71]: (k2_zfmisc_1('#skF_5', B_71)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_19091, c_19091, c_186])).
% 9.61/3.47  tff(c_20882, plain, (![B_1128, C_1129]: (k1_relset_1('#skF_5', B_1128, C_1129)='#skF_5' | ~v1_funct_2(C_1129, '#skF_5', B_1128) | ~m1_subset_1(C_1129, k1_zfmisc_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_19098, c_19091, c_19091, c_19091, c_19091, c_46])).
% 9.61/3.47  tff(c_20890, plain, (![B_31]: (k1_relset_1('#skF_5', B_31, '#skF_2'('#skF_5', B_31))='#skF_5' | ~m1_subset_1('#skF_2'('#skF_5', B_31), k1_zfmisc_1('#skF_5')))), inference(resolution, [status(thm)], [c_50, c_20882])).
% 9.61/3.47  tff(c_20900, plain, (k1_relat_1('#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_19101, c_19095, c_19343, c_19095, c_20890])).
% 9.61/3.47  tff(c_21060, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_21054, c_21054, c_20900])).
% 9.61/3.47  tff(c_16710, plain, (v1_relat_1(k2_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_16695, c_16697])).
% 9.61/3.47  tff(c_21102, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_21054, c_16710])).
% 9.61/3.47  tff(c_21106, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_21054, c_172])).
% 9.61/3.47  tff(c_21079, plain, (k2_relat_1('#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_21054, c_20159])).
% 9.61/3.47  tff(c_19257, plain, (![A_1008]: (k1_relat_1(k2_funct_1(A_1008))=k2_relat_1(A_1008) | ~v2_funct_1(A_1008) | ~v1_funct_1(A_1008) | ~v1_relat_1(A_1008))), inference(cnfTransformation, [status(thm)], [f_78])).
% 9.61/3.47  tff(c_21654, plain, (![A_1166]: (v1_funct_2(k2_funct_1(A_1166), k2_relat_1(A_1166), k2_relat_1(k2_funct_1(A_1166))) | ~v1_funct_1(k2_funct_1(A_1166)) | ~v1_relat_1(k2_funct_1(A_1166)) | ~v2_funct_1(A_1166) | ~v1_funct_1(A_1166) | ~v1_relat_1(A_1166))), inference(superposition, [status(thm), theory('equality')], [c_19257, c_64])).
% 9.61/3.47  tff(c_21657, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_4', k2_relat_1(k2_funct_1('#skF_3'))) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_21079, c_21654])).
% 9.61/3.47  tff(c_21665, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_4', k2_relat_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_21103, c_21109, c_21108, c_21102, c_21106, c_21657])).
% 9.61/3.47  tff(c_21669, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_4', k1_relat_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_28, c_21665])).
% 9.61/3.47  tff(c_21671, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_21103, c_21109, c_21108, c_21060, c_21669])).
% 9.61/3.47  tff(c_21673, plain, $false, inference(negUnitSimplification, [status(thm)], [c_21105, c_21671])).
% 9.61/3.47  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.61/3.47  
% 9.61/3.47  Inference rules
% 9.61/3.47  ----------------------
% 9.61/3.47  #Ref     : 0
% 9.61/3.47  #Sup     : 4930
% 9.61/3.47  #Fact    : 0
% 9.61/3.47  #Define  : 0
% 9.61/3.47  #Split   : 24
% 9.61/3.47  #Chain   : 0
% 9.61/3.47  #Close   : 0
% 9.61/3.47  
% 9.61/3.47  Ordering : KBO
% 9.61/3.47  
% 9.61/3.47  Simplification rules
% 9.61/3.47  ----------------------
% 9.61/3.47  #Subsume      : 1476
% 9.61/3.47  #Demod        : 5957
% 9.61/3.47  #Tautology    : 2432
% 9.61/3.47  #SimpNegUnit  : 14
% 9.61/3.47  #BackRed      : 611
% 9.61/3.47  
% 9.61/3.47  #Partial instantiations: 0
% 9.61/3.47  #Strategies tried      : 1
% 9.61/3.47  
% 9.61/3.47  Timing (in seconds)
% 9.61/3.47  ----------------------
% 9.61/3.47  Preprocessing        : 0.36
% 9.61/3.47  Parsing              : 0.19
% 9.61/3.47  CNF conversion       : 0.02
% 9.61/3.47  Main loop            : 2.22
% 9.61/3.47  Inferencing          : 0.72
% 9.61/3.47  Reduction            : 0.82
% 9.61/3.47  Demodulation         : 0.60
% 9.61/3.47  BG Simplification    : 0.07
% 9.61/3.47  Subsumption          : 0.44
% 9.61/3.47  Abstraction          : 0.10
% 9.61/3.47  MUC search           : 0.00
% 9.61/3.47  Cooper               : 0.00
% 9.61/3.47  Total                : 2.68
% 9.61/3.47  Index Insertion      : 0.00
% 9.61/3.47  Index Deletion       : 0.00
% 9.61/3.47  Index Matching       : 0.00
% 9.61/3.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
