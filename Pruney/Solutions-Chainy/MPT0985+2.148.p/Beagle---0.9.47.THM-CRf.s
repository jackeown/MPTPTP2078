%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:50 EST 2020

% Result     : Theorem 4.78s
% Output     : CNFRefutation 5.05s
% Verified   : 
% Statistics : Number of formulae       :  181 (3418 expanded)
%              Number of leaves         :   39 (1183 expanded)
%              Depth                    :   25
%              Number of atoms          :  353 (10513 expanded)
%              Number of equality atoms :   79 (1444 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

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

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_40,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_151,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ( v2_funct_1(C)
            & k2_relset_1(A,B,C) = B )
         => ( v1_funct_1(k2_funct_1(C))
            & v1_funct_2(k2_funct_1(C),B,A)
            & m1_subset_1(k2_funct_1(C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_106,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_48,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_102,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_78,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v2_funct_1(B)
       => r1_tarski(k10_relat_1(B,k9_relat_1(B,A)),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_funct_1)).

tff(f_62,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_96,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_122,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_86,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v2_funct_1(B)
       => k9_relat_1(B,A) = k10_relat_1(k2_funct_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t154_funct_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(A,k2_relat_1(B))
       => k9_relat_1(B,k10_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).

tff(f_134,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(k2_relat_1(B),A)
       => ( v1_funct_1(B)
          & v1_funct_2(B,k1_relat_1(B),A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).

tff(f_38,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(c_8,plain,(
    ! [A_6,B_7] : v1_relat_1(k2_zfmisc_1(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_56,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_68,plain,(
    ! [B_38,A_39] :
      ( v1_relat_1(B_38)
      | ~ m1_subset_1(B_38,k1_zfmisc_1(A_39))
      | ~ v1_relat_1(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_71,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_56,c_68])).

tff(c_74,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_71])).

tff(c_60,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_54,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_52,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_1991,plain,(
    ! [A_143,B_144,C_145] :
      ( k2_relset_1(A_143,B_144,C_145) = k2_relat_1(C_145)
      | ~ m1_subset_1(C_145,k1_zfmisc_1(k2_zfmisc_1(A_143,B_144))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_1997,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_1991])).

tff(c_2000,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_1997])).

tff(c_12,plain,(
    ! [A_10] :
      ( k10_relat_1(A_10,k2_relat_1(A_10)) = k1_relat_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_2014,plain,
    ( k10_relat_1('#skF_3','#skF_2') = k1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2000,c_12])).

tff(c_2024,plain,(
    k10_relat_1('#skF_3','#skF_2') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_2014])).

tff(c_94,plain,(
    ! [C_41,A_42,B_43] :
      ( v4_relat_1(C_41,A_42)
      | ~ m1_subset_1(C_41,k1_zfmisc_1(k2_zfmisc_1(A_42,B_43))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_98,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_56,c_94])).

tff(c_1891,plain,(
    ! [B_132,A_133] :
      ( k7_relat_1(B_132,A_133) = B_132
      | ~ v4_relat_1(B_132,A_133)
      | ~ v1_relat_1(B_132) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_1894,plain,
    ( k7_relat_1('#skF_3','#skF_1') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_98,c_1891])).

tff(c_1897,plain,(
    k7_relat_1('#skF_3','#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_1894])).

tff(c_1913,plain,(
    ! [B_136,A_137] :
      ( k2_relat_1(k7_relat_1(B_136,A_137)) = k9_relat_1(B_136,A_137)
      | ~ v1_relat_1(B_136) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_1931,plain,
    ( k9_relat_1('#skF_3','#skF_1') = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1897,c_1913])).

tff(c_1937,plain,(
    k9_relat_1('#skF_3','#skF_1') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_1931])).

tff(c_2001,plain,(
    k9_relat_1('#skF_3','#skF_1') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2000,c_1937])).

tff(c_2218,plain,(
    ! [B_155,A_156] :
      ( r1_tarski(k10_relat_1(B_155,k9_relat_1(B_155,A_156)),A_156)
      | ~ v2_funct_1(B_155)
      | ~ v1_funct_1(B_155)
      | ~ v1_relat_1(B_155) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_2228,plain,
    ( r1_tarski(k10_relat_1('#skF_3','#skF_2'),'#skF_1')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2001,c_2218])).

tff(c_2235,plain,(
    r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_60,c_54,c_2024,c_2228])).

tff(c_186,plain,(
    ! [A_58,B_59,C_60] :
      ( k2_relset_1(A_58,B_59,C_60) = k2_relat_1(C_60)
      | ~ m1_subset_1(C_60,k1_zfmisc_1(k2_zfmisc_1(A_58,B_59))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_189,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_186])).

tff(c_191,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_189])).

tff(c_205,plain,
    ( k10_relat_1('#skF_3','#skF_2') = k1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_191,c_12])).

tff(c_215,plain,(
    k10_relat_1('#skF_3','#skF_2') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_205])).

tff(c_105,plain,(
    ! [B_47,A_48] :
      ( k7_relat_1(B_47,A_48) = B_47
      | ~ v4_relat_1(B_47,A_48)
      | ~ v1_relat_1(B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_108,plain,
    ( k7_relat_1('#skF_3','#skF_1') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_98,c_105])).

tff(c_111,plain,(
    k7_relat_1('#skF_3','#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_108])).

tff(c_122,plain,(
    ! [B_53,A_54] :
      ( k2_relat_1(k7_relat_1(B_53,A_54)) = k9_relat_1(B_53,A_54)
      | ~ v1_relat_1(B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_140,plain,
    ( k9_relat_1('#skF_3','#skF_1') = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_111,c_122])).

tff(c_144,plain,(
    k9_relat_1('#skF_3','#skF_1') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_140])).

tff(c_192,plain,(
    k9_relat_1('#skF_3','#skF_1') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_191,c_144])).

tff(c_319,plain,(
    ! [B_65,A_66] :
      ( r1_tarski(k10_relat_1(B_65,k9_relat_1(B_65,A_66)),A_66)
      | ~ v2_funct_1(B_65)
      | ~ v1_funct_1(B_65)
      | ~ v1_relat_1(B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_325,plain,
    ( r1_tarski(k10_relat_1('#skF_3','#skF_2'),'#skF_1')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_192,c_319])).

tff(c_329,plain,(
    r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_60,c_54,c_215,c_325])).

tff(c_18,plain,(
    ! [A_13] :
      ( v1_relat_1(k2_funct_1(A_13))
      | ~ v1_funct_1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_16,plain,(
    ! [A_13] :
      ( v1_funct_1(k2_funct_1(A_13))
      | ~ v1_funct_1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_50,plain,
    ( ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_75,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_78,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_16,c_75])).

tff(c_82,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_60,c_78])).

tff(c_84,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_28,plain,(
    ! [A_20] :
      ( k1_relat_1(k2_funct_1(A_20)) = k2_relat_1(A_20)
      | ~ v2_funct_1(A_20)
      | ~ v1_funct_1(A_20)
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_225,plain,(
    ! [A_61] :
      ( m1_subset_1(A_61,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_61),k2_relat_1(A_61))))
      | ~ v1_funct_1(A_61)
      | ~ v1_relat_1(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_32,plain,(
    ! [C_23,A_21,B_22] :
      ( v4_relat_1(C_23,A_21)
      | ~ m1_subset_1(C_23,k1_zfmisc_1(k2_zfmisc_1(A_21,B_22))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_311,plain,(
    ! [A_64] :
      ( v4_relat_1(A_64,k1_relat_1(A_64))
      | ~ v1_funct_1(A_64)
      | ~ v1_relat_1(A_64) ) ),
    inference(resolution,[status(thm)],[c_225,c_32])).

tff(c_827,plain,(
    ! [A_108] :
      ( v4_relat_1(k2_funct_1(A_108),k2_relat_1(A_108))
      | ~ v1_funct_1(k2_funct_1(A_108))
      | ~ v1_relat_1(k2_funct_1(A_108))
      | ~ v2_funct_1(A_108)
      | ~ v1_funct_1(A_108)
      | ~ v1_relat_1(A_108) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_311])).

tff(c_833,plain,
    ( v4_relat_1(k2_funct_1('#skF_3'),'#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_191,c_827])).

tff(c_842,plain,
    ( v4_relat_1(k2_funct_1('#skF_3'),'#skF_2')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_60,c_54,c_84,c_833])).

tff(c_890,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_842])).

tff(c_893,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_18,c_890])).

tff(c_897,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_60,c_893])).

tff(c_899,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_842])).

tff(c_898,plain,(
    v4_relat_1(k2_funct_1('#skF_3'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_842])).

tff(c_14,plain,(
    ! [B_12,A_11] :
      ( k7_relat_1(B_12,A_11) = B_12
      | ~ v4_relat_1(B_12,A_11)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_921,plain,
    ( k7_relat_1(k2_funct_1('#skF_3'),'#skF_2') = k2_funct_1('#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_898,c_14])).

tff(c_924,plain,(
    k7_relat_1(k2_funct_1('#skF_3'),'#skF_2') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_899,c_921])).

tff(c_10,plain,(
    ! [B_9,A_8] :
      ( k2_relat_1(k7_relat_1(B_9,A_8)) = k9_relat_1(B_9,A_8)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_937,plain,
    ( k9_relat_1(k2_funct_1('#skF_3'),'#skF_2') = k2_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_924,c_10])).

tff(c_947,plain,(
    k9_relat_1(k2_funct_1('#skF_3'),'#skF_2') = k2_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_899,c_937])).

tff(c_26,plain,(
    ! [A_20] :
      ( k2_relat_1(k2_funct_1(A_20)) = k1_relat_1(A_20)
      | ~ v2_funct_1(A_20)
      | ~ v1_funct_1(A_20)
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_240,plain,
    ( m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2')))
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_191,c_225])).

tff(c_257,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_60,c_240])).

tff(c_284,plain,(
    v4_relat_1('#skF_3',k1_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_257,c_32])).

tff(c_290,plain,
    ( k7_relat_1('#skF_3',k1_relat_1('#skF_3')) = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_284,c_14])).

tff(c_293,plain,(
    k7_relat_1('#skF_3',k1_relat_1('#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_290])).

tff(c_297,plain,
    ( k9_relat_1('#skF_3',k1_relat_1('#skF_3')) = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_293,c_10])).

tff(c_301,plain,(
    k9_relat_1('#skF_3',k1_relat_1('#skF_3')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_191,c_297])).

tff(c_134,plain,(
    ! [B_53,A_54] :
      ( k10_relat_1(k7_relat_1(B_53,A_54),k9_relat_1(B_53,A_54)) = k1_relat_1(k7_relat_1(B_53,A_54))
      | ~ v1_relat_1(k7_relat_1(B_53,A_54))
      | ~ v1_relat_1(B_53) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_122,c_12])).

tff(c_952,plain,
    ( k10_relat_1(k7_relat_1(k2_funct_1('#skF_3'),'#skF_2'),k2_relat_1(k2_funct_1('#skF_3'))) = k1_relat_1(k7_relat_1(k2_funct_1('#skF_3'),'#skF_2'))
    | ~ v1_relat_1(k7_relat_1(k2_funct_1('#skF_3'),'#skF_2'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_947,c_134])).

tff(c_959,plain,(
    k10_relat_1(k2_funct_1('#skF_3'),k2_relat_1(k2_funct_1('#skF_3'))) = k1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_899,c_899,c_924,c_924,c_924,c_952])).

tff(c_24,plain,(
    ! [B_19,A_18] :
      ( k10_relat_1(k2_funct_1(B_19),A_18) = k9_relat_1(B_19,A_18)
      | ~ v2_funct_1(B_19)
      | ~ v1_funct_1(B_19)
      | ~ v1_relat_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_969,plain,
    ( k9_relat_1('#skF_3',k2_relat_1(k2_funct_1('#skF_3'))) = k1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_959,c_24])).

tff(c_987,plain,(
    k9_relat_1('#skF_3',k2_relat_1(k2_funct_1('#skF_3'))) = k1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_60,c_54,c_969])).

tff(c_1015,plain,
    ( k9_relat_1('#skF_3',k1_relat_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_987])).

tff(c_1029,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_60,c_54,c_301,c_1015])).

tff(c_1046,plain,(
    k10_relat_1(k2_funct_1('#skF_3'),k2_relat_1(k2_funct_1('#skF_3'))) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1029,c_959])).

tff(c_1176,plain,
    ( k10_relat_1(k2_funct_1('#skF_3'),k1_relat_1('#skF_3')) = '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_1046])).

tff(c_1191,plain,(
    k10_relat_1(k2_funct_1('#skF_3'),k1_relat_1('#skF_3')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_60,c_54,c_1176])).

tff(c_1045,plain,(
    k9_relat_1('#skF_3',k2_relat_1(k2_funct_1('#skF_3'))) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1029,c_987])).

tff(c_22,plain,(
    ! [B_17,A_16] :
      ( r1_tarski(k10_relat_1(B_17,k9_relat_1(B_17,A_16)),A_16)
      | ~ v2_funct_1(B_17)
      | ~ v1_funct_1(B_17)
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1125,plain,
    ( r1_tarski(k10_relat_1('#skF_3','#skF_2'),k2_relat_1(k2_funct_1('#skF_3')))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1045,c_22])).

tff(c_1139,plain,(
    r1_tarski(k1_relat_1('#skF_3'),k2_relat_1(k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_60,c_54,c_215,c_1125])).

tff(c_20,plain,(
    ! [B_15,A_14] :
      ( k9_relat_1(B_15,k10_relat_1(B_15,A_14)) = A_14
      | ~ r1_tarski(A_14,k2_relat_1(B_15))
      | ~ v1_funct_1(B_15)
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_1146,plain,
    ( k9_relat_1(k2_funct_1('#skF_3'),k10_relat_1(k2_funct_1('#skF_3'),k1_relat_1('#skF_3'))) = k1_relat_1('#skF_3')
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_1139,c_20])).

tff(c_1152,plain,(
    k9_relat_1(k2_funct_1('#skF_3'),k10_relat_1(k2_funct_1('#skF_3'),k1_relat_1('#skF_3'))) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_899,c_84,c_1146])).

tff(c_1606,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_947,c_1191,c_1152])).

tff(c_44,plain,(
    ! [B_33,A_32] :
      ( m1_subset_1(B_33,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_33),A_32)))
      | ~ r1_tarski(k2_relat_1(B_33),A_32)
      | ~ v1_funct_1(B_33)
      | ~ v1_relat_1(B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_1059,plain,(
    ! [A_32] :
      ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2',A_32)))
      | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),A_32)
      | ~ v1_funct_1(k2_funct_1('#skF_3'))
      | ~ v1_relat_1(k2_funct_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1029,c_44])).

tff(c_1096,plain,(
    ! [A_32] :
      ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2',A_32)))
      | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),A_32) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_899,c_84,c_1059])).

tff(c_1849,plain,(
    ! [A_131] :
      ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2',A_131)))
      | ~ r1_tarski(k1_relat_1('#skF_3'),A_131) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1606,c_1096])).

tff(c_83,plain,
    ( ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_104,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_83])).

tff(c_1857,plain,(
    ~ r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_1849,c_104])).

tff(c_1874,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_329,c_1857])).

tff(c_1876,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_83])).

tff(c_2,plain,(
    ! [B_3,A_1] :
      ( v1_relat_1(B_3)
      | ~ m1_subset_1(B_3,k1_zfmisc_1(A_1))
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1885,plain,
    ( v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_1876,c_2])).

tff(c_1890,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_1885])).

tff(c_1887,plain,(
    v4_relat_1(k2_funct_1('#skF_3'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_1876,c_32])).

tff(c_1900,plain,
    ( k7_relat_1(k2_funct_1('#skF_3'),'#skF_2') = k2_funct_1('#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_1887,c_14])).

tff(c_1903,plain,(
    k7_relat_1(k2_funct_1('#skF_3'),'#skF_2') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1890,c_1900])).

tff(c_1928,plain,
    ( k9_relat_1(k2_funct_1('#skF_3'),'#skF_2') = k2_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1903,c_1913])).

tff(c_1935,plain,(
    k9_relat_1(k2_funct_1('#skF_3'),'#skF_2') = k2_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1890,c_1928])).

tff(c_2035,plain,(
    ! [A_147] :
      ( m1_subset_1(A_147,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_147),k2_relat_1(A_147))))
      | ~ v1_funct_1(A_147)
      | ~ v1_relat_1(A_147) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_2050,plain,
    ( m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2')))
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2000,c_2035])).

tff(c_2067,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_60,c_2050])).

tff(c_2093,plain,(
    v4_relat_1('#skF_3',k1_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_2067,c_32])).

tff(c_2103,plain,
    ( k7_relat_1('#skF_3',k1_relat_1('#skF_3')) = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2093,c_14])).

tff(c_2106,plain,(
    k7_relat_1('#skF_3',k1_relat_1('#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_2103])).

tff(c_2110,plain,
    ( k9_relat_1('#skF_3',k1_relat_1('#skF_3')) = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2106,c_10])).

tff(c_2114,plain,(
    k9_relat_1('#skF_3',k1_relat_1('#skF_3')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_2000,c_2110])).

tff(c_30,plain,(
    ! [C_23,B_22,A_21] :
      ( v5_relat_1(C_23,B_22)
      | ~ m1_subset_1(C_23,k1_zfmisc_1(k2_zfmisc_1(A_21,B_22))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_2061,plain,(
    ! [A_147] :
      ( v5_relat_1(A_147,k2_relat_1(A_147))
      | ~ v1_funct_1(A_147)
      | ~ v1_relat_1(A_147) ) ),
    inference(resolution,[status(thm)],[c_2035,c_30])).

tff(c_1946,plain,(
    ! [B_138,A_139] :
      ( r1_tarski(k2_relat_1(B_138),A_139)
      | ~ v5_relat_1(B_138,A_139)
      | ~ v1_relat_1(B_138) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2606,plain,(
    ! [B_184,A_185,A_186] :
      ( r1_tarski(k9_relat_1(B_184,A_185),A_186)
      | ~ v5_relat_1(k7_relat_1(B_184,A_185),A_186)
      | ~ v1_relat_1(k7_relat_1(B_184,A_185))
      | ~ v1_relat_1(B_184) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_1946])).

tff(c_2619,plain,(
    ! [A_186] :
      ( r1_tarski(k9_relat_1(k2_funct_1('#skF_3'),'#skF_2'),A_186)
      | ~ v5_relat_1(k2_funct_1('#skF_3'),A_186)
      | ~ v1_relat_1(k7_relat_1(k2_funct_1('#skF_3'),'#skF_2'))
      | ~ v1_relat_1(k2_funct_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1903,c_2606])).

tff(c_2630,plain,(
    ! [A_187] :
      ( r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),A_187)
      | ~ v5_relat_1(k2_funct_1('#skF_3'),A_187) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1890,c_1890,c_1903,c_1935,c_2619])).

tff(c_2647,plain,(
    ! [A_187] :
      ( r1_tarski(k1_relat_1('#skF_3'),A_187)
      | ~ v5_relat_1(k2_funct_1('#skF_3'),A_187)
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_2630])).

tff(c_2659,plain,(
    ! [A_188] :
      ( r1_tarski(k1_relat_1('#skF_3'),A_188)
      | ~ v5_relat_1(k2_funct_1('#skF_3'),A_188) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_60,c_54,c_2647])).

tff(c_2666,plain,
    ( r1_tarski(k1_relat_1('#skF_3'),k2_relat_1(k2_funct_1('#skF_3')))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_2061,c_2659])).

tff(c_2673,plain,(
    r1_tarski(k1_relat_1('#skF_3'),k2_relat_1(k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1890,c_84,c_2666])).

tff(c_2680,plain,
    ( k9_relat_1(k2_funct_1('#skF_3'),k10_relat_1(k2_funct_1('#skF_3'),k1_relat_1('#skF_3'))) = k1_relat_1('#skF_3')
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_2673,c_20])).

tff(c_2688,plain,(
    k9_relat_1(k2_funct_1('#skF_3'),k10_relat_1(k2_funct_1('#skF_3'),k1_relat_1('#skF_3'))) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1890,c_84,c_2680])).

tff(c_2739,plain,
    ( k9_relat_1(k2_funct_1('#skF_3'),k9_relat_1('#skF_3',k1_relat_1('#skF_3'))) = k1_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_2688])).

tff(c_2745,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_60,c_54,c_1935,c_2114,c_2739])).

tff(c_2787,plain,
    ( k10_relat_1(k2_funct_1('#skF_3'),k1_relat_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2745,c_12])).

tff(c_2813,plain,(
    k10_relat_1(k2_funct_1('#skF_3'),k1_relat_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1890,c_2787])).

tff(c_2868,plain,
    ( k9_relat_1('#skF_3',k1_relat_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2813,c_24])).

tff(c_2875,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_60,c_54,c_2114,c_2868])).

tff(c_46,plain,(
    ! [B_33,A_32] :
      ( v1_funct_2(B_33,k1_relat_1(B_33),A_32)
      | ~ r1_tarski(k2_relat_1(B_33),A_32)
      | ~ v1_funct_1(B_33)
      | ~ v1_relat_1(B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_2914,plain,(
    ! [A_32] :
      ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_2',A_32)
      | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),A_32)
      | ~ v1_funct_1(k2_funct_1('#skF_3'))
      | ~ v1_relat_1(k2_funct_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2875,c_46])).

tff(c_3040,plain,(
    ! [A_195] :
      ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_2',A_195)
      | ~ r1_tarski(k1_relat_1('#skF_3'),A_195) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1890,c_84,c_2745,c_2914])).

tff(c_1875,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_83])).

tff(c_3043,plain,(
    ~ r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_3040,c_1875])).

tff(c_3047,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2235,c_3043])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:56:41 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.78/1.97  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.05/1.99  
% 5.05/1.99  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.05/1.99  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 5.05/1.99  
% 5.05/1.99  %Foreground sorts:
% 5.05/1.99  
% 5.05/1.99  
% 5.05/1.99  %Background operators:
% 5.05/1.99  
% 5.05/1.99  
% 5.05/1.99  %Foreground operators:
% 5.05/1.99  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 5.05/1.99  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.05/1.99  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 5.05/1.99  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 5.05/1.99  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.05/1.99  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 5.05/1.99  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.05/1.99  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.05/1.99  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.05/1.99  tff('#skF_2', type, '#skF_2': $i).
% 5.05/1.99  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 5.05/1.99  tff('#skF_3', type, '#skF_3': $i).
% 5.05/1.99  tff('#skF_1', type, '#skF_1': $i).
% 5.05/1.99  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 5.05/1.99  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.05/1.99  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.05/1.99  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 5.05/1.99  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.05/1.99  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.05/1.99  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.05/1.99  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 5.05/1.99  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.05/1.99  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.05/1.99  
% 5.05/2.02  tff(f_40, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 5.05/2.02  tff(f_151, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_funct_2)).
% 5.05/2.02  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 5.05/2.02  tff(f_106, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 5.05/2.02  tff(f_48, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_relat_1)).
% 5.05/2.02  tff(f_102, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 5.05/2.02  tff(f_54, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 5.05/2.02  tff(f_44, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 5.05/2.02  tff(f_78, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v2_funct_1(B) => r1_tarski(k10_relat_1(B, k9_relat_1(B, A)), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_funct_1)).
% 5.05/2.02  tff(f_62, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 5.05/2.02  tff(f_96, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 5.05/2.02  tff(f_122, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_funct_2)).
% 5.05/2.02  tff(f_86, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v2_funct_1(B) => (k9_relat_1(B, A) = k10_relat_1(k2_funct_1(B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t154_funct_1)).
% 5.05/2.02  tff(f_70, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(A, k2_relat_1(B)) => (k9_relat_1(B, k10_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t147_funct_1)).
% 5.05/2.02  tff(f_134, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_funct_2)).
% 5.05/2.02  tff(f_38, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 5.05/2.02  tff(c_8, plain, (![A_6, B_7]: (v1_relat_1(k2_zfmisc_1(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 5.05/2.02  tff(c_56, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_151])).
% 5.05/2.02  tff(c_68, plain, (![B_38, A_39]: (v1_relat_1(B_38) | ~m1_subset_1(B_38, k1_zfmisc_1(A_39)) | ~v1_relat_1(A_39))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.05/2.02  tff(c_71, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_56, c_68])).
% 5.05/2.02  tff(c_74, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_71])).
% 5.05/2.02  tff(c_60, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_151])).
% 5.05/2.02  tff(c_54, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_151])).
% 5.05/2.02  tff(c_52, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_151])).
% 5.05/2.02  tff(c_1991, plain, (![A_143, B_144, C_145]: (k2_relset_1(A_143, B_144, C_145)=k2_relat_1(C_145) | ~m1_subset_1(C_145, k1_zfmisc_1(k2_zfmisc_1(A_143, B_144))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 5.05/2.02  tff(c_1997, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_56, c_1991])).
% 5.05/2.02  tff(c_2000, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_1997])).
% 5.05/2.02  tff(c_12, plain, (![A_10]: (k10_relat_1(A_10, k2_relat_1(A_10))=k1_relat_1(A_10) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_48])).
% 5.05/2.02  tff(c_2014, plain, (k10_relat_1('#skF_3', '#skF_2')=k1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2000, c_12])).
% 5.05/2.02  tff(c_2024, plain, (k10_relat_1('#skF_3', '#skF_2')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_2014])).
% 5.05/2.02  tff(c_94, plain, (![C_41, A_42, B_43]: (v4_relat_1(C_41, A_42) | ~m1_subset_1(C_41, k1_zfmisc_1(k2_zfmisc_1(A_42, B_43))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 5.05/2.02  tff(c_98, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_56, c_94])).
% 5.05/2.02  tff(c_1891, plain, (![B_132, A_133]: (k7_relat_1(B_132, A_133)=B_132 | ~v4_relat_1(B_132, A_133) | ~v1_relat_1(B_132))), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.05/2.02  tff(c_1894, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_98, c_1891])).
% 5.05/2.02  tff(c_1897, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_1894])).
% 5.05/2.02  tff(c_1913, plain, (![B_136, A_137]: (k2_relat_1(k7_relat_1(B_136, A_137))=k9_relat_1(B_136, A_137) | ~v1_relat_1(B_136))), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.05/2.02  tff(c_1931, plain, (k9_relat_1('#skF_3', '#skF_1')=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1897, c_1913])).
% 5.05/2.02  tff(c_1937, plain, (k9_relat_1('#skF_3', '#skF_1')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_1931])).
% 5.05/2.02  tff(c_2001, plain, (k9_relat_1('#skF_3', '#skF_1')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2000, c_1937])).
% 5.05/2.02  tff(c_2218, plain, (![B_155, A_156]: (r1_tarski(k10_relat_1(B_155, k9_relat_1(B_155, A_156)), A_156) | ~v2_funct_1(B_155) | ~v1_funct_1(B_155) | ~v1_relat_1(B_155))), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.05/2.02  tff(c_2228, plain, (r1_tarski(k10_relat_1('#skF_3', '#skF_2'), '#skF_1') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2001, c_2218])).
% 5.05/2.02  tff(c_2235, plain, (r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_60, c_54, c_2024, c_2228])).
% 5.05/2.02  tff(c_186, plain, (![A_58, B_59, C_60]: (k2_relset_1(A_58, B_59, C_60)=k2_relat_1(C_60) | ~m1_subset_1(C_60, k1_zfmisc_1(k2_zfmisc_1(A_58, B_59))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 5.05/2.02  tff(c_189, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_56, c_186])).
% 5.05/2.02  tff(c_191, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_189])).
% 5.05/2.02  tff(c_205, plain, (k10_relat_1('#skF_3', '#skF_2')=k1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_191, c_12])).
% 5.05/2.02  tff(c_215, plain, (k10_relat_1('#skF_3', '#skF_2')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_205])).
% 5.05/2.02  tff(c_105, plain, (![B_47, A_48]: (k7_relat_1(B_47, A_48)=B_47 | ~v4_relat_1(B_47, A_48) | ~v1_relat_1(B_47))), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.05/2.02  tff(c_108, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_98, c_105])).
% 5.05/2.02  tff(c_111, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_108])).
% 5.05/2.02  tff(c_122, plain, (![B_53, A_54]: (k2_relat_1(k7_relat_1(B_53, A_54))=k9_relat_1(B_53, A_54) | ~v1_relat_1(B_53))), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.05/2.02  tff(c_140, plain, (k9_relat_1('#skF_3', '#skF_1')=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_111, c_122])).
% 5.05/2.02  tff(c_144, plain, (k9_relat_1('#skF_3', '#skF_1')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_140])).
% 5.05/2.02  tff(c_192, plain, (k9_relat_1('#skF_3', '#skF_1')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_191, c_144])).
% 5.05/2.02  tff(c_319, plain, (![B_65, A_66]: (r1_tarski(k10_relat_1(B_65, k9_relat_1(B_65, A_66)), A_66) | ~v2_funct_1(B_65) | ~v1_funct_1(B_65) | ~v1_relat_1(B_65))), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.05/2.02  tff(c_325, plain, (r1_tarski(k10_relat_1('#skF_3', '#skF_2'), '#skF_1') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_192, c_319])).
% 5.05/2.02  tff(c_329, plain, (r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_60, c_54, c_215, c_325])).
% 5.05/2.02  tff(c_18, plain, (![A_13]: (v1_relat_1(k2_funct_1(A_13)) | ~v1_funct_1(A_13) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_62])).
% 5.05/2.02  tff(c_16, plain, (![A_13]: (v1_funct_1(k2_funct_1(A_13)) | ~v1_funct_1(A_13) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_62])).
% 5.05/2.02  tff(c_50, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_151])).
% 5.05/2.02  tff(c_75, plain, (~v1_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_50])).
% 5.05/2.02  tff(c_78, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_16, c_75])).
% 5.05/2.02  tff(c_82, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_60, c_78])).
% 5.05/2.02  tff(c_84, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_50])).
% 5.05/2.02  tff(c_28, plain, (![A_20]: (k1_relat_1(k2_funct_1(A_20))=k2_relat_1(A_20) | ~v2_funct_1(A_20) | ~v1_funct_1(A_20) | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_96])).
% 5.05/2.02  tff(c_225, plain, (![A_61]: (m1_subset_1(A_61, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_61), k2_relat_1(A_61)))) | ~v1_funct_1(A_61) | ~v1_relat_1(A_61))), inference(cnfTransformation, [status(thm)], [f_122])).
% 5.05/2.02  tff(c_32, plain, (![C_23, A_21, B_22]: (v4_relat_1(C_23, A_21) | ~m1_subset_1(C_23, k1_zfmisc_1(k2_zfmisc_1(A_21, B_22))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 5.05/2.02  tff(c_311, plain, (![A_64]: (v4_relat_1(A_64, k1_relat_1(A_64)) | ~v1_funct_1(A_64) | ~v1_relat_1(A_64))), inference(resolution, [status(thm)], [c_225, c_32])).
% 5.05/2.02  tff(c_827, plain, (![A_108]: (v4_relat_1(k2_funct_1(A_108), k2_relat_1(A_108)) | ~v1_funct_1(k2_funct_1(A_108)) | ~v1_relat_1(k2_funct_1(A_108)) | ~v2_funct_1(A_108) | ~v1_funct_1(A_108) | ~v1_relat_1(A_108))), inference(superposition, [status(thm), theory('equality')], [c_28, c_311])).
% 5.05/2.02  tff(c_833, plain, (v4_relat_1(k2_funct_1('#skF_3'), '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_191, c_827])).
% 5.05/2.02  tff(c_842, plain, (v4_relat_1(k2_funct_1('#skF_3'), '#skF_2') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_60, c_54, c_84, c_833])).
% 5.05/2.02  tff(c_890, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_842])).
% 5.05/2.02  tff(c_893, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_18, c_890])).
% 5.05/2.02  tff(c_897, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_60, c_893])).
% 5.05/2.02  tff(c_899, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_842])).
% 5.05/2.02  tff(c_898, plain, (v4_relat_1(k2_funct_1('#skF_3'), '#skF_2')), inference(splitRight, [status(thm)], [c_842])).
% 5.05/2.02  tff(c_14, plain, (![B_12, A_11]: (k7_relat_1(B_12, A_11)=B_12 | ~v4_relat_1(B_12, A_11) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.05/2.02  tff(c_921, plain, (k7_relat_1(k2_funct_1('#skF_3'), '#skF_2')=k2_funct_1('#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_898, c_14])).
% 5.05/2.02  tff(c_924, plain, (k7_relat_1(k2_funct_1('#skF_3'), '#skF_2')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_899, c_921])).
% 5.05/2.02  tff(c_10, plain, (![B_9, A_8]: (k2_relat_1(k7_relat_1(B_9, A_8))=k9_relat_1(B_9, A_8) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.05/2.02  tff(c_937, plain, (k9_relat_1(k2_funct_1('#skF_3'), '#skF_2')=k2_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_924, c_10])).
% 5.05/2.02  tff(c_947, plain, (k9_relat_1(k2_funct_1('#skF_3'), '#skF_2')=k2_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_899, c_937])).
% 5.05/2.02  tff(c_26, plain, (![A_20]: (k2_relat_1(k2_funct_1(A_20))=k1_relat_1(A_20) | ~v2_funct_1(A_20) | ~v1_funct_1(A_20) | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_96])).
% 5.05/2.02  tff(c_240, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2'))) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_191, c_225])).
% 5.05/2.02  tff(c_257, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_60, c_240])).
% 5.05/2.02  tff(c_284, plain, (v4_relat_1('#skF_3', k1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_257, c_32])).
% 5.05/2.02  tff(c_290, plain, (k7_relat_1('#skF_3', k1_relat_1('#skF_3'))='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_284, c_14])).
% 5.05/2.02  tff(c_293, plain, (k7_relat_1('#skF_3', k1_relat_1('#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_290])).
% 5.05/2.02  tff(c_297, plain, (k9_relat_1('#skF_3', k1_relat_1('#skF_3'))=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_293, c_10])).
% 5.05/2.02  tff(c_301, plain, (k9_relat_1('#skF_3', k1_relat_1('#skF_3'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_191, c_297])).
% 5.05/2.02  tff(c_134, plain, (![B_53, A_54]: (k10_relat_1(k7_relat_1(B_53, A_54), k9_relat_1(B_53, A_54))=k1_relat_1(k7_relat_1(B_53, A_54)) | ~v1_relat_1(k7_relat_1(B_53, A_54)) | ~v1_relat_1(B_53))), inference(superposition, [status(thm), theory('equality')], [c_122, c_12])).
% 5.05/2.02  tff(c_952, plain, (k10_relat_1(k7_relat_1(k2_funct_1('#skF_3'), '#skF_2'), k2_relat_1(k2_funct_1('#skF_3')))=k1_relat_1(k7_relat_1(k2_funct_1('#skF_3'), '#skF_2')) | ~v1_relat_1(k7_relat_1(k2_funct_1('#skF_3'), '#skF_2')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_947, c_134])).
% 5.05/2.02  tff(c_959, plain, (k10_relat_1(k2_funct_1('#skF_3'), k2_relat_1(k2_funct_1('#skF_3')))=k1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_899, c_899, c_924, c_924, c_924, c_952])).
% 5.05/2.02  tff(c_24, plain, (![B_19, A_18]: (k10_relat_1(k2_funct_1(B_19), A_18)=k9_relat_1(B_19, A_18) | ~v2_funct_1(B_19) | ~v1_funct_1(B_19) | ~v1_relat_1(B_19))), inference(cnfTransformation, [status(thm)], [f_86])).
% 5.05/2.02  tff(c_969, plain, (k9_relat_1('#skF_3', k2_relat_1(k2_funct_1('#skF_3')))=k1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_959, c_24])).
% 5.05/2.02  tff(c_987, plain, (k9_relat_1('#skF_3', k2_relat_1(k2_funct_1('#skF_3')))=k1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_60, c_54, c_969])).
% 5.05/2.02  tff(c_1015, plain, (k9_relat_1('#skF_3', k1_relat_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_26, c_987])).
% 5.05/2.02  tff(c_1029, plain, (k1_relat_1(k2_funct_1('#skF_3'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_60, c_54, c_301, c_1015])).
% 5.05/2.02  tff(c_1046, plain, (k10_relat_1(k2_funct_1('#skF_3'), k2_relat_1(k2_funct_1('#skF_3')))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1029, c_959])).
% 5.05/2.02  tff(c_1176, plain, (k10_relat_1(k2_funct_1('#skF_3'), k1_relat_1('#skF_3'))='#skF_2' | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_26, c_1046])).
% 5.05/2.02  tff(c_1191, plain, (k10_relat_1(k2_funct_1('#skF_3'), k1_relat_1('#skF_3'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_60, c_54, c_1176])).
% 5.05/2.02  tff(c_1045, plain, (k9_relat_1('#skF_3', k2_relat_1(k2_funct_1('#skF_3')))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1029, c_987])).
% 5.05/2.02  tff(c_22, plain, (![B_17, A_16]: (r1_tarski(k10_relat_1(B_17, k9_relat_1(B_17, A_16)), A_16) | ~v2_funct_1(B_17) | ~v1_funct_1(B_17) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.05/2.02  tff(c_1125, plain, (r1_tarski(k10_relat_1('#skF_3', '#skF_2'), k2_relat_1(k2_funct_1('#skF_3'))) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1045, c_22])).
% 5.05/2.02  tff(c_1139, plain, (r1_tarski(k1_relat_1('#skF_3'), k2_relat_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_60, c_54, c_215, c_1125])).
% 5.05/2.02  tff(c_20, plain, (![B_15, A_14]: (k9_relat_1(B_15, k10_relat_1(B_15, A_14))=A_14 | ~r1_tarski(A_14, k2_relat_1(B_15)) | ~v1_funct_1(B_15) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_70])).
% 5.05/2.02  tff(c_1146, plain, (k9_relat_1(k2_funct_1('#skF_3'), k10_relat_1(k2_funct_1('#skF_3'), k1_relat_1('#skF_3')))=k1_relat_1('#skF_3') | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_1139, c_20])).
% 5.05/2.02  tff(c_1152, plain, (k9_relat_1(k2_funct_1('#skF_3'), k10_relat_1(k2_funct_1('#skF_3'), k1_relat_1('#skF_3')))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_899, c_84, c_1146])).
% 5.05/2.02  tff(c_1606, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_947, c_1191, c_1152])).
% 5.05/2.02  tff(c_44, plain, (![B_33, A_32]: (m1_subset_1(B_33, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_33), A_32))) | ~r1_tarski(k2_relat_1(B_33), A_32) | ~v1_funct_1(B_33) | ~v1_relat_1(B_33))), inference(cnfTransformation, [status(thm)], [f_134])).
% 5.05/2.02  tff(c_1059, plain, (![A_32]: (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', A_32))) | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), A_32) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_1029, c_44])).
% 5.05/2.02  tff(c_1096, plain, (![A_32]: (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', A_32))) | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), A_32))), inference(demodulation, [status(thm), theory('equality')], [c_899, c_84, c_1059])).
% 5.05/2.02  tff(c_1849, plain, (![A_131]: (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', A_131))) | ~r1_tarski(k1_relat_1('#skF_3'), A_131))), inference(demodulation, [status(thm), theory('equality')], [c_1606, c_1096])).
% 5.05/2.02  tff(c_83, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_50])).
% 5.05/2.02  tff(c_104, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitLeft, [status(thm)], [c_83])).
% 5.05/2.02  tff(c_1857, plain, (~r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_1849, c_104])).
% 5.05/2.02  tff(c_1874, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_329, c_1857])).
% 5.05/2.02  tff(c_1876, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_83])).
% 5.05/2.02  tff(c_2, plain, (![B_3, A_1]: (v1_relat_1(B_3) | ~m1_subset_1(B_3, k1_zfmisc_1(A_1)) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.05/2.02  tff(c_1885, plain, (v1_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_1876, c_2])).
% 5.05/2.02  tff(c_1890, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_1885])).
% 5.05/2.02  tff(c_1887, plain, (v4_relat_1(k2_funct_1('#skF_3'), '#skF_2')), inference(resolution, [status(thm)], [c_1876, c_32])).
% 5.05/2.02  tff(c_1900, plain, (k7_relat_1(k2_funct_1('#skF_3'), '#skF_2')=k2_funct_1('#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_1887, c_14])).
% 5.05/2.02  tff(c_1903, plain, (k7_relat_1(k2_funct_1('#skF_3'), '#skF_2')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1890, c_1900])).
% 5.05/2.02  tff(c_1928, plain, (k9_relat_1(k2_funct_1('#skF_3'), '#skF_2')=k2_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1903, c_1913])).
% 5.05/2.02  tff(c_1935, plain, (k9_relat_1(k2_funct_1('#skF_3'), '#skF_2')=k2_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1890, c_1928])).
% 5.05/2.02  tff(c_2035, plain, (![A_147]: (m1_subset_1(A_147, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_147), k2_relat_1(A_147)))) | ~v1_funct_1(A_147) | ~v1_relat_1(A_147))), inference(cnfTransformation, [status(thm)], [f_122])).
% 5.05/2.02  tff(c_2050, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2'))) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2000, c_2035])).
% 5.05/2.02  tff(c_2067, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_60, c_2050])).
% 5.05/2.02  tff(c_2093, plain, (v4_relat_1('#skF_3', k1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_2067, c_32])).
% 5.05/2.02  tff(c_2103, plain, (k7_relat_1('#skF_3', k1_relat_1('#skF_3'))='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_2093, c_14])).
% 5.05/2.02  tff(c_2106, plain, (k7_relat_1('#skF_3', k1_relat_1('#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_2103])).
% 5.05/2.02  tff(c_2110, plain, (k9_relat_1('#skF_3', k1_relat_1('#skF_3'))=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2106, c_10])).
% 5.05/2.02  tff(c_2114, plain, (k9_relat_1('#skF_3', k1_relat_1('#skF_3'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_2000, c_2110])).
% 5.05/2.02  tff(c_30, plain, (![C_23, B_22, A_21]: (v5_relat_1(C_23, B_22) | ~m1_subset_1(C_23, k1_zfmisc_1(k2_zfmisc_1(A_21, B_22))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 5.05/2.02  tff(c_2061, plain, (![A_147]: (v5_relat_1(A_147, k2_relat_1(A_147)) | ~v1_funct_1(A_147) | ~v1_relat_1(A_147))), inference(resolution, [status(thm)], [c_2035, c_30])).
% 5.05/2.02  tff(c_1946, plain, (![B_138, A_139]: (r1_tarski(k2_relat_1(B_138), A_139) | ~v5_relat_1(B_138, A_139) | ~v1_relat_1(B_138))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.05/2.02  tff(c_2606, plain, (![B_184, A_185, A_186]: (r1_tarski(k9_relat_1(B_184, A_185), A_186) | ~v5_relat_1(k7_relat_1(B_184, A_185), A_186) | ~v1_relat_1(k7_relat_1(B_184, A_185)) | ~v1_relat_1(B_184))), inference(superposition, [status(thm), theory('equality')], [c_10, c_1946])).
% 5.05/2.02  tff(c_2619, plain, (![A_186]: (r1_tarski(k9_relat_1(k2_funct_1('#skF_3'), '#skF_2'), A_186) | ~v5_relat_1(k2_funct_1('#skF_3'), A_186) | ~v1_relat_1(k7_relat_1(k2_funct_1('#skF_3'), '#skF_2')) | ~v1_relat_1(k2_funct_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_1903, c_2606])).
% 5.05/2.02  tff(c_2630, plain, (![A_187]: (r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), A_187) | ~v5_relat_1(k2_funct_1('#skF_3'), A_187))), inference(demodulation, [status(thm), theory('equality')], [c_1890, c_1890, c_1903, c_1935, c_2619])).
% 5.05/2.02  tff(c_2647, plain, (![A_187]: (r1_tarski(k1_relat_1('#skF_3'), A_187) | ~v5_relat_1(k2_funct_1('#skF_3'), A_187) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_26, c_2630])).
% 5.05/2.02  tff(c_2659, plain, (![A_188]: (r1_tarski(k1_relat_1('#skF_3'), A_188) | ~v5_relat_1(k2_funct_1('#skF_3'), A_188))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_60, c_54, c_2647])).
% 5.05/2.02  tff(c_2666, plain, (r1_tarski(k1_relat_1('#skF_3'), k2_relat_1(k2_funct_1('#skF_3'))) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_2061, c_2659])).
% 5.05/2.02  tff(c_2673, plain, (r1_tarski(k1_relat_1('#skF_3'), k2_relat_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_1890, c_84, c_2666])).
% 5.05/2.02  tff(c_2680, plain, (k9_relat_1(k2_funct_1('#skF_3'), k10_relat_1(k2_funct_1('#skF_3'), k1_relat_1('#skF_3')))=k1_relat_1('#skF_3') | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_2673, c_20])).
% 5.05/2.02  tff(c_2688, plain, (k9_relat_1(k2_funct_1('#skF_3'), k10_relat_1(k2_funct_1('#skF_3'), k1_relat_1('#skF_3')))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1890, c_84, c_2680])).
% 5.05/2.02  tff(c_2739, plain, (k9_relat_1(k2_funct_1('#skF_3'), k9_relat_1('#skF_3', k1_relat_1('#skF_3')))=k1_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_24, c_2688])).
% 5.05/2.02  tff(c_2745, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_60, c_54, c_1935, c_2114, c_2739])).
% 5.05/2.02  tff(c_2787, plain, (k10_relat_1(k2_funct_1('#skF_3'), k1_relat_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_2745, c_12])).
% 5.05/2.02  tff(c_2813, plain, (k10_relat_1(k2_funct_1('#skF_3'), k1_relat_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1890, c_2787])).
% 5.05/2.02  tff(c_2868, plain, (k9_relat_1('#skF_3', k1_relat_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2813, c_24])).
% 5.05/2.02  tff(c_2875, plain, (k1_relat_1(k2_funct_1('#skF_3'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_60, c_54, c_2114, c_2868])).
% 5.05/2.02  tff(c_46, plain, (![B_33, A_32]: (v1_funct_2(B_33, k1_relat_1(B_33), A_32) | ~r1_tarski(k2_relat_1(B_33), A_32) | ~v1_funct_1(B_33) | ~v1_relat_1(B_33))), inference(cnfTransformation, [status(thm)], [f_134])).
% 5.05/2.02  tff(c_2914, plain, (![A_32]: (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', A_32) | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), A_32) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_2875, c_46])).
% 5.05/2.02  tff(c_3040, plain, (![A_195]: (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', A_195) | ~r1_tarski(k1_relat_1('#skF_3'), A_195))), inference(demodulation, [status(thm), theory('equality')], [c_1890, c_84, c_2745, c_2914])).
% 5.05/2.02  tff(c_1875, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_83])).
% 5.05/2.02  tff(c_3043, plain, (~r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_3040, c_1875])).
% 5.05/2.02  tff(c_3047, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2235, c_3043])).
% 5.05/2.02  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.05/2.02  
% 5.05/2.02  Inference rules
% 5.05/2.02  ----------------------
% 5.05/2.02  #Ref     : 0
% 5.05/2.02  #Sup     : 676
% 5.05/2.02  #Fact    : 0
% 5.05/2.02  #Define  : 0
% 5.05/2.02  #Split   : 5
% 5.05/2.02  #Chain   : 0
% 5.05/2.02  #Close   : 0
% 5.05/2.02  
% 5.05/2.02  Ordering : KBO
% 5.05/2.02  
% 5.05/2.02  Simplification rules
% 5.05/2.02  ----------------------
% 5.05/2.02  #Subsume      : 61
% 5.05/2.02  #Demod        : 1061
% 5.05/2.02  #Tautology    : 354
% 5.05/2.02  #SimpNegUnit  : 0
% 5.05/2.02  #BackRed      : 30
% 5.05/2.02  
% 5.05/2.02  #Partial instantiations: 0
% 5.05/2.02  #Strategies tried      : 1
% 5.05/2.02  
% 5.05/2.02  Timing (in seconds)
% 5.05/2.02  ----------------------
% 5.05/2.03  Preprocessing        : 0.37
% 5.05/2.03  Parsing              : 0.20
% 5.05/2.03  CNF conversion       : 0.02
% 5.05/2.03  Main loop            : 0.76
% 5.05/2.03  Inferencing          : 0.29
% 5.05/2.03  Reduction            : 0.26
% 5.05/2.03  Demodulation         : 0.20
% 5.05/2.03  BG Simplification    : 0.03
% 5.05/2.03  Subsumption          : 0.11
% 5.05/2.03  Abstraction          : 0.03
% 5.05/2.03  MUC search           : 0.00
% 5.05/2.03  Cooper               : 0.00
% 5.05/2.03  Total                : 1.19
% 5.05/2.03  Index Insertion      : 0.00
% 5.05/2.03  Index Deletion       : 0.00
% 5.05/2.03  Index Matching       : 0.00
% 5.05/2.03  BG Taut test         : 0.00
%------------------------------------------------------------------------------
