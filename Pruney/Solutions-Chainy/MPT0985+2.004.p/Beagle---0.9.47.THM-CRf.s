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
% DateTime   : Thu Dec  3 10:12:25 EST 2020

% Result     : Theorem 4.77s
% Output     : CNFRefutation 5.11s
% Verified   : 
% Statistics : Number of formulae       :  232 (2386 expanded)
%              Number of leaves         :   38 ( 781 expanded)
%              Depth                    :   16
%              Number of atoms          :  439 (5967 expanded)
%              Number of equality atoms :   99 (1138 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v1_partfun1 > r2_hidden > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

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

tff(f_106,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_partfun1(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_partfun1)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_89,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_70,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_81,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).

tff(f_60,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_124,axiom,(
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

tff(f_134,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_34,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

tff(f_42,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_52,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_funct_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_1)).

tff(f_99,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v1_partfun1(C,A) )
       => ( v1_funct_1(C)
          & v1_funct_2(C,A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_2)).

tff(c_64,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_222,plain,(
    ! [C_65,A_66,B_67] :
      ( v1_partfun1(C_65,A_66)
      | ~ m1_subset_1(C_65,k1_zfmisc_1(k2_zfmisc_1(A_66,B_67)))
      | ~ v1_xboole_0(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_236,plain,
    ( v1_partfun1('#skF_3','#skF_1')
    | ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_64,c_222])).

tff(c_240,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_236])).

tff(c_119,plain,(
    ! [C_46,A_47,B_48] :
      ( v1_relat_1(C_46)
      | ~ m1_subset_1(C_46,k1_zfmisc_1(k2_zfmisc_1(A_47,B_48))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_131,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_119])).

tff(c_68,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_62,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_60,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_1092,plain,(
    ! [A_144,B_145,C_146] :
      ( k2_relset_1(A_144,B_145,C_146) = k2_relat_1(C_146)
      | ~ m1_subset_1(C_146,k1_zfmisc_1(k2_zfmisc_1(A_144,B_145))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_1098,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_1092])).

tff(c_1111,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_1098])).

tff(c_24,plain,(
    ! [A_11] :
      ( k1_relat_1(k2_funct_1(A_11)) = k2_relat_1(A_11)
      | ~ v2_funct_1(A_11)
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_170,plain,(
    ! [C_58,B_59,A_60] :
      ( v1_xboole_0(C_58)
      | ~ m1_subset_1(C_58,k1_zfmisc_1(k2_zfmisc_1(B_59,A_60)))
      | ~ v1_xboole_0(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_184,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_170])).

tff(c_189,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_184])).

tff(c_18,plain,(
    ! [A_10] :
      ( v1_funct_1(k2_funct_1(A_10))
      | ~ v1_funct_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_58,plain,
    ( ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_133,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_136,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_18,c_133])).

tff(c_140,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_68,c_136])).

tff(c_141,plain,
    ( ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_241,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_141])).

tff(c_66,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_353,plain,(
    ! [A_79,B_80,C_81] :
      ( k1_relset_1(A_79,B_80,C_81) = k1_relat_1(C_81)
      | ~ m1_subset_1(C_81,k1_zfmisc_1(k2_zfmisc_1(A_79,B_80))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_375,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_353])).

tff(c_626,plain,(
    ! [B_112,A_113,C_114] :
      ( k1_xboole_0 = B_112
      | k1_relset_1(A_113,B_112,C_114) = A_113
      | ~ v1_funct_2(C_114,A_113,B_112)
      | ~ m1_subset_1(C_114,k1_zfmisc_1(k2_zfmisc_1(A_113,B_112))) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_635,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_626])).

tff(c_652,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_375,c_635])).

tff(c_656,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_652])).

tff(c_22,plain,(
    ! [A_11] :
      ( k2_relat_1(k2_funct_1(A_11)) = k1_relat_1(A_11)
      | ~ v2_funct_1(A_11)
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_20,plain,(
    ! [A_10] :
      ( v1_relat_1(k2_funct_1(A_10))
      | ~ v1_funct_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_142,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_254,plain,(
    ! [A_72,B_73,C_74] :
      ( k2_relset_1(A_72,B_73,C_74) = k2_relat_1(C_74)
      | ~ m1_subset_1(C_74,k1_zfmisc_1(k2_zfmisc_1(A_72,B_73))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_257,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_254])).

tff(c_269,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_257])).

tff(c_198,plain,(
    ! [A_63] :
      ( k1_relat_1(k2_funct_1(A_63)) = k2_relat_1(A_63)
      | ~ v2_funct_1(A_63)
      | ~ v1_funct_1(A_63)
      | ~ v1_relat_1(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_54,plain,(
    ! [A_35] :
      ( v1_funct_2(A_35,k1_relat_1(A_35),k2_relat_1(A_35))
      | ~ v1_funct_1(A_35)
      | ~ v1_relat_1(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_864,plain,(
    ! [A_133] :
      ( v1_funct_2(k2_funct_1(A_133),k2_relat_1(A_133),k2_relat_1(k2_funct_1(A_133)))
      | ~ v1_funct_1(k2_funct_1(A_133))
      | ~ v1_relat_1(k2_funct_1(A_133))
      | ~ v2_funct_1(A_133)
      | ~ v1_funct_1(A_133)
      | ~ v1_relat_1(A_133) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_198,c_54])).

tff(c_867,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_2',k2_relat_1(k2_funct_1('#skF_3')))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_269,c_864])).

tff(c_875,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_2',k2_relat_1(k2_funct_1('#skF_3')))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_68,c_62,c_142,c_867])).

tff(c_876,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_875])).

tff(c_879,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_876])).

tff(c_883,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_68,c_879])).

tff(c_885,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_875])).

tff(c_287,plain,(
    ! [A_77] :
      ( m1_subset_1(A_77,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_77),k2_relat_1(A_77))))
      | ~ v1_funct_1(A_77)
      | ~ v1_relat_1(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_935,plain,(
    ! [A_138] :
      ( m1_subset_1(k2_funct_1(A_138),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_138),k2_relat_1(k2_funct_1(A_138)))))
      | ~ v1_funct_1(k2_funct_1(A_138))
      | ~ v1_relat_1(k2_funct_1(A_138))
      | ~ v2_funct_1(A_138)
      | ~ v1_funct_1(A_138)
      | ~ v1_relat_1(A_138) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_287])).

tff(c_964,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2',k2_relat_1(k2_funct_1('#skF_3')))))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_269,c_935])).

tff(c_981,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2',k2_relat_1(k2_funct_1('#skF_3'))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_68,c_62,c_885,c_142,c_964])).

tff(c_1010,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2',k1_relat_1('#skF_3'))))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_981])).

tff(c_1027,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_68,c_62,c_656,c_1010])).

tff(c_1029,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_241,c_1027])).

tff(c_1030,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_652])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_1059,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1030,c_2])).

tff(c_1061,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_189,c_1059])).

tff(c_1062,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_141])).

tff(c_1063,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_141])).

tff(c_1200,plain,(
    ! [A_152,B_153,C_154] :
      ( k1_relset_1(A_152,B_153,C_154) = k1_relat_1(C_154)
      | ~ m1_subset_1(C_154,k1_zfmisc_1(k2_zfmisc_1(A_152,B_153))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_1225,plain,(
    k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_1063,c_1200])).

tff(c_1486,plain,(
    ! [B_184,C_185,A_186] :
      ( k1_xboole_0 = B_184
      | v1_funct_2(C_185,A_186,B_184)
      | k1_relset_1(A_186,B_184,C_185) != A_186
      | ~ m1_subset_1(C_185,k1_zfmisc_1(k2_zfmisc_1(A_186,B_184))) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_1495,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(resolution,[status(thm)],[c_1063,c_1486])).

tff(c_1514,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1225,c_1495])).

tff(c_1515,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_1062,c_1514])).

tff(c_1523,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_1515])).

tff(c_1526,plain,
    ( k2_relat_1('#skF_3') != '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_1523])).

tff(c_1529,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_68,c_62,c_1111,c_1526])).

tff(c_1530,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_1515])).

tff(c_1559,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1530,c_2])).

tff(c_1561,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_240,c_1559])).

tff(c_1563,plain,(
    v1_xboole_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_236])).

tff(c_106,plain,(
    ! [B_40,A_41] :
      ( ~ v1_xboole_0(B_40)
      | B_40 = A_41
      | ~ v1_xboole_0(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_109,plain,(
    ! [A_41] :
      ( k1_xboole_0 = A_41
      | ~ v1_xboole_0(A_41) ) ),
    inference(resolution,[status(thm)],[c_2,c_106])).

tff(c_1579,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_1563,c_109])).

tff(c_12,plain,(
    ! [A_5] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_40,plain,(
    ! [A_32] :
      ( v1_funct_2(k1_xboole_0,A_32,k1_xboole_0)
      | k1_xboole_0 = A_32
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_32,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_70,plain,(
    ! [A_32] :
      ( v1_funct_2(k1_xboole_0,A_32,k1_xboole_0)
      | k1_xboole_0 = A_32 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_40])).

tff(c_1588,plain,(
    ! [A_32] :
      ( v1_funct_2('#skF_1',A_32,'#skF_1')
      | A_32 = '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1579,c_1579,c_1579,c_70])).

tff(c_10,plain,(
    ! [B_4] : k2_zfmisc_1(k1_xboole_0,B_4) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_1590,plain,(
    ! [B_4] : k2_zfmisc_1('#skF_1',B_4) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1579,c_1579,c_10])).

tff(c_2279,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1590,c_64])).

tff(c_8,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_179,plain,(
    ! [C_58] :
      ( v1_xboole_0(C_58)
      | ~ m1_subset_1(C_58,k1_zfmisc_1(k1_xboole_0))
      | ~ v1_xboole_0(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_170])).

tff(c_186,plain,(
    ! [C_58] :
      ( v1_xboole_0(C_58)
      | ~ m1_subset_1(C_58,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_179])).

tff(c_2348,plain,(
    ! [C_274] :
      ( v1_xboole_0(C_274)
      | ~ m1_subset_1(C_274,k1_zfmisc_1('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1579,c_186])).

tff(c_2356,plain,(
    v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_2279,c_2348])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( ~ v1_xboole_0(B_2)
      | B_2 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_1580,plain,(
    ! [A_1] :
      ( A_1 = '#skF_1'
      | ~ v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_1563,c_4])).

tff(c_2379,plain,(
    '#skF_3' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_2356,c_1580])).

tff(c_1591,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1579,c_1579,c_8])).

tff(c_1593,plain,(
    ! [A_5] : m1_subset_1('#skF_1',k1_zfmisc_1(A_5)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1579,c_12])).

tff(c_132,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_12,c_119])).

tff(c_1587,plain,(
    v1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1579,c_132])).

tff(c_16,plain,(
    ! [A_9] :
      ( v1_funct_1(A_9)
      | ~ v1_xboole_0(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_1581,plain,(
    v1_funct_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_1563,c_16])).

tff(c_1648,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1590,c_64])).

tff(c_1706,plain,(
    ! [C_202] :
      ( v1_xboole_0(C_202)
      | ~ m1_subset_1(C_202,k1_zfmisc_1('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1579,c_186])).

tff(c_1714,plain,(
    v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_1648,c_1706])).

tff(c_1589,plain,(
    ! [A_41] :
      ( A_41 = '#skF_1'
      | ~ v1_xboole_0(A_41) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1579,c_109])).

tff(c_1725,plain,(
    '#skF_3' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_1714,c_1589])).

tff(c_1738,plain,(
    v2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1725,c_62])).

tff(c_1734,plain,(
    v1_funct_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1725,c_142])).

tff(c_1748,plain,(
    ! [A_203,B_204,C_205] :
      ( k1_relset_1(A_203,B_204,C_205) = k1_relat_1(C_205)
      | ~ m1_subset_1(C_205,k1_zfmisc_1(k2_zfmisc_1(A_203,B_204))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_1759,plain,(
    ! [A_203,B_204] : k1_relset_1(A_203,B_204,'#skF_1') = k1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_1593,c_1748])).

tff(c_1737,plain,(
    v1_funct_2('#skF_1','#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1725,c_66])).

tff(c_48,plain,(
    ! [B_33,C_34] :
      ( k1_relset_1(k1_xboole_0,B_33,C_34) = k1_xboole_0
      | ~ v1_funct_2(C_34,k1_xboole_0,B_33)
      | ~ m1_subset_1(C_34,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_33))) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_71,plain,(
    ! [B_33,C_34] :
      ( k1_relset_1(k1_xboole_0,B_33,C_34) = k1_xboole_0
      | ~ v1_funct_2(C_34,k1_xboole_0,B_33)
      | ~ m1_subset_1(C_34,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_48])).

tff(c_1858,plain,(
    ! [B_216,C_217] :
      ( k1_relset_1('#skF_1',B_216,C_217) = '#skF_1'
      | ~ v1_funct_2(C_217,'#skF_1',B_216)
      | ~ m1_subset_1(C_217,k1_zfmisc_1('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1579,c_1579,c_1579,c_1579,c_71])).

tff(c_1860,plain,
    ( k1_relset_1('#skF_1','#skF_2','#skF_1') = '#skF_1'
    | ~ m1_subset_1('#skF_1',k1_zfmisc_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_1737,c_1858])).

tff(c_1866,plain,(
    k1_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1593,c_1759,c_1860])).

tff(c_1773,plain,(
    ! [A_208] :
      ( m1_subset_1(A_208,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_208),k2_relat_1(A_208))))
      | ~ v1_funct_1(A_208)
      | ~ v1_relat_1(A_208) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_28,plain,(
    ! [C_18,B_16,A_15] :
      ( v1_xboole_0(C_18)
      | ~ m1_subset_1(C_18,k1_zfmisc_1(k2_zfmisc_1(B_16,A_15)))
      | ~ v1_xboole_0(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_1926,plain,(
    ! [A_227] :
      ( v1_xboole_0(A_227)
      | ~ v1_xboole_0(k2_relat_1(A_227))
      | ~ v1_funct_1(A_227)
      | ~ v1_relat_1(A_227) ) ),
    inference(resolution,[status(thm)],[c_1773,c_28])).

tff(c_2206,plain,(
    ! [A_261] :
      ( v1_xboole_0(k2_funct_1(A_261))
      | ~ v1_xboole_0(k1_relat_1(A_261))
      | ~ v1_funct_1(k2_funct_1(A_261))
      | ~ v1_relat_1(k2_funct_1(A_261))
      | ~ v2_funct_1(A_261)
      | ~ v1_funct_1(A_261)
      | ~ v1_relat_1(A_261) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_1926])).

tff(c_2218,plain,(
    ! [A_262] :
      ( k2_funct_1(A_262) = '#skF_1'
      | ~ v1_xboole_0(k1_relat_1(A_262))
      | ~ v1_funct_1(k2_funct_1(A_262))
      | ~ v1_relat_1(k2_funct_1(A_262))
      | ~ v2_funct_1(A_262)
      | ~ v1_funct_1(A_262)
      | ~ v1_relat_1(A_262) ) ),
    inference(resolution,[status(thm)],[c_2206,c_1589])).

tff(c_2221,plain,
    ( k2_funct_1('#skF_1') = '#skF_1'
    | ~ v1_xboole_0('#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_1'))
    | ~ v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1866,c_2218])).

tff(c_2226,plain,
    ( k2_funct_1('#skF_1') = '#skF_1'
    | ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1587,c_1581,c_1738,c_1734,c_1563,c_2221])).

tff(c_2227,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_2226])).

tff(c_2242,plain,
    ( ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_2227])).

tff(c_2246,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1587,c_1581,c_2242])).

tff(c_2247,plain,(
    k2_funct_1('#skF_1') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_2226])).

tff(c_1600,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_141])).

tff(c_1629,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1591,c_1600])).

tff(c_1731,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_1'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1725,c_1629])).

tff(c_2249,plain,(
    ~ m1_subset_1('#skF_1',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2247,c_1731])).

tff(c_2253,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1593,c_2249])).

tff(c_2255,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_141])).

tff(c_2359,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1591,c_2255])).

tff(c_1583,plain,(
    ! [C_58] :
      ( v1_xboole_0(C_58)
      | ~ m1_subset_1(C_58,k1_zfmisc_1('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1579,c_186])).

tff(c_2368,plain,(
    v1_xboole_0(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_2359,c_1583])).

tff(c_2403,plain,(
    v1_xboole_0(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2379,c_2368])).

tff(c_2412,plain,(
    k2_funct_1('#skF_1') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_2403,c_1580])).

tff(c_2254,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_141])).

tff(c_2387,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_1'),'#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2379,c_2254])).

tff(c_2474,plain,(
    ~ v1_funct_2('#skF_1','#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2412,c_2387])).

tff(c_2478,plain,(
    '#skF_2' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_1588,c_2474])).

tff(c_2482,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2478,c_189])).

tff(c_2485,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1563,c_2482])).

tff(c_2486,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_184])).

tff(c_2496,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_2486,c_109])).

tff(c_2521,plain,(
    ! [A_5] : m1_subset_1('#skF_3',k1_zfmisc_1(A_5)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2496,c_12])).

tff(c_2518,plain,(
    ! [B_4] : k2_zfmisc_1('#skF_3',B_4) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2496,c_2496,c_10])).

tff(c_2584,plain,(
    ! [C_282,A_283,B_284] :
      ( v1_partfun1(C_282,A_283)
      | ~ m1_subset_1(C_282,k1_zfmisc_1(k2_zfmisc_1(A_283,B_284)))
      | ~ v1_xboole_0(A_283) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_2587,plain,(
    ! [C_282] :
      ( v1_partfun1(C_282,'#skF_3')
      | ~ m1_subset_1(C_282,k1_zfmisc_1('#skF_3'))
      | ~ v1_xboole_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2518,c_2584])).

tff(c_3378,plain,(
    ! [C_368] :
      ( v1_partfun1(C_368,'#skF_3')
      | ~ m1_subset_1(C_368,k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2486,c_2587])).

tff(c_3383,plain,(
    v1_partfun1('#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_2521,c_3378])).

tff(c_3610,plain,(
    ! [C_402,A_403,B_404] :
      ( v1_funct_2(C_402,A_403,B_404)
      | ~ v1_partfun1(C_402,A_403)
      | ~ v1_funct_1(C_402)
      | ~ m1_subset_1(C_402,k1_zfmisc_1(k2_zfmisc_1(A_403,B_404))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_3617,plain,(
    ! [A_403,B_404] :
      ( v1_funct_2('#skF_3',A_403,B_404)
      | ~ v1_partfun1('#skF_3',A_403)
      | ~ v1_funct_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_2521,c_3610])).

tff(c_3628,plain,(
    ! [A_405,B_406] :
      ( v1_funct_2('#skF_3',A_405,B_406)
      | ~ v1_partfun1('#skF_3',A_405) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_3617])).

tff(c_2717,plain,(
    ! [A_302,B_303,C_304] :
      ( k1_relset_1(A_302,B_303,C_304) = k1_relat_1(C_304)
      | ~ m1_subset_1(C_304,k1_zfmisc_1(k2_zfmisc_1(A_302,B_303))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_2732,plain,(
    ! [A_302,B_303] : k1_relset_1(A_302,B_303,'#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2521,c_2717])).

tff(c_44,plain,(
    ! [C_34,B_33] :
      ( v1_funct_2(C_34,k1_xboole_0,B_33)
      | k1_relset_1(k1_xboole_0,B_33,C_34) != k1_xboole_0
      | ~ m1_subset_1(C_34,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_33))) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_72,plain,(
    ! [C_34,B_33] :
      ( v1_funct_2(C_34,k1_xboole_0,B_33)
      | k1_relset_1(k1_xboole_0,B_33,C_34) != k1_xboole_0
      | ~ m1_subset_1(C_34,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_44])).

tff(c_2841,plain,(
    ! [C_324,B_325] :
      ( v1_funct_2(C_324,'#skF_3',B_325)
      | k1_relset_1('#skF_3',B_325,C_324) != '#skF_3'
      | ~ m1_subset_1(C_324,k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2496,c_2496,c_2496,c_2496,c_72])).

tff(c_2844,plain,(
    ! [B_325] :
      ( v1_funct_2('#skF_3','#skF_3',B_325)
      | k1_relset_1('#skF_3',B_325,'#skF_3') != '#skF_3' ) ),
    inference(resolution,[status(thm)],[c_2521,c_2841])).

tff(c_2846,plain,(
    ! [B_325] :
      ( v1_funct_2('#skF_3','#skF_3',B_325)
      | k1_relat_1('#skF_3') != '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2732,c_2844])).

tff(c_2847,plain,(
    k1_relat_1('#skF_3') != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_2846])).

tff(c_2651,plain,(
    ! [C_293] :
      ( v1_partfun1(C_293,'#skF_3')
      | ~ m1_subset_1(C_293,k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2486,c_2587])).

tff(c_2656,plain,(
    v1_partfun1('#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_2521,c_2651])).

tff(c_2880,plain,(
    ! [C_327,A_328,B_329] :
      ( v1_funct_2(C_327,A_328,B_329)
      | ~ v1_partfun1(C_327,A_328)
      | ~ v1_funct_1(C_327)
      | ~ m1_subset_1(C_327,k1_zfmisc_1(k2_zfmisc_1(A_328,B_329))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_2887,plain,(
    ! [A_328,B_329] :
      ( v1_funct_2('#skF_3',A_328,B_329)
      | ~ v1_partfun1('#skF_3',A_328)
      | ~ v1_funct_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_2521,c_2880])).

tff(c_2897,plain,(
    ! [A_328,B_329] :
      ( v1_funct_2('#skF_3',A_328,B_329)
      | ~ v1_partfun1('#skF_3',A_328) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_2887])).

tff(c_2941,plain,(
    ! [B_333,C_334] :
      ( k1_relset_1('#skF_3',B_333,C_334) = '#skF_3'
      | ~ v1_funct_2(C_334,'#skF_3',B_333)
      | ~ m1_subset_1(C_334,k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2496,c_2496,c_2496,c_2496,c_71])).

tff(c_2944,plain,(
    ! [B_329] :
      ( k1_relset_1('#skF_3',B_329,'#skF_3') = '#skF_3'
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3'))
      | ~ v1_partfun1('#skF_3','#skF_3') ) ),
    inference(resolution,[status(thm)],[c_2897,c_2941])).

tff(c_2950,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2656,c_2521,c_2732,c_2944])).

tff(c_2952,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2847,c_2950])).

tff(c_2954,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_2846])).

tff(c_2687,plain,(
    ! [A_299] :
      ( m1_subset_1(A_299,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_299),k2_relat_1(A_299))))
      | ~ v1_funct_1(A_299)
      | ~ v1_relat_1(A_299) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_2709,plain,(
    ! [A_300] :
      ( v1_xboole_0(A_300)
      | ~ v1_xboole_0(k2_relat_1(A_300))
      | ~ v1_funct_1(A_300)
      | ~ v1_relat_1(A_300) ) ),
    inference(resolution,[status(thm)],[c_2687,c_28])).

tff(c_3247,plain,(
    ! [A_364] :
      ( v1_xboole_0(k2_funct_1(A_364))
      | ~ v1_xboole_0(k1_relat_1(A_364))
      | ~ v1_funct_1(k2_funct_1(A_364))
      | ~ v1_relat_1(k2_funct_1(A_364))
      | ~ v2_funct_1(A_364)
      | ~ v1_funct_1(A_364)
      | ~ v1_relat_1(A_364) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_2709])).

tff(c_2487,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_184])).

tff(c_2508,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_2487,c_109])).

tff(c_2530,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2496,c_2508])).

tff(c_2509,plain,(
    ! [A_1] :
      ( A_1 = '#skF_2'
      | ~ v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_2487,c_4])).

tff(c_2543,plain,(
    ! [A_1] :
      ( A_1 = '#skF_3'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2530,c_2509])).

tff(c_3259,plain,(
    ! [A_365] :
      ( k2_funct_1(A_365) = '#skF_3'
      | ~ v1_xboole_0(k1_relat_1(A_365))
      | ~ v1_funct_1(k2_funct_1(A_365))
      | ~ v1_relat_1(k2_funct_1(A_365))
      | ~ v2_funct_1(A_365)
      | ~ v1_funct_1(A_365)
      | ~ v1_relat_1(A_365) ) ),
    inference(resolution,[status(thm)],[c_3247,c_2543])).

tff(c_3262,plain,
    ( k2_funct_1('#skF_3') = '#skF_3'
    | ~ v1_xboole_0('#skF_3')
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2954,c_3259])).

tff(c_3267,plain,
    ( k2_funct_1('#skF_3') = '#skF_3'
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_68,c_62,c_142,c_2486,c_3262])).

tff(c_3280,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_3267])).

tff(c_3283,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_3280])).

tff(c_3287,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_68,c_3283])).

tff(c_3288,plain,(
    k2_funct_1('#skF_3') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_3267])).

tff(c_2649,plain,
    ( ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_3','#skF_1')
    | ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2518,c_2530,c_2530,c_141])).

tff(c_2650,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_2649])).

tff(c_3290,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3288,c_2650])).

tff(c_3294,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2521,c_3290])).

tff(c_3296,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_2649])).

tff(c_2620,plain,(
    ! [C_58] :
      ( v1_xboole_0(C_58)
      | ~ m1_subset_1(C_58,k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2496,c_186])).

tff(c_3307,plain,(
    v1_xboole_0(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_3296,c_2620])).

tff(c_3317,plain,(
    k2_funct_1('#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_3307,c_2543])).

tff(c_3295,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_2649])).

tff(c_3324,plain,(
    ~ v1_funct_2('#skF_3','#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3317,c_3295])).

tff(c_3637,plain,(
    ~ v1_partfun1('#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_3628,c_3324])).

tff(c_3648,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3383,c_3637])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:07:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.77/1.89  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.11/1.92  
% 5.11/1.92  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.11/1.92  %$ v1_funct_2 > v1_partfun1 > r2_hidden > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 5.11/1.92  
% 5.11/1.92  %Foreground sorts:
% 5.11/1.92  
% 5.11/1.92  
% 5.11/1.92  %Background operators:
% 5.11/1.92  
% 5.11/1.92  
% 5.11/1.92  %Foreground operators:
% 5.11/1.92  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 5.11/1.92  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.11/1.92  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 5.11/1.92  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 5.11/1.92  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.11/1.92  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.11/1.92  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.11/1.92  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.11/1.92  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.11/1.92  tff('#skF_2', type, '#skF_2': $i).
% 5.11/1.92  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 5.11/1.92  tff('#skF_3', type, '#skF_3': $i).
% 5.11/1.92  tff('#skF_1', type, '#skF_1': $i).
% 5.11/1.92  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 5.11/1.92  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.11/1.92  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.11/1.92  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.11/1.92  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.11/1.92  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.11/1.92  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.11/1.92  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.11/1.92  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.11/1.92  
% 5.11/1.94  tff(f_151, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_funct_2)).
% 5.11/1.94  tff(f_106, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_partfun1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_partfun1)).
% 5.11/1.94  tff(f_74, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 5.11/1.94  tff(f_89, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 5.11/1.94  tff(f_70, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 5.11/1.94  tff(f_81, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => v1_xboole_0(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc4_relset_1)).
% 5.11/1.94  tff(f_60, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 5.11/1.94  tff(f_85, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 5.11/1.94  tff(f_124, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 5.11/1.94  tff(f_134, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_funct_2)).
% 5.11/1.94  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 5.11/1.94  tff(f_34, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 5.11/1.94  tff(f_42, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 5.11/1.94  tff(f_40, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 5.11/1.94  tff(f_52, axiom, (![A]: (v1_xboole_0(A) => v1_funct_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_funct_1)).
% 5.11/1.94  tff(f_99, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_partfun1(C, A)) => (v1_funct_1(C) & v1_funct_2(C, A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_funct_2)).
% 5.11/1.94  tff(c_64, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_151])).
% 5.11/1.94  tff(c_222, plain, (![C_65, A_66, B_67]: (v1_partfun1(C_65, A_66) | ~m1_subset_1(C_65, k1_zfmisc_1(k2_zfmisc_1(A_66, B_67))) | ~v1_xboole_0(A_66))), inference(cnfTransformation, [status(thm)], [f_106])).
% 5.11/1.94  tff(c_236, plain, (v1_partfun1('#skF_3', '#skF_1') | ~v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_64, c_222])).
% 5.11/1.94  tff(c_240, plain, (~v1_xboole_0('#skF_1')), inference(splitLeft, [status(thm)], [c_236])).
% 5.11/1.94  tff(c_119, plain, (![C_46, A_47, B_48]: (v1_relat_1(C_46) | ~m1_subset_1(C_46, k1_zfmisc_1(k2_zfmisc_1(A_47, B_48))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 5.11/1.95  tff(c_131, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_64, c_119])).
% 5.11/1.95  tff(c_68, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_151])).
% 5.11/1.95  tff(c_62, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_151])).
% 5.11/1.95  tff(c_60, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_151])).
% 5.11/1.95  tff(c_1092, plain, (![A_144, B_145, C_146]: (k2_relset_1(A_144, B_145, C_146)=k2_relat_1(C_146) | ~m1_subset_1(C_146, k1_zfmisc_1(k2_zfmisc_1(A_144, B_145))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 5.11/1.95  tff(c_1098, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_64, c_1092])).
% 5.11/1.95  tff(c_1111, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_1098])).
% 5.11/1.95  tff(c_24, plain, (![A_11]: (k1_relat_1(k2_funct_1(A_11))=k2_relat_1(A_11) | ~v2_funct_1(A_11) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_70])).
% 5.11/1.95  tff(c_170, plain, (![C_58, B_59, A_60]: (v1_xboole_0(C_58) | ~m1_subset_1(C_58, k1_zfmisc_1(k2_zfmisc_1(B_59, A_60))) | ~v1_xboole_0(A_60))), inference(cnfTransformation, [status(thm)], [f_81])).
% 5.11/1.95  tff(c_184, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_64, c_170])).
% 5.11/1.95  tff(c_189, plain, (~v1_xboole_0('#skF_2')), inference(splitLeft, [status(thm)], [c_184])).
% 5.11/1.95  tff(c_18, plain, (![A_10]: (v1_funct_1(k2_funct_1(A_10)) | ~v1_funct_1(A_10) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.11/1.95  tff(c_58, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_151])).
% 5.11/1.95  tff(c_133, plain, (~v1_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_58])).
% 5.11/1.95  tff(c_136, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_18, c_133])).
% 5.11/1.95  tff(c_140, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_131, c_68, c_136])).
% 5.11/1.95  tff(c_141, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_58])).
% 5.11/1.95  tff(c_241, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitLeft, [status(thm)], [c_141])).
% 5.11/1.95  tff(c_66, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_151])).
% 5.11/1.95  tff(c_353, plain, (![A_79, B_80, C_81]: (k1_relset_1(A_79, B_80, C_81)=k1_relat_1(C_81) | ~m1_subset_1(C_81, k1_zfmisc_1(k2_zfmisc_1(A_79, B_80))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 5.11/1.95  tff(c_375, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_64, c_353])).
% 5.11/1.95  tff(c_626, plain, (![B_112, A_113, C_114]: (k1_xboole_0=B_112 | k1_relset_1(A_113, B_112, C_114)=A_113 | ~v1_funct_2(C_114, A_113, B_112) | ~m1_subset_1(C_114, k1_zfmisc_1(k2_zfmisc_1(A_113, B_112))))), inference(cnfTransformation, [status(thm)], [f_124])).
% 5.11/1.95  tff(c_635, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_64, c_626])).
% 5.11/1.95  tff(c_652, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_375, c_635])).
% 5.11/1.95  tff(c_656, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(splitLeft, [status(thm)], [c_652])).
% 5.11/1.95  tff(c_22, plain, (![A_11]: (k2_relat_1(k2_funct_1(A_11))=k1_relat_1(A_11) | ~v2_funct_1(A_11) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_70])).
% 5.11/1.95  tff(c_20, plain, (![A_10]: (v1_relat_1(k2_funct_1(A_10)) | ~v1_funct_1(A_10) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.11/1.95  tff(c_142, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_58])).
% 5.11/1.95  tff(c_254, plain, (![A_72, B_73, C_74]: (k2_relset_1(A_72, B_73, C_74)=k2_relat_1(C_74) | ~m1_subset_1(C_74, k1_zfmisc_1(k2_zfmisc_1(A_72, B_73))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 5.11/1.95  tff(c_257, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_64, c_254])).
% 5.11/1.95  tff(c_269, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_257])).
% 5.11/1.95  tff(c_198, plain, (![A_63]: (k1_relat_1(k2_funct_1(A_63))=k2_relat_1(A_63) | ~v2_funct_1(A_63) | ~v1_funct_1(A_63) | ~v1_relat_1(A_63))), inference(cnfTransformation, [status(thm)], [f_70])).
% 5.11/1.95  tff(c_54, plain, (![A_35]: (v1_funct_2(A_35, k1_relat_1(A_35), k2_relat_1(A_35)) | ~v1_funct_1(A_35) | ~v1_relat_1(A_35))), inference(cnfTransformation, [status(thm)], [f_134])).
% 5.11/1.95  tff(c_864, plain, (![A_133]: (v1_funct_2(k2_funct_1(A_133), k2_relat_1(A_133), k2_relat_1(k2_funct_1(A_133))) | ~v1_funct_1(k2_funct_1(A_133)) | ~v1_relat_1(k2_funct_1(A_133)) | ~v2_funct_1(A_133) | ~v1_funct_1(A_133) | ~v1_relat_1(A_133))), inference(superposition, [status(thm), theory('equality')], [c_198, c_54])).
% 5.11/1.95  tff(c_867, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', k2_relat_1(k2_funct_1('#skF_3'))) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_269, c_864])).
% 5.11/1.95  tff(c_875, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', k2_relat_1(k2_funct_1('#skF_3'))) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_131, c_68, c_62, c_142, c_867])).
% 5.11/1.95  tff(c_876, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_875])).
% 5.11/1.95  tff(c_879, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_20, c_876])).
% 5.11/1.95  tff(c_883, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_131, c_68, c_879])).
% 5.11/1.95  tff(c_885, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_875])).
% 5.11/1.95  tff(c_287, plain, (![A_77]: (m1_subset_1(A_77, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_77), k2_relat_1(A_77)))) | ~v1_funct_1(A_77) | ~v1_relat_1(A_77))), inference(cnfTransformation, [status(thm)], [f_134])).
% 5.11/1.95  tff(c_935, plain, (![A_138]: (m1_subset_1(k2_funct_1(A_138), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_138), k2_relat_1(k2_funct_1(A_138))))) | ~v1_funct_1(k2_funct_1(A_138)) | ~v1_relat_1(k2_funct_1(A_138)) | ~v2_funct_1(A_138) | ~v1_funct_1(A_138) | ~v1_relat_1(A_138))), inference(superposition, [status(thm), theory('equality')], [c_24, c_287])).
% 5.11/1.95  tff(c_964, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', k2_relat_1(k2_funct_1('#skF_3'))))) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_269, c_935])).
% 5.11/1.95  tff(c_981, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', k2_relat_1(k2_funct_1('#skF_3')))))), inference(demodulation, [status(thm), theory('equality')], [c_131, c_68, c_62, c_885, c_142, c_964])).
% 5.11/1.95  tff(c_1010, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', k1_relat_1('#skF_3')))) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_22, c_981])).
% 5.11/1.95  tff(c_1027, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_131, c_68, c_62, c_656, c_1010])).
% 5.11/1.95  tff(c_1029, plain, $false, inference(negUnitSimplification, [status(thm)], [c_241, c_1027])).
% 5.11/1.95  tff(c_1030, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_652])).
% 5.11/1.95  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 5.11/1.95  tff(c_1059, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1030, c_2])).
% 5.11/1.95  tff(c_1061, plain, $false, inference(negUnitSimplification, [status(thm)], [c_189, c_1059])).
% 5.11/1.95  tff(c_1062, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_141])).
% 5.11/1.95  tff(c_1063, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_141])).
% 5.11/1.95  tff(c_1200, plain, (![A_152, B_153, C_154]: (k1_relset_1(A_152, B_153, C_154)=k1_relat_1(C_154) | ~m1_subset_1(C_154, k1_zfmisc_1(k2_zfmisc_1(A_152, B_153))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 5.11/1.95  tff(c_1225, plain, (k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_1063, c_1200])).
% 5.11/1.95  tff(c_1486, plain, (![B_184, C_185, A_186]: (k1_xboole_0=B_184 | v1_funct_2(C_185, A_186, B_184) | k1_relset_1(A_186, B_184, C_185)!=A_186 | ~m1_subset_1(C_185, k1_zfmisc_1(k2_zfmisc_1(A_186, B_184))))), inference(cnfTransformation, [status(thm)], [f_124])).
% 5.11/1.95  tff(c_1495, plain, (k1_xboole_0='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))!='#skF_2'), inference(resolution, [status(thm)], [c_1063, c_1486])).
% 5.11/1.95  tff(c_1514, plain, (k1_xboole_0='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1225, c_1495])).
% 5.11/1.95  tff(c_1515, plain, (k1_xboole_0='#skF_1' | k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_1062, c_1514])).
% 5.11/1.95  tff(c_1523, plain, (k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(splitLeft, [status(thm)], [c_1515])).
% 5.11/1.95  tff(c_1526, plain, (k2_relat_1('#skF_3')!='#skF_2' | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_24, c_1523])).
% 5.11/1.95  tff(c_1529, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_131, c_68, c_62, c_1111, c_1526])).
% 5.11/1.95  tff(c_1530, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_1515])).
% 5.11/1.95  tff(c_1559, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1530, c_2])).
% 5.11/1.95  tff(c_1561, plain, $false, inference(negUnitSimplification, [status(thm)], [c_240, c_1559])).
% 5.11/1.95  tff(c_1563, plain, (v1_xboole_0('#skF_1')), inference(splitRight, [status(thm)], [c_236])).
% 5.11/1.95  tff(c_106, plain, (![B_40, A_41]: (~v1_xboole_0(B_40) | B_40=A_41 | ~v1_xboole_0(A_41))), inference(cnfTransformation, [status(thm)], [f_34])).
% 5.11/1.95  tff(c_109, plain, (![A_41]: (k1_xboole_0=A_41 | ~v1_xboole_0(A_41))), inference(resolution, [status(thm)], [c_2, c_106])).
% 5.11/1.95  tff(c_1579, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_1563, c_109])).
% 5.11/1.95  tff(c_12, plain, (![A_5]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 5.11/1.95  tff(c_40, plain, (![A_32]: (v1_funct_2(k1_xboole_0, A_32, k1_xboole_0) | k1_xboole_0=A_32 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_32, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_124])).
% 5.11/1.95  tff(c_70, plain, (![A_32]: (v1_funct_2(k1_xboole_0, A_32, k1_xboole_0) | k1_xboole_0=A_32)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_40])).
% 5.11/1.95  tff(c_1588, plain, (![A_32]: (v1_funct_2('#skF_1', A_32, '#skF_1') | A_32='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1579, c_1579, c_1579, c_70])).
% 5.11/1.95  tff(c_10, plain, (![B_4]: (k2_zfmisc_1(k1_xboole_0, B_4)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_40])).
% 5.11/1.95  tff(c_1590, plain, (![B_4]: (k2_zfmisc_1('#skF_1', B_4)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1579, c_1579, c_10])).
% 5.11/1.95  tff(c_2279, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_1590, c_64])).
% 5.11/1.95  tff(c_8, plain, (![A_3]: (k2_zfmisc_1(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_40])).
% 5.11/1.95  tff(c_179, plain, (![C_58]: (v1_xboole_0(C_58) | ~m1_subset_1(C_58, k1_zfmisc_1(k1_xboole_0)) | ~v1_xboole_0(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_170])).
% 5.11/1.95  tff(c_186, plain, (![C_58]: (v1_xboole_0(C_58) | ~m1_subset_1(C_58, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_179])).
% 5.11/1.95  tff(c_2348, plain, (![C_274]: (v1_xboole_0(C_274) | ~m1_subset_1(C_274, k1_zfmisc_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_1579, c_186])).
% 5.11/1.95  tff(c_2356, plain, (v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_2279, c_2348])).
% 5.11/1.95  tff(c_4, plain, (![B_2, A_1]: (~v1_xboole_0(B_2) | B_2=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_34])).
% 5.11/1.95  tff(c_1580, plain, (![A_1]: (A_1='#skF_1' | ~v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_1563, c_4])).
% 5.11/1.95  tff(c_2379, plain, ('#skF_3'='#skF_1'), inference(resolution, [status(thm)], [c_2356, c_1580])).
% 5.11/1.95  tff(c_1591, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1579, c_1579, c_8])).
% 5.11/1.95  tff(c_1593, plain, (![A_5]: (m1_subset_1('#skF_1', k1_zfmisc_1(A_5)))), inference(demodulation, [status(thm), theory('equality')], [c_1579, c_12])).
% 5.11/1.95  tff(c_132, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_119])).
% 5.11/1.95  tff(c_1587, plain, (v1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1579, c_132])).
% 5.11/1.95  tff(c_16, plain, (![A_9]: (v1_funct_1(A_9) | ~v1_xboole_0(A_9))), inference(cnfTransformation, [status(thm)], [f_52])).
% 5.11/1.95  tff(c_1581, plain, (v1_funct_1('#skF_1')), inference(resolution, [status(thm)], [c_1563, c_16])).
% 5.11/1.95  tff(c_1648, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_1590, c_64])).
% 5.11/1.95  tff(c_1706, plain, (![C_202]: (v1_xboole_0(C_202) | ~m1_subset_1(C_202, k1_zfmisc_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_1579, c_186])).
% 5.11/1.95  tff(c_1714, plain, (v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_1648, c_1706])).
% 5.11/1.95  tff(c_1589, plain, (![A_41]: (A_41='#skF_1' | ~v1_xboole_0(A_41))), inference(demodulation, [status(thm), theory('equality')], [c_1579, c_109])).
% 5.11/1.95  tff(c_1725, plain, ('#skF_3'='#skF_1'), inference(resolution, [status(thm)], [c_1714, c_1589])).
% 5.11/1.95  tff(c_1738, plain, (v2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1725, c_62])).
% 5.11/1.95  tff(c_1734, plain, (v1_funct_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_1725, c_142])).
% 5.11/1.95  tff(c_1748, plain, (![A_203, B_204, C_205]: (k1_relset_1(A_203, B_204, C_205)=k1_relat_1(C_205) | ~m1_subset_1(C_205, k1_zfmisc_1(k2_zfmisc_1(A_203, B_204))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 5.11/1.95  tff(c_1759, plain, (![A_203, B_204]: (k1_relset_1(A_203, B_204, '#skF_1')=k1_relat_1('#skF_1'))), inference(resolution, [status(thm)], [c_1593, c_1748])).
% 5.11/1.95  tff(c_1737, plain, (v1_funct_2('#skF_1', '#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1725, c_66])).
% 5.11/1.95  tff(c_48, plain, (![B_33, C_34]: (k1_relset_1(k1_xboole_0, B_33, C_34)=k1_xboole_0 | ~v1_funct_2(C_34, k1_xboole_0, B_33) | ~m1_subset_1(C_34, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_33))))), inference(cnfTransformation, [status(thm)], [f_124])).
% 5.11/1.95  tff(c_71, plain, (![B_33, C_34]: (k1_relset_1(k1_xboole_0, B_33, C_34)=k1_xboole_0 | ~v1_funct_2(C_34, k1_xboole_0, B_33) | ~m1_subset_1(C_34, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_48])).
% 5.11/1.95  tff(c_1858, plain, (![B_216, C_217]: (k1_relset_1('#skF_1', B_216, C_217)='#skF_1' | ~v1_funct_2(C_217, '#skF_1', B_216) | ~m1_subset_1(C_217, k1_zfmisc_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_1579, c_1579, c_1579, c_1579, c_71])).
% 5.11/1.95  tff(c_1860, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_1')='#skF_1' | ~m1_subset_1('#skF_1', k1_zfmisc_1('#skF_1'))), inference(resolution, [status(thm)], [c_1737, c_1858])).
% 5.11/1.95  tff(c_1866, plain, (k1_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1593, c_1759, c_1860])).
% 5.11/1.95  tff(c_1773, plain, (![A_208]: (m1_subset_1(A_208, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_208), k2_relat_1(A_208)))) | ~v1_funct_1(A_208) | ~v1_relat_1(A_208))), inference(cnfTransformation, [status(thm)], [f_134])).
% 5.11/1.95  tff(c_28, plain, (![C_18, B_16, A_15]: (v1_xboole_0(C_18) | ~m1_subset_1(C_18, k1_zfmisc_1(k2_zfmisc_1(B_16, A_15))) | ~v1_xboole_0(A_15))), inference(cnfTransformation, [status(thm)], [f_81])).
% 5.11/1.95  tff(c_1926, plain, (![A_227]: (v1_xboole_0(A_227) | ~v1_xboole_0(k2_relat_1(A_227)) | ~v1_funct_1(A_227) | ~v1_relat_1(A_227))), inference(resolution, [status(thm)], [c_1773, c_28])).
% 5.11/1.95  tff(c_2206, plain, (![A_261]: (v1_xboole_0(k2_funct_1(A_261)) | ~v1_xboole_0(k1_relat_1(A_261)) | ~v1_funct_1(k2_funct_1(A_261)) | ~v1_relat_1(k2_funct_1(A_261)) | ~v2_funct_1(A_261) | ~v1_funct_1(A_261) | ~v1_relat_1(A_261))), inference(superposition, [status(thm), theory('equality')], [c_22, c_1926])).
% 5.11/1.95  tff(c_2218, plain, (![A_262]: (k2_funct_1(A_262)='#skF_1' | ~v1_xboole_0(k1_relat_1(A_262)) | ~v1_funct_1(k2_funct_1(A_262)) | ~v1_relat_1(k2_funct_1(A_262)) | ~v2_funct_1(A_262) | ~v1_funct_1(A_262) | ~v1_relat_1(A_262))), inference(resolution, [status(thm)], [c_2206, c_1589])).
% 5.11/1.95  tff(c_2221, plain, (k2_funct_1('#skF_1')='#skF_1' | ~v1_xboole_0('#skF_1') | ~v1_funct_1(k2_funct_1('#skF_1')) | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1866, c_2218])).
% 5.11/1.95  tff(c_2226, plain, (k2_funct_1('#skF_1')='#skF_1' | ~v1_relat_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_1587, c_1581, c_1738, c_1734, c_1563, c_2221])).
% 5.11/1.95  tff(c_2227, plain, (~v1_relat_1(k2_funct_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_2226])).
% 5.11/1.95  tff(c_2242, plain, (~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_20, c_2227])).
% 5.11/1.95  tff(c_2246, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1587, c_1581, c_2242])).
% 5.11/1.95  tff(c_2247, plain, (k2_funct_1('#skF_1')='#skF_1'), inference(splitRight, [status(thm)], [c_2226])).
% 5.11/1.95  tff(c_1600, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitLeft, [status(thm)], [c_141])).
% 5.11/1.95  tff(c_1629, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_1591, c_1600])).
% 5.11/1.95  tff(c_1731, plain, (~m1_subset_1(k2_funct_1('#skF_1'), k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_1725, c_1629])).
% 5.11/1.95  tff(c_2249, plain, (~m1_subset_1('#skF_1', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_2247, c_1731])).
% 5.11/1.95  tff(c_2253, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1593, c_2249])).
% 5.11/1.95  tff(c_2255, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_141])).
% 5.11/1.95  tff(c_2359, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_1591, c_2255])).
% 5.11/1.95  tff(c_1583, plain, (![C_58]: (v1_xboole_0(C_58) | ~m1_subset_1(C_58, k1_zfmisc_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_1579, c_186])).
% 5.11/1.95  tff(c_2368, plain, (v1_xboole_0(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_2359, c_1583])).
% 5.11/1.95  tff(c_2403, plain, (v1_xboole_0(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_2379, c_2368])).
% 5.11/1.95  tff(c_2412, plain, (k2_funct_1('#skF_1')='#skF_1'), inference(resolution, [status(thm)], [c_2403, c_1580])).
% 5.11/1.95  tff(c_2254, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_141])).
% 5.11/1.95  tff(c_2387, plain, (~v1_funct_2(k2_funct_1('#skF_1'), '#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2379, c_2254])).
% 5.11/1.95  tff(c_2474, plain, (~v1_funct_2('#skF_1', '#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2412, c_2387])).
% 5.11/1.95  tff(c_2478, plain, ('#skF_2'='#skF_1'), inference(resolution, [status(thm)], [c_1588, c_2474])).
% 5.11/1.95  tff(c_2482, plain, (~v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2478, c_189])).
% 5.11/1.95  tff(c_2485, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1563, c_2482])).
% 5.11/1.95  tff(c_2486, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_184])).
% 5.11/1.95  tff(c_2496, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_2486, c_109])).
% 5.11/1.95  tff(c_2521, plain, (![A_5]: (m1_subset_1('#skF_3', k1_zfmisc_1(A_5)))), inference(demodulation, [status(thm), theory('equality')], [c_2496, c_12])).
% 5.11/1.95  tff(c_2518, plain, (![B_4]: (k2_zfmisc_1('#skF_3', B_4)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2496, c_2496, c_10])).
% 5.11/1.95  tff(c_2584, plain, (![C_282, A_283, B_284]: (v1_partfun1(C_282, A_283) | ~m1_subset_1(C_282, k1_zfmisc_1(k2_zfmisc_1(A_283, B_284))) | ~v1_xboole_0(A_283))), inference(cnfTransformation, [status(thm)], [f_106])).
% 5.11/1.95  tff(c_2587, plain, (![C_282]: (v1_partfun1(C_282, '#skF_3') | ~m1_subset_1(C_282, k1_zfmisc_1('#skF_3')) | ~v1_xboole_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_2518, c_2584])).
% 5.11/1.95  tff(c_3378, plain, (![C_368]: (v1_partfun1(C_368, '#skF_3') | ~m1_subset_1(C_368, k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_2486, c_2587])).
% 5.11/1.95  tff(c_3383, plain, (v1_partfun1('#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_2521, c_3378])).
% 5.11/1.95  tff(c_3610, plain, (![C_402, A_403, B_404]: (v1_funct_2(C_402, A_403, B_404) | ~v1_partfun1(C_402, A_403) | ~v1_funct_1(C_402) | ~m1_subset_1(C_402, k1_zfmisc_1(k2_zfmisc_1(A_403, B_404))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 5.11/1.95  tff(c_3617, plain, (![A_403, B_404]: (v1_funct_2('#skF_3', A_403, B_404) | ~v1_partfun1('#skF_3', A_403) | ~v1_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_2521, c_3610])).
% 5.11/1.95  tff(c_3628, plain, (![A_405, B_406]: (v1_funct_2('#skF_3', A_405, B_406) | ~v1_partfun1('#skF_3', A_405))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_3617])).
% 5.11/1.95  tff(c_2717, plain, (![A_302, B_303, C_304]: (k1_relset_1(A_302, B_303, C_304)=k1_relat_1(C_304) | ~m1_subset_1(C_304, k1_zfmisc_1(k2_zfmisc_1(A_302, B_303))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 5.11/1.95  tff(c_2732, plain, (![A_302, B_303]: (k1_relset_1(A_302, B_303, '#skF_3')=k1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_2521, c_2717])).
% 5.11/1.95  tff(c_44, plain, (![C_34, B_33]: (v1_funct_2(C_34, k1_xboole_0, B_33) | k1_relset_1(k1_xboole_0, B_33, C_34)!=k1_xboole_0 | ~m1_subset_1(C_34, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_33))))), inference(cnfTransformation, [status(thm)], [f_124])).
% 5.11/1.95  tff(c_72, plain, (![C_34, B_33]: (v1_funct_2(C_34, k1_xboole_0, B_33) | k1_relset_1(k1_xboole_0, B_33, C_34)!=k1_xboole_0 | ~m1_subset_1(C_34, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_44])).
% 5.11/1.95  tff(c_2841, plain, (![C_324, B_325]: (v1_funct_2(C_324, '#skF_3', B_325) | k1_relset_1('#skF_3', B_325, C_324)!='#skF_3' | ~m1_subset_1(C_324, k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_2496, c_2496, c_2496, c_2496, c_72])).
% 5.11/1.95  tff(c_2844, plain, (![B_325]: (v1_funct_2('#skF_3', '#skF_3', B_325) | k1_relset_1('#skF_3', B_325, '#skF_3')!='#skF_3')), inference(resolution, [status(thm)], [c_2521, c_2841])).
% 5.11/1.95  tff(c_2846, plain, (![B_325]: (v1_funct_2('#skF_3', '#skF_3', B_325) | k1_relat_1('#skF_3')!='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2732, c_2844])).
% 5.11/1.95  tff(c_2847, plain, (k1_relat_1('#skF_3')!='#skF_3'), inference(splitLeft, [status(thm)], [c_2846])).
% 5.11/1.95  tff(c_2651, plain, (![C_293]: (v1_partfun1(C_293, '#skF_3') | ~m1_subset_1(C_293, k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_2486, c_2587])).
% 5.11/1.95  tff(c_2656, plain, (v1_partfun1('#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_2521, c_2651])).
% 5.11/1.95  tff(c_2880, plain, (![C_327, A_328, B_329]: (v1_funct_2(C_327, A_328, B_329) | ~v1_partfun1(C_327, A_328) | ~v1_funct_1(C_327) | ~m1_subset_1(C_327, k1_zfmisc_1(k2_zfmisc_1(A_328, B_329))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 5.11/1.95  tff(c_2887, plain, (![A_328, B_329]: (v1_funct_2('#skF_3', A_328, B_329) | ~v1_partfun1('#skF_3', A_328) | ~v1_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_2521, c_2880])).
% 5.11/1.95  tff(c_2897, plain, (![A_328, B_329]: (v1_funct_2('#skF_3', A_328, B_329) | ~v1_partfun1('#skF_3', A_328))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_2887])).
% 5.11/1.95  tff(c_2941, plain, (![B_333, C_334]: (k1_relset_1('#skF_3', B_333, C_334)='#skF_3' | ~v1_funct_2(C_334, '#skF_3', B_333) | ~m1_subset_1(C_334, k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_2496, c_2496, c_2496, c_2496, c_71])).
% 5.11/1.95  tff(c_2944, plain, (![B_329]: (k1_relset_1('#skF_3', B_329, '#skF_3')='#skF_3' | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3')) | ~v1_partfun1('#skF_3', '#skF_3'))), inference(resolution, [status(thm)], [c_2897, c_2941])).
% 5.11/1.95  tff(c_2950, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2656, c_2521, c_2732, c_2944])).
% 5.11/1.95  tff(c_2952, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2847, c_2950])).
% 5.11/1.95  tff(c_2954, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(splitRight, [status(thm)], [c_2846])).
% 5.11/1.95  tff(c_2687, plain, (![A_299]: (m1_subset_1(A_299, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_299), k2_relat_1(A_299)))) | ~v1_funct_1(A_299) | ~v1_relat_1(A_299))), inference(cnfTransformation, [status(thm)], [f_134])).
% 5.11/1.95  tff(c_2709, plain, (![A_300]: (v1_xboole_0(A_300) | ~v1_xboole_0(k2_relat_1(A_300)) | ~v1_funct_1(A_300) | ~v1_relat_1(A_300))), inference(resolution, [status(thm)], [c_2687, c_28])).
% 5.11/1.95  tff(c_3247, plain, (![A_364]: (v1_xboole_0(k2_funct_1(A_364)) | ~v1_xboole_0(k1_relat_1(A_364)) | ~v1_funct_1(k2_funct_1(A_364)) | ~v1_relat_1(k2_funct_1(A_364)) | ~v2_funct_1(A_364) | ~v1_funct_1(A_364) | ~v1_relat_1(A_364))), inference(superposition, [status(thm), theory('equality')], [c_22, c_2709])).
% 5.11/1.95  tff(c_2487, plain, (v1_xboole_0('#skF_2')), inference(splitRight, [status(thm)], [c_184])).
% 5.11/1.95  tff(c_2508, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_2487, c_109])).
% 5.11/1.95  tff(c_2530, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2496, c_2508])).
% 5.11/1.95  tff(c_2509, plain, (![A_1]: (A_1='#skF_2' | ~v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_2487, c_4])).
% 5.11/1.95  tff(c_2543, plain, (![A_1]: (A_1='#skF_3' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_2530, c_2509])).
% 5.11/1.95  tff(c_3259, plain, (![A_365]: (k2_funct_1(A_365)='#skF_3' | ~v1_xboole_0(k1_relat_1(A_365)) | ~v1_funct_1(k2_funct_1(A_365)) | ~v1_relat_1(k2_funct_1(A_365)) | ~v2_funct_1(A_365) | ~v1_funct_1(A_365) | ~v1_relat_1(A_365))), inference(resolution, [status(thm)], [c_3247, c_2543])).
% 5.11/1.95  tff(c_3262, plain, (k2_funct_1('#skF_3')='#skF_3' | ~v1_xboole_0('#skF_3') | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2954, c_3259])).
% 5.11/1.95  tff(c_3267, plain, (k2_funct_1('#skF_3')='#skF_3' | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_131, c_68, c_62, c_142, c_2486, c_3262])).
% 5.11/1.95  tff(c_3280, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_3267])).
% 5.11/1.95  tff(c_3283, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_20, c_3280])).
% 5.11/1.95  tff(c_3287, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_131, c_68, c_3283])).
% 5.11/1.95  tff(c_3288, plain, (k2_funct_1('#skF_3')='#skF_3'), inference(splitRight, [status(thm)], [c_3267])).
% 5.11/1.95  tff(c_2649, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_3', '#skF_1') | ~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2518, c_2530, c_2530, c_141])).
% 5.11/1.95  tff(c_2650, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_2649])).
% 5.11/1.95  tff(c_3290, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_3288, c_2650])).
% 5.11/1.95  tff(c_3294, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2521, c_3290])).
% 5.11/1.95  tff(c_3296, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1('#skF_3'))), inference(splitRight, [status(thm)], [c_2649])).
% 5.11/1.95  tff(c_2620, plain, (![C_58]: (v1_xboole_0(C_58) | ~m1_subset_1(C_58, k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_2496, c_186])).
% 5.11/1.95  tff(c_3307, plain, (v1_xboole_0(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_3296, c_2620])).
% 5.11/1.95  tff(c_3317, plain, (k2_funct_1('#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_3307, c_2543])).
% 5.11/1.95  tff(c_3295, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_2649])).
% 5.11/1.95  tff(c_3324, plain, (~v1_funct_2('#skF_3', '#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3317, c_3295])).
% 5.11/1.95  tff(c_3637, plain, (~v1_partfun1('#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_3628, c_3324])).
% 5.11/1.95  tff(c_3648, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3383, c_3637])).
% 5.11/1.95  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.11/1.95  
% 5.11/1.95  Inference rules
% 5.11/1.95  ----------------------
% 5.11/1.95  #Ref     : 0
% 5.11/1.95  #Sup     : 734
% 5.11/1.95  #Fact    : 0
% 5.11/1.95  #Define  : 0
% 5.11/1.95  #Split   : 21
% 5.11/1.95  #Chain   : 0
% 5.11/1.95  #Close   : 0
% 5.11/1.95  
% 5.11/1.95  Ordering : KBO
% 5.11/1.95  
% 5.11/1.95  Simplification rules
% 5.11/1.95  ----------------------
% 5.11/1.95  #Subsume      : 92
% 5.11/1.95  #Demod        : 931
% 5.11/1.95  #Tautology    : 413
% 5.11/1.95  #SimpNegUnit  : 8
% 5.11/1.95  #BackRed      : 149
% 5.11/1.95  
% 5.11/1.95  #Partial instantiations: 0
% 5.11/1.95  #Strategies tried      : 1
% 5.11/1.95  
% 5.11/1.95  Timing (in seconds)
% 5.11/1.95  ----------------------
% 5.11/1.95  Preprocessing        : 0.36
% 5.11/1.95  Parsing              : 0.20
% 5.11/1.95  CNF conversion       : 0.02
% 5.11/1.95  Main loop            : 0.78
% 5.11/1.95  Inferencing          : 0.29
% 5.11/1.95  Reduction            : 0.26
% 5.11/1.95  Demodulation         : 0.18
% 5.11/1.95  BG Simplification    : 0.03
% 5.11/1.95  Subsumption          : 0.13
% 5.11/1.95  Abstraction          : 0.04
% 5.11/1.95  MUC search           : 0.00
% 5.11/1.95  Cooper               : 0.00
% 5.11/1.95  Total                : 1.21
% 5.11/1.95  Index Insertion      : 0.00
% 5.11/1.95  Index Deletion       : 0.00
% 5.11/1.95  Index Matching       : 0.00
% 5.11/1.95  BG Taut test         : 0.00
%------------------------------------------------------------------------------
