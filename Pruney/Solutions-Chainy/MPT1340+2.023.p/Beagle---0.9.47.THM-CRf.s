%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:32 EST 2020

% Result     : Theorem 13.76s
% Output     : CNFRefutation 13.93s
% Verified   : 
% Statistics : Number of formulae       :  192 (65836 expanded)
%              Number of leaves         :   43 (23259 expanded)
%              Depth                    :   25
%              Number of atoms          :  450 (194055 expanded)
%              Number of equality atoms :  121 (52835 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k2_tops_2 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tops_2,type,(
    k2_tops_2: ( $i * $i * $i ) > $i )).

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

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

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

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(r2_funct_2,type,(
    r2_funct_2: ( $i * $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_194,negated_conjecture,(
    ~ ! [A] :
        ( l1_struct_0(A)
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & l1_struct_0(B) )
           => ! [C] :
                ( ( v1_funct_1(C)
                  & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                  & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
               => ( ( k2_relset_1(u1_struct_0(A),u1_struct_0(B),C) = k2_struct_0(B)
                    & v2_funct_1(C) )
                 => r2_funct_2(u1_struct_0(A),u1_struct_0(B),k2_tops_2(u1_struct_0(B),u1_struct_0(A),k2_tops_2(u1_struct_0(A),u1_struct_0(B),C)),C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_tops_2)).

tff(f_148,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_93,axiom,(
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

tff(f_136,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( v2_funct_1(C)
          & k2_relset_1(A,B,C) = B )
       => ( v1_funct_1(k2_funct_1(C))
          & v1_funct_2(k2_funct_1(C),B,A)
          & m1_subset_1(k2_funct_1(C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).

tff(f_45,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A)
        & v2_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A))
        & v2_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_funct_1)).

tff(f_160,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( k2_relset_1(A,B,C) = B
          & v2_funct_1(C) )
       => k2_tops_2(A,B,C) = k2_funct_1(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_2)).

tff(f_172,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( v1_funct_1(k2_tops_2(A,B,C))
        & v1_funct_2(k2_tops_2(A,B,C),B,A)
        & m1_subset_1(k2_tops_2(A,B,C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_2)).

tff(f_55,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_63,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(k2_funct_1(A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_1)).

tff(f_120,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_funct_2(A,B,C,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_funct_2)).

tff(f_144,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k1_relset_1(A,A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_funct_2)).

tff(f_106,axiom,(
    ! [A,B] :
    ? [C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
      & v1_relat_1(C)
      & v4_relat_1(C,A)
      & v5_relat_1(C,B)
      & v1_funct_1(C)
      & v1_funct_2(C,A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_funct_2)).

tff(c_84,plain,(
    l1_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_89,plain,(
    ! [A_48] :
      ( u1_struct_0(A_48) = k2_struct_0(A_48)
      | ~ l1_struct_0(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_97,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_84,c_89])).

tff(c_80,plain,(
    l1_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_96,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_80,c_89])).

tff(c_74,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_117,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_96,c_74])).

tff(c_18,plain,(
    ! [C_7,A_5,B_6] :
      ( v1_relat_1(C_7)
      | ~ m1_subset_1(C_7,k1_zfmisc_1(k2_zfmisc_1(A_5,B_6))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_121,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_117,c_18])).

tff(c_78,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_70,plain,(
    v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_179,plain,(
    ! [A_62,B_63,C_64] :
      ( k2_relset_1(A_62,B_63,C_64) = k2_relat_1(C_64)
      | ~ m1_subset_1(C_64,k1_zfmisc_1(k2_zfmisc_1(A_62,B_63))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_187,plain,(
    k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_3'),'#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_117,c_179])).

tff(c_72,plain,(
    k2_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4') = k2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_112,plain,(
    k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_3'),'#skF_4') = k2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_96,c_72])).

tff(c_188,plain,(
    k2_struct_0('#skF_3') = k2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_187,c_112])).

tff(c_76,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_98,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_2'),k2_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_76])).

tff(c_108,plain,(
    v1_funct_2('#skF_4',k2_struct_0('#skF_2'),k2_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_98])).

tff(c_195,plain,(
    v1_funct_2('#skF_4',k2_struct_0('#skF_2'),k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_188,c_108])).

tff(c_194,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),k2_relat_1('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_188,c_117])).

tff(c_221,plain,(
    ! [A_65,B_66,C_67] :
      ( k1_relset_1(A_65,B_66,C_67) = k1_relat_1(C_67)
      | ~ m1_subset_1(C_67,k1_zfmisc_1(k2_zfmisc_1(A_65,B_66))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_228,plain,(
    k1_relset_1(k2_struct_0('#skF_2'),k2_relat_1('#skF_4'),'#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_194,c_221])).

tff(c_356,plain,(
    ! [B_84,A_85,C_86] :
      ( k1_xboole_0 = B_84
      | k1_relset_1(A_85,B_84,C_86) = A_85
      | ~ v1_funct_2(C_86,A_85,B_84)
      | ~ m1_subset_1(C_86,k1_zfmisc_1(k2_zfmisc_1(A_85,B_84))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_362,plain,
    ( k2_relat_1('#skF_4') = k1_xboole_0
    | k1_relset_1(k2_struct_0('#skF_2'),k2_relat_1('#skF_4'),'#skF_4') = k2_struct_0('#skF_2')
    | ~ v1_funct_2('#skF_4',k2_struct_0('#skF_2'),k2_relat_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_194,c_356])).

tff(c_370,plain,
    ( k2_relat_1('#skF_4') = k1_xboole_0
    | k2_struct_0('#skF_2') = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_195,c_228,c_362])).

tff(c_398,plain,(
    k2_struct_0('#skF_2') = k1_relat_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_370])).

tff(c_403,plain,(
    v1_funct_2('#skF_4',k1_relat_1('#skF_4'),k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_398,c_195])).

tff(c_193,plain,(
    k2_relset_1(k2_struct_0('#skF_2'),k2_relat_1('#skF_4'),'#skF_4') = k2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_188,c_187])).

tff(c_401,plain,(
    k2_relset_1(k1_relat_1('#skF_4'),k2_relat_1('#skF_4'),'#skF_4') = k2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_398,c_193])).

tff(c_402,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),k2_relat_1('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_398,c_194])).

tff(c_696,plain,(
    ! [C_117,A_118,B_119] :
      ( v1_funct_1(k2_funct_1(C_117))
      | k2_relset_1(A_118,B_119,C_117) != B_119
      | ~ v2_funct_1(C_117)
      | ~ m1_subset_1(C_117,k1_zfmisc_1(k2_zfmisc_1(A_118,B_119)))
      | ~ v1_funct_2(C_117,A_118,B_119)
      | ~ v1_funct_1(C_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_702,plain,
    ( v1_funct_1(k2_funct_1('#skF_4'))
    | k2_relset_1(k1_relat_1('#skF_4'),k2_relat_1('#skF_4'),'#skF_4') != k2_relat_1('#skF_4')
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_2('#skF_4',k1_relat_1('#skF_4'),k2_relat_1('#skF_4'))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_402,c_696])).

tff(c_712,plain,(
    v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_403,c_70,c_401,c_702])).

tff(c_730,plain,(
    ! [C_125,B_126,A_127] :
      ( v1_funct_2(k2_funct_1(C_125),B_126,A_127)
      | k2_relset_1(A_127,B_126,C_125) != B_126
      | ~ v2_funct_1(C_125)
      | ~ m1_subset_1(C_125,k1_zfmisc_1(k2_zfmisc_1(A_127,B_126)))
      | ~ v1_funct_2(C_125,A_127,B_126)
      | ~ v1_funct_1(C_125) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_736,plain,
    ( v1_funct_2(k2_funct_1('#skF_4'),k2_relat_1('#skF_4'),k1_relat_1('#skF_4'))
    | k2_relset_1(k1_relat_1('#skF_4'),k2_relat_1('#skF_4'),'#skF_4') != k2_relat_1('#skF_4')
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_2('#skF_4',k1_relat_1('#skF_4'),k2_relat_1('#skF_4'))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_402,c_730])).

tff(c_746,plain,(
    v1_funct_2(k2_funct_1('#skF_4'),k2_relat_1('#skF_4'),k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_403,c_70,c_401,c_736])).

tff(c_6,plain,(
    ! [A_2] :
      ( v2_funct_1(k2_funct_1(A_2))
      | ~ v2_funct_1(A_2)
      | ~ v1_funct_1(A_2)
      | ~ v1_relat_1(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_758,plain,(
    ! [A_131,B_132,C_133] :
      ( k2_tops_2(A_131,B_132,C_133) = k2_funct_1(C_133)
      | ~ v2_funct_1(C_133)
      | k2_relset_1(A_131,B_132,C_133) != B_132
      | ~ m1_subset_1(C_133,k1_zfmisc_1(k2_zfmisc_1(A_131,B_132)))
      | ~ v1_funct_2(C_133,A_131,B_132)
      | ~ v1_funct_1(C_133) ) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_764,plain,
    ( k2_tops_2(k1_relat_1('#skF_4'),k2_relat_1('#skF_4'),'#skF_4') = k2_funct_1('#skF_4')
    | ~ v2_funct_1('#skF_4')
    | k2_relset_1(k1_relat_1('#skF_4'),k2_relat_1('#skF_4'),'#skF_4') != k2_relat_1('#skF_4')
    | ~ v1_funct_2('#skF_4',k1_relat_1('#skF_4'),k2_relat_1('#skF_4'))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_402,c_758])).

tff(c_774,plain,(
    k2_tops_2(k1_relat_1('#skF_4'),k2_relat_1('#skF_4'),'#skF_4') = k2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_403,c_401,c_70,c_764])).

tff(c_62,plain,(
    ! [A_33,B_34,C_35] :
      ( m1_subset_1(k2_tops_2(A_33,B_34,C_35),k1_zfmisc_1(k2_zfmisc_1(B_34,A_33)))
      | ~ m1_subset_1(C_35,k1_zfmisc_1(k2_zfmisc_1(A_33,B_34)))
      | ~ v1_funct_2(C_35,A_33,B_34)
      | ~ v1_funct_1(C_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_790,plain,
    ( m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_4'),k1_relat_1('#skF_4'))))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),k2_relat_1('#skF_4'))))
    | ~ v1_funct_2('#skF_4',k1_relat_1('#skF_4'),k2_relat_1('#skF_4'))
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_774,c_62])).

tff(c_794,plain,(
    m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_4'),k1_relat_1('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_403,c_402,c_790])).

tff(c_22,plain,(
    ! [A_11,B_12,C_13] :
      ( k2_relset_1(A_11,B_12,C_13) = k2_relat_1(C_13)
      | ~ m1_subset_1(C_13,k1_zfmisc_1(k2_zfmisc_1(A_11,B_12))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_852,plain,(
    k2_relset_1(k2_relat_1('#skF_4'),k1_relat_1('#skF_4'),k2_funct_1('#skF_4')) = k2_relat_1(k2_funct_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_794,c_22])).

tff(c_54,plain,(
    ! [C_26,A_24,B_25] :
      ( v1_funct_1(k2_funct_1(C_26))
      | k2_relset_1(A_24,B_25,C_26) != B_25
      | ~ v2_funct_1(C_26)
      | ~ m1_subset_1(C_26,k1_zfmisc_1(k2_zfmisc_1(A_24,B_25)))
      | ~ v1_funct_2(C_26,A_24,B_25)
      | ~ v1_funct_1(C_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_804,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1('#skF_4')))
    | k2_relset_1(k2_relat_1('#skF_4'),k1_relat_1('#skF_4'),k2_funct_1('#skF_4')) != k1_relat_1('#skF_4')
    | ~ v2_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_funct_2(k2_funct_1('#skF_4'),k2_relat_1('#skF_4'),k1_relat_1('#skF_4'))
    | ~ v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_794,c_54])).

tff(c_836,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1('#skF_4')))
    | k2_relset_1(k2_relat_1('#skF_4'),k1_relat_1('#skF_4'),k2_funct_1('#skF_4')) != k1_relat_1('#skF_4')
    | ~ v2_funct_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_712,c_746,c_804])).

tff(c_953,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1('#skF_4')))
    | k2_relat_1(k2_funct_1('#skF_4')) != k1_relat_1('#skF_4')
    | ~ v2_funct_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_852,c_836])).

tff(c_954,plain,(
    ~ v2_funct_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_953])).

tff(c_957,plain,
    ( ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_6,c_954])).

tff(c_961,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_78,c_70,c_957])).

tff(c_963,plain,(
    v2_funct_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_953])).

tff(c_12,plain,(
    ! [A_3] :
      ( k2_relat_1(k2_funct_1(A_3)) = k1_relat_1(A_3)
      | ~ v2_funct_1(A_3)
      | ~ v1_funct_1(A_3)
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_962,plain,
    ( k2_relat_1(k2_funct_1('#skF_4')) != k1_relat_1('#skF_4')
    | v1_funct_1(k2_funct_1(k2_funct_1('#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_953])).

tff(c_991,plain,(
    k2_relat_1(k2_funct_1('#skF_4')) != k1_relat_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_962])).

tff(c_994,plain,
    ( ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_991])).

tff(c_998,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_78,c_70,c_994])).

tff(c_1000,plain,(
    k2_relat_1(k2_funct_1('#skF_4')) = k1_relat_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_962])).

tff(c_1026,plain,(
    k2_relset_1(k2_relat_1('#skF_4'),k1_relat_1('#skF_4'),k2_funct_1('#skF_4')) = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1000,c_852])).

tff(c_999,plain,(
    v1_funct_1(k2_funct_1(k2_funct_1('#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_962])).

tff(c_52,plain,(
    ! [C_26,B_25,A_24] :
      ( v1_funct_2(k2_funct_1(C_26),B_25,A_24)
      | k2_relset_1(A_24,B_25,C_26) != B_25
      | ~ v2_funct_1(C_26)
      | ~ m1_subset_1(C_26,k1_zfmisc_1(k2_zfmisc_1(A_24,B_25)))
      | ~ v1_funct_2(C_26,A_24,B_25)
      | ~ v1_funct_1(C_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_801,plain,
    ( v1_funct_2(k2_funct_1(k2_funct_1('#skF_4')),k1_relat_1('#skF_4'),k2_relat_1('#skF_4'))
    | k2_relset_1(k2_relat_1('#skF_4'),k1_relat_1('#skF_4'),k2_funct_1('#skF_4')) != k1_relat_1('#skF_4')
    | ~ v2_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_funct_2(k2_funct_1('#skF_4'),k2_relat_1('#skF_4'),k1_relat_1('#skF_4'))
    | ~ v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_794,c_52])).

tff(c_833,plain,
    ( v1_funct_2(k2_funct_1(k2_funct_1('#skF_4')),k1_relat_1('#skF_4'),k2_relat_1('#skF_4'))
    | k2_relset_1(k2_relat_1('#skF_4'),k1_relat_1('#skF_4'),k2_funct_1('#skF_4')) != k1_relat_1('#skF_4')
    | ~ v2_funct_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_712,c_746,c_801])).

tff(c_1105,plain,(
    v1_funct_2(k2_funct_1(k2_funct_1('#skF_4')),k1_relat_1('#skF_4'),k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_963,c_1026,c_833])).

tff(c_16,plain,(
    ! [A_4] :
      ( k2_funct_1(k2_funct_1(A_4)) = A_4
      | ~ v2_funct_1(A_4)
      | ~ v1_funct_1(A_4)
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_50,plain,(
    ! [C_26,B_25,A_24] :
      ( m1_subset_1(k2_funct_1(C_26),k1_zfmisc_1(k2_zfmisc_1(B_25,A_24)))
      | k2_relset_1(A_24,B_25,C_26) != B_25
      | ~ v2_funct_1(C_26)
      | ~ m1_subset_1(C_26,k1_zfmisc_1(k2_zfmisc_1(A_24,B_25)))
      | ~ v1_funct_2(C_26,A_24,B_25)
      | ~ v1_funct_1(C_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_964,plain,(
    ! [A_137,B_138,C_139,D_140] :
      ( r2_funct_2(A_137,B_138,C_139,C_139)
      | ~ m1_subset_1(D_140,k1_zfmisc_1(k2_zfmisc_1(A_137,B_138)))
      | ~ v1_funct_2(D_140,A_137,B_138)
      | ~ v1_funct_1(D_140)
      | ~ m1_subset_1(C_139,k1_zfmisc_1(k2_zfmisc_1(A_137,B_138)))
      | ~ v1_funct_2(C_139,A_137,B_138)
      | ~ v1_funct_1(C_139) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_972,plain,(
    ! [C_139] :
      ( r2_funct_2(k1_relat_1('#skF_4'),k2_relat_1('#skF_4'),C_139,C_139)
      | ~ v1_funct_2('#skF_4',k1_relat_1('#skF_4'),k2_relat_1('#skF_4'))
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(C_139,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),k2_relat_1('#skF_4'))))
      | ~ v1_funct_2(C_139,k1_relat_1('#skF_4'),k2_relat_1('#skF_4'))
      | ~ v1_funct_1(C_139) ) ),
    inference(resolution,[status(thm)],[c_402,c_964])).

tff(c_1001,plain,(
    ! [C_141] :
      ( r2_funct_2(k1_relat_1('#skF_4'),k2_relat_1('#skF_4'),C_141,C_141)
      | ~ m1_subset_1(C_141,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),k2_relat_1('#skF_4'))))
      | ~ v1_funct_2(C_141,k1_relat_1('#skF_4'),k2_relat_1('#skF_4'))
      | ~ v1_funct_1(C_141) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_403,c_972])).

tff(c_1090,plain,(
    ! [C_149] :
      ( r2_funct_2(k1_relat_1('#skF_4'),k2_relat_1('#skF_4'),k2_funct_1(C_149),k2_funct_1(C_149))
      | ~ v1_funct_2(k2_funct_1(C_149),k1_relat_1('#skF_4'),k2_relat_1('#skF_4'))
      | ~ v1_funct_1(k2_funct_1(C_149))
      | k2_relset_1(k2_relat_1('#skF_4'),k1_relat_1('#skF_4'),C_149) != k1_relat_1('#skF_4')
      | ~ v2_funct_1(C_149)
      | ~ m1_subset_1(C_149,k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_4'),k1_relat_1('#skF_4'))))
      | ~ v1_funct_2(C_149,k2_relat_1('#skF_4'),k1_relat_1('#skF_4'))
      | ~ v1_funct_1(C_149) ) ),
    inference(resolution,[status(thm)],[c_50,c_1001])).

tff(c_1205,plain,(
    ! [A_166] :
      ( r2_funct_2(k1_relat_1('#skF_4'),k2_relat_1('#skF_4'),k2_funct_1(k2_funct_1(A_166)),A_166)
      | ~ v1_funct_2(k2_funct_1(k2_funct_1(A_166)),k1_relat_1('#skF_4'),k2_relat_1('#skF_4'))
      | ~ v1_funct_1(k2_funct_1(k2_funct_1(A_166)))
      | k2_relset_1(k2_relat_1('#skF_4'),k1_relat_1('#skF_4'),k2_funct_1(A_166)) != k1_relat_1('#skF_4')
      | ~ v2_funct_1(k2_funct_1(A_166))
      | ~ m1_subset_1(k2_funct_1(A_166),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_4'),k1_relat_1('#skF_4'))))
      | ~ v1_funct_2(k2_funct_1(A_166),k2_relat_1('#skF_4'),k1_relat_1('#skF_4'))
      | ~ v1_funct_1(k2_funct_1(A_166))
      | ~ v2_funct_1(A_166)
      | ~ v1_funct_1(A_166)
      | ~ v1_relat_1(A_166) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_1090])).

tff(c_1210,plain,
    ( r2_funct_2(k1_relat_1('#skF_4'),k2_relat_1('#skF_4'),k2_funct_1(k2_funct_1('#skF_4')),'#skF_4')
    | ~ v1_funct_2(k2_funct_1(k2_funct_1('#skF_4')),k1_relat_1('#skF_4'),k2_relat_1('#skF_4'))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_4')))
    | k2_relset_1(k2_relat_1('#skF_4'),k1_relat_1('#skF_4'),k2_funct_1('#skF_4')) != k1_relat_1('#skF_4')
    | ~ v2_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_funct_2(k2_funct_1('#skF_4'),k2_relat_1('#skF_4'),k1_relat_1('#skF_4'))
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_794,c_1205])).

tff(c_1216,plain,(
    r2_funct_2(k1_relat_1('#skF_4'),k2_relat_1('#skF_4'),k2_funct_1(k2_funct_1('#skF_4')),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_78,c_70,c_712,c_746,c_963,c_1026,c_999,c_1105,c_1210])).

tff(c_60,plain,(
    ! [A_30,B_31,C_32] :
      ( k2_tops_2(A_30,B_31,C_32) = k2_funct_1(C_32)
      | ~ v2_funct_1(C_32)
      | k2_relset_1(A_30,B_31,C_32) != B_31
      | ~ m1_subset_1(C_32,k1_zfmisc_1(k2_zfmisc_1(A_30,B_31)))
      | ~ v1_funct_2(C_32,A_30,B_31)
      | ~ v1_funct_1(C_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_798,plain,
    ( k2_tops_2(k2_relat_1('#skF_4'),k1_relat_1('#skF_4'),k2_funct_1('#skF_4')) = k2_funct_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1(k2_funct_1('#skF_4'))
    | k2_relset_1(k2_relat_1('#skF_4'),k1_relat_1('#skF_4'),k2_funct_1('#skF_4')) != k1_relat_1('#skF_4')
    | ~ v1_funct_2(k2_funct_1('#skF_4'),k2_relat_1('#skF_4'),k1_relat_1('#skF_4'))
    | ~ v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_794,c_60])).

tff(c_830,plain,
    ( k2_tops_2(k2_relat_1('#skF_4'),k1_relat_1('#skF_4'),k2_funct_1('#skF_4')) = k2_funct_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1(k2_funct_1('#skF_4'))
    | k2_relset_1(k2_relat_1('#skF_4'),k1_relat_1('#skF_4'),k2_funct_1('#skF_4')) != k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_712,c_746,c_798])).

tff(c_1253,plain,(
    k2_tops_2(k2_relat_1('#skF_4'),k1_relat_1('#skF_4'),k2_funct_1('#skF_4')) = k2_funct_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1026,c_963,c_830])).

tff(c_196,plain,(
    u1_struct_0('#skF_3') = k2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_188,c_96])).

tff(c_68,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k2_tops_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4')),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_201,plain,(
    ~ r2_funct_2(k2_struct_0('#skF_2'),u1_struct_0('#skF_3'),k2_tops_2(u1_struct_0('#skF_3'),k2_struct_0('#skF_2'),k2_tops_2(k2_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4')),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_97,c_97,c_68])).

tff(c_202,plain,(
    ~ r2_funct_2(k2_struct_0('#skF_2'),k2_relat_1('#skF_4'),k2_tops_2(k2_relat_1('#skF_4'),k2_struct_0('#skF_2'),k2_tops_2(k2_struct_0('#skF_2'),k2_relat_1('#skF_4'),'#skF_4')),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_196,c_196,c_196,c_201])).

tff(c_399,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_4'),k2_relat_1('#skF_4'),k2_tops_2(k2_relat_1('#skF_4'),k1_relat_1('#skF_4'),k2_tops_2(k1_relat_1('#skF_4'),k2_relat_1('#skF_4'),'#skF_4')),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_398,c_398,c_398,c_202])).

tff(c_784,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_4'),k2_relat_1('#skF_4'),k2_tops_2(k2_relat_1('#skF_4'),k1_relat_1('#skF_4'),k2_funct_1('#skF_4')),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_774,c_399])).

tff(c_1256,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_4'),k2_relat_1('#skF_4'),k2_funct_1(k2_funct_1('#skF_4')),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1253,c_784])).

tff(c_1262,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1216,c_1256])).

tff(c_1263,plain,(
    k2_relat_1('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_370])).

tff(c_1288,plain,(
    v1_funct_2('#skF_4',k2_struct_0('#skF_2'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1263,c_195])).

tff(c_1287,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),k1_xboole_0))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1263,c_194])).

tff(c_26,plain,(
    ! [C_16,A_14] :
      ( k1_xboole_0 = C_16
      | ~ v1_funct_2(C_16,A_14,k1_xboole_0)
      | k1_xboole_0 = A_14
      | ~ m1_subset_1(C_16,k1_zfmisc_1(k2_zfmisc_1(A_14,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_1326,plain,
    ( k1_xboole_0 = '#skF_4'
    | ~ v1_funct_2('#skF_4',k2_struct_0('#skF_2'),k1_xboole_0)
    | k2_struct_0('#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1287,c_26])).

tff(c_1487,plain,
    ( k1_xboole_0 = '#skF_4'
    | k2_struct_0('#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1288,c_1326])).

tff(c_1488,plain,(
    k2_struct_0('#skF_2') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_1487])).

tff(c_1264,plain,(
    k2_struct_0('#skF_2') != k1_relat_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_370])).

tff(c_1494,plain,(
    k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1488,c_1264])).

tff(c_1493,plain,(
    v1_funct_2('#skF_4',k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1488,c_1288])).

tff(c_1495,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1488,c_1287])).

tff(c_56,plain,(
    ! [A_27,B_28] :
      ( k1_relset_1(A_27,A_27,B_28) = A_27
      | ~ m1_subset_1(B_28,k1_zfmisc_1(k2_zfmisc_1(A_27,A_27)))
      | ~ v1_funct_2(B_28,A_27,A_27)
      | ~ v1_funct_1(B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_1511,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,'#skF_4') = k1_xboole_0
    | ~ v1_funct_2('#skF_4',k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_1495,c_56])).

tff(c_1541,plain,(
    k1_relset_1(k1_xboole_0,k1_xboole_0,'#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_1493,c_1511])).

tff(c_1285,plain,(
    k1_relset_1(k2_struct_0('#skF_2'),k1_xboole_0,'#skF_4') = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1263,c_228])).

tff(c_1491,plain,(
    k1_relset_1(k1_xboole_0,k1_xboole_0,'#skF_4') = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1488,c_1285])).

tff(c_1587,plain,(
    k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1541,c_1491])).

tff(c_1588,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1494,c_1587])).

tff(c_1589,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1487])).

tff(c_1590,plain,(
    k2_struct_0('#skF_2') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_1487])).

tff(c_1627,plain,(
    k2_struct_0('#skF_2') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1589,c_1590])).

tff(c_1603,plain,(
    v1_funct_2('#skF_4',k2_struct_0('#skF_2'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1589,c_1288])).

tff(c_36,plain,(
    ! [A_17,B_18] : v1_funct_2('#skF_1'(A_17,B_18),A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_46,plain,(
    ! [A_17,B_18] : m1_subset_1('#skF_1'(A_17,B_18),k1_zfmisc_1(k2_zfmisc_1(A_17,B_18))) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_253,plain,(
    ! [C_73,A_74] :
      ( k1_xboole_0 = C_73
      | ~ v1_funct_2(C_73,A_74,k1_xboole_0)
      | k1_xboole_0 = A_74
      | ~ m1_subset_1(C_73,k1_zfmisc_1(k2_zfmisc_1(A_74,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_257,plain,(
    ! [A_17] :
      ( '#skF_1'(A_17,k1_xboole_0) = k1_xboole_0
      | ~ v1_funct_2('#skF_1'(A_17,k1_xboole_0),A_17,k1_xboole_0)
      | k1_xboole_0 = A_17 ) ),
    inference(resolution,[status(thm)],[c_46,c_253])).

tff(c_262,plain,(
    ! [A_75] :
      ( '#skF_1'(A_75,k1_xboole_0) = k1_xboole_0
      | k1_xboole_0 = A_75 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_257])).

tff(c_274,plain,(
    ! [A_75] :
      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_75,k1_xboole_0)))
      | k1_xboole_0 = A_75 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_262,c_46])).

tff(c_1610,plain,(
    ! [A_75] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_75,'#skF_4')))
      | A_75 = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1589,c_1589,c_1589,c_274])).

tff(c_1604,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),'#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1589,c_1287])).

tff(c_2130,plain,(
    ! [A_223,B_224,C_225,D_226] :
      ( r2_funct_2(A_223,B_224,C_225,C_225)
      | ~ m1_subset_1(D_226,k1_zfmisc_1(k2_zfmisc_1(A_223,B_224)))
      | ~ v1_funct_2(D_226,A_223,B_224)
      | ~ v1_funct_1(D_226)
      | ~ m1_subset_1(C_225,k1_zfmisc_1(k2_zfmisc_1(A_223,B_224)))
      | ~ v1_funct_2(C_225,A_223,B_224)
      | ~ v1_funct_1(C_225) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_2140,plain,(
    ! [C_225] :
      ( r2_funct_2(k2_struct_0('#skF_2'),'#skF_4',C_225,C_225)
      | ~ v1_funct_2('#skF_4',k2_struct_0('#skF_2'),'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(C_225,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),'#skF_4')))
      | ~ v1_funct_2(C_225,k2_struct_0('#skF_2'),'#skF_4')
      | ~ v1_funct_1(C_225) ) ),
    inference(resolution,[status(thm)],[c_1604,c_2130])).

tff(c_2246,plain,(
    ! [C_233] :
      ( r2_funct_2(k2_struct_0('#skF_2'),'#skF_4',C_233,C_233)
      | ~ m1_subset_1(C_233,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),'#skF_4')))
      | ~ v1_funct_2(C_233,k2_struct_0('#skF_2'),'#skF_4')
      | ~ v1_funct_1(C_233) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_1603,c_2140])).

tff(c_2252,plain,
    ( r2_funct_2(k2_struct_0('#skF_2'),'#skF_4','#skF_4','#skF_4')
    | ~ v1_funct_2('#skF_4',k2_struct_0('#skF_2'),'#skF_4')
    | ~ v1_funct_1('#skF_4')
    | k2_struct_0('#skF_2') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1610,c_2246])).

tff(c_2264,plain,
    ( r2_funct_2(k2_struct_0('#skF_2'),'#skF_4','#skF_4','#skF_4')
    | k2_struct_0('#skF_2') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_1603,c_2252])).

tff(c_2265,plain,(
    r2_funct_2(k2_struct_0('#skF_2'),'#skF_4','#skF_4','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_1627,c_2264])).

tff(c_1286,plain,(
    k2_relset_1(k2_struct_0('#skF_2'),k1_xboole_0,'#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1263,c_1263,c_193])).

tff(c_1602,plain,(
    k2_relset_1(k2_struct_0('#skF_2'),'#skF_4','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1589,c_1589,c_1286])).

tff(c_1808,plain,(
    ! [C_201,A_202,B_203] :
      ( v1_funct_1(k2_funct_1(C_201))
      | k2_relset_1(A_202,B_203,C_201) != B_203
      | ~ v2_funct_1(C_201)
      | ~ m1_subset_1(C_201,k1_zfmisc_1(k2_zfmisc_1(A_202,B_203)))
      | ~ v1_funct_2(C_201,A_202,B_203)
      | ~ v1_funct_1(C_201) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_1814,plain,
    ( v1_funct_1(k2_funct_1('#skF_4'))
    | k2_relset_1(k2_struct_0('#skF_2'),'#skF_4','#skF_4') != '#skF_4'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_2('#skF_4',k2_struct_0('#skF_2'),'#skF_4')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_1604,c_1808])).

tff(c_1821,plain,(
    v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_1603,c_70,c_1602,c_1814])).

tff(c_1910,plain,(
    ! [C_209,B_210,A_211] :
      ( v1_funct_2(k2_funct_1(C_209),B_210,A_211)
      | k2_relset_1(A_211,B_210,C_209) != B_210
      | ~ v2_funct_1(C_209)
      | ~ m1_subset_1(C_209,k1_zfmisc_1(k2_zfmisc_1(A_211,B_210)))
      | ~ v1_funct_2(C_209,A_211,B_210)
      | ~ v1_funct_1(C_209) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_1919,plain,
    ( v1_funct_2(k2_funct_1('#skF_4'),'#skF_4',k2_struct_0('#skF_2'))
    | k2_relset_1(k2_struct_0('#skF_2'),'#skF_4','#skF_4') != '#skF_4'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_2('#skF_4',k2_struct_0('#skF_2'),'#skF_4')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_1604,c_1910])).

tff(c_1929,plain,(
    v1_funct_2(k2_funct_1('#skF_4'),'#skF_4',k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_1603,c_70,c_1602,c_1919])).

tff(c_1975,plain,(
    ! [A_214,B_215,C_216] :
      ( k2_tops_2(A_214,B_215,C_216) = k2_funct_1(C_216)
      | ~ v2_funct_1(C_216)
      | k2_relset_1(A_214,B_215,C_216) != B_215
      | ~ m1_subset_1(C_216,k1_zfmisc_1(k2_zfmisc_1(A_214,B_215)))
      | ~ v1_funct_2(C_216,A_214,B_215)
      | ~ v1_funct_1(C_216) ) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_1984,plain,
    ( k2_tops_2(k2_struct_0('#skF_2'),'#skF_4','#skF_4') = k2_funct_1('#skF_4')
    | ~ v2_funct_1('#skF_4')
    | k2_relset_1(k2_struct_0('#skF_2'),'#skF_4','#skF_4') != '#skF_4'
    | ~ v1_funct_2('#skF_4',k2_struct_0('#skF_2'),'#skF_4')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_1604,c_1975])).

tff(c_1994,plain,(
    k2_tops_2(k2_struct_0('#skF_2'),'#skF_4','#skF_4') = k2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_1603,c_1602,c_70,c_1984])).

tff(c_2012,plain,
    ( m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_4',k2_struct_0('#skF_2'))))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),'#skF_4')))
    | ~ v1_funct_2('#skF_4',k2_struct_0('#skF_2'),'#skF_4')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1994,c_62])).

tff(c_2020,plain,(
    m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_4',k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_1603,c_1604,c_2012])).

tff(c_64,plain,(
    ! [A_33,B_34,C_35] :
      ( v1_funct_2(k2_tops_2(A_33,B_34,C_35),B_34,A_33)
      | ~ m1_subset_1(C_35,k1_zfmisc_1(k2_zfmisc_1(A_33,B_34)))
      | ~ v1_funct_2(C_35,A_33,B_34)
      | ~ v1_funct_1(C_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_2032,plain,
    ( v1_funct_2(k2_tops_2('#skF_4',k2_struct_0('#skF_2'),k2_funct_1('#skF_4')),k2_struct_0('#skF_2'),'#skF_4')
    | ~ v1_funct_2(k2_funct_1('#skF_4'),'#skF_4',k2_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_2020,c_64])).

tff(c_2056,plain,(
    v1_funct_2(k2_tops_2('#skF_4',k2_struct_0('#skF_2'),k2_funct_1('#skF_4')),k2_struct_0('#skF_2'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1821,c_1929,c_2032])).

tff(c_2157,plain,(
    ! [C_227,A_228] :
      ( C_227 = '#skF_4'
      | ~ v1_funct_2(C_227,A_228,'#skF_4')
      | A_228 = '#skF_4'
      | ~ m1_subset_1(C_227,k1_zfmisc_1(k2_zfmisc_1(A_228,'#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1589,c_1589,c_1589,c_1589,c_26])).

tff(c_18097,plain,(
    ! [B_873,C_874] :
      ( k2_tops_2('#skF_4',B_873,C_874) = '#skF_4'
      | ~ v1_funct_2(k2_tops_2('#skF_4',B_873,C_874),B_873,'#skF_4')
      | B_873 = '#skF_4'
      | ~ m1_subset_1(C_874,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_873)))
      | ~ v1_funct_2(C_874,'#skF_4',B_873)
      | ~ v1_funct_1(C_874) ) ),
    inference(resolution,[status(thm)],[c_62,c_2157])).

tff(c_18124,plain,
    ( k2_tops_2('#skF_4',k2_struct_0('#skF_2'),k2_funct_1('#skF_4')) = '#skF_4'
    | k2_struct_0('#skF_2') = '#skF_4'
    | ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_4',k2_struct_0('#skF_2'))))
    | ~ v1_funct_2(k2_funct_1('#skF_4'),'#skF_4',k2_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_2056,c_18097])).

tff(c_18154,plain,
    ( k2_tops_2('#skF_4',k2_struct_0('#skF_2'),k2_funct_1('#skF_4')) = '#skF_4'
    | k2_struct_0('#skF_2') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1821,c_1929,c_2020,c_18124])).

tff(c_18155,plain,(
    k2_tops_2('#skF_4',k2_struct_0('#skF_2'),k2_funct_1('#skF_4')) = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_1627,c_18154])).

tff(c_1284,plain,(
    ~ r2_funct_2(k2_struct_0('#skF_2'),k1_xboole_0,k2_tops_2(k1_xboole_0,k2_struct_0('#skF_2'),k2_tops_2(k2_struct_0('#skF_2'),k1_xboole_0,'#skF_4')),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1263,c_1263,c_1263,c_202])).

tff(c_1597,plain,(
    ~ r2_funct_2(k2_struct_0('#skF_2'),'#skF_4',k2_tops_2('#skF_4',k2_struct_0('#skF_2'),k2_tops_2(k2_struct_0('#skF_2'),'#skF_4','#skF_4')),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1589,c_1589,c_1589,c_1284])).

tff(c_1999,plain,(
    ~ r2_funct_2(k2_struct_0('#skF_2'),'#skF_4',k2_tops_2('#skF_4',k2_struct_0('#skF_2'),k2_funct_1('#skF_4')),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1994,c_1597])).

tff(c_18175,plain,(
    ~ r2_funct_2(k2_struct_0('#skF_2'),'#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18155,c_1999])).

tff(c_18191,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2265,c_18175])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:20:53 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 13.76/5.72  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.76/5.74  
% 13.76/5.74  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.76/5.74  %$ r2_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k2_tops_2 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 13.76/5.74  
% 13.76/5.74  %Foreground sorts:
% 13.76/5.74  
% 13.76/5.74  
% 13.76/5.74  %Background operators:
% 13.76/5.74  
% 13.76/5.74  
% 13.76/5.74  %Foreground operators:
% 13.76/5.74  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 13.76/5.74  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 13.76/5.74  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 13.76/5.74  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 13.76/5.74  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 13.76/5.74  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 13.76/5.74  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 13.76/5.74  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 13.76/5.74  tff(k2_tops_2, type, k2_tops_2: ($i * $i * $i) > $i).
% 13.76/5.74  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 13.76/5.74  tff('#skF_2', type, '#skF_2': $i).
% 13.76/5.74  tff('#skF_3', type, '#skF_3': $i).
% 13.76/5.74  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 13.76/5.74  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 13.76/5.74  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 13.76/5.74  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 13.76/5.74  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 13.76/5.74  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 13.76/5.74  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 13.76/5.74  tff('#skF_4', type, '#skF_4': $i).
% 13.76/5.74  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 13.76/5.74  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 13.76/5.74  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 13.76/5.74  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 13.76/5.74  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 13.76/5.74  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 13.76/5.74  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 13.76/5.74  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 13.76/5.74  
% 13.93/5.77  tff(f_194, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: ((~v2_struct_0(B) & l1_struct_0(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B)) & v2_funct_1(C)) => r2_funct_2(u1_struct_0(A), u1_struct_0(B), k2_tops_2(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)), C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_tops_2)).
% 13.93/5.77  tff(f_148, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 13.93/5.77  tff(f_67, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 13.93/5.77  tff(f_75, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 13.93/5.77  tff(f_71, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 13.93/5.77  tff(f_93, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 13.93/5.77  tff(f_136, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_funct_2)).
% 13.93/5.77  tff(f_45, axiom, (![A]: (((v1_relat_1(A) & v1_funct_1(A)) & v2_funct_1(A)) => ((v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))) & v2_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_funct_1)).
% 13.93/5.77  tff(f_160, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => (k2_tops_2(A, B, C) = k2_funct_1(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tops_2)).
% 13.93/5.77  tff(f_172, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v1_funct_1(k2_tops_2(A, B, C)) & v1_funct_2(k2_tops_2(A, B, C), B, A)) & m1_subset_1(k2_tops_2(A, B, C), k1_zfmisc_1(k2_zfmisc_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_tops_2)).
% 13.93/5.77  tff(f_55, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 13.93/5.77  tff(f_63, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(k2_funct_1(A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_funct_1)).
% 13.93/5.77  tff(f_120, axiom, (![A, B, C, D]: ((((((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(D)) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_funct_2(A, B, C, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', reflexivity_r2_funct_2)).
% 13.93/5.77  tff(f_144, axiom, (![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k1_relset_1(A, A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_funct_2)).
% 13.93/5.77  tff(f_106, axiom, (![A, B]: (?[C]: (((((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & v1_relat_1(C)) & v4_relat_1(C, A)) & v5_relat_1(C, B)) & v1_funct_1(C)) & v1_funct_2(C, A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc1_funct_2)).
% 13.93/5.77  tff(c_84, plain, (l1_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_194])).
% 13.93/5.77  tff(c_89, plain, (![A_48]: (u1_struct_0(A_48)=k2_struct_0(A_48) | ~l1_struct_0(A_48))), inference(cnfTransformation, [status(thm)], [f_148])).
% 13.93/5.77  tff(c_97, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_84, c_89])).
% 13.93/5.77  tff(c_80, plain, (l1_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_194])).
% 13.93/5.77  tff(c_96, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_80, c_89])).
% 13.93/5.77  tff(c_74, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_194])).
% 13.93/5.77  tff(c_117, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_97, c_96, c_74])).
% 13.93/5.77  tff(c_18, plain, (![C_7, A_5, B_6]: (v1_relat_1(C_7) | ~m1_subset_1(C_7, k1_zfmisc_1(k2_zfmisc_1(A_5, B_6))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 13.93/5.77  tff(c_121, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_117, c_18])).
% 13.93/5.77  tff(c_78, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_194])).
% 13.93/5.77  tff(c_70, plain, (v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_194])).
% 13.93/5.77  tff(c_179, plain, (![A_62, B_63, C_64]: (k2_relset_1(A_62, B_63, C_64)=k2_relat_1(C_64) | ~m1_subset_1(C_64, k1_zfmisc_1(k2_zfmisc_1(A_62, B_63))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 13.93/5.77  tff(c_187, plain, (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_3'), '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_117, c_179])).
% 13.93/5.77  tff(c_72, plain, (k2_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4')=k2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_194])).
% 13.93/5.77  tff(c_112, plain, (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_3'), '#skF_4')=k2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_97, c_96, c_72])).
% 13.93/5.77  tff(c_188, plain, (k2_struct_0('#skF_3')=k2_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_187, c_112])).
% 13.93/5.77  tff(c_76, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_194])).
% 13.93/5.77  tff(c_98, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_2'), k2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_76])).
% 13.93/5.77  tff(c_108, plain, (v1_funct_2('#skF_4', k2_struct_0('#skF_2'), k2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_97, c_98])).
% 13.93/5.77  tff(c_195, plain, (v1_funct_2('#skF_4', k2_struct_0('#skF_2'), k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_188, c_108])).
% 13.93/5.77  tff(c_194, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), k2_relat_1('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_188, c_117])).
% 13.93/5.77  tff(c_221, plain, (![A_65, B_66, C_67]: (k1_relset_1(A_65, B_66, C_67)=k1_relat_1(C_67) | ~m1_subset_1(C_67, k1_zfmisc_1(k2_zfmisc_1(A_65, B_66))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 13.93/5.77  tff(c_228, plain, (k1_relset_1(k2_struct_0('#skF_2'), k2_relat_1('#skF_4'), '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_194, c_221])).
% 13.93/5.77  tff(c_356, plain, (![B_84, A_85, C_86]: (k1_xboole_0=B_84 | k1_relset_1(A_85, B_84, C_86)=A_85 | ~v1_funct_2(C_86, A_85, B_84) | ~m1_subset_1(C_86, k1_zfmisc_1(k2_zfmisc_1(A_85, B_84))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 13.93/5.77  tff(c_362, plain, (k2_relat_1('#skF_4')=k1_xboole_0 | k1_relset_1(k2_struct_0('#skF_2'), k2_relat_1('#skF_4'), '#skF_4')=k2_struct_0('#skF_2') | ~v1_funct_2('#skF_4', k2_struct_0('#skF_2'), k2_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_194, c_356])).
% 13.93/5.77  tff(c_370, plain, (k2_relat_1('#skF_4')=k1_xboole_0 | k2_struct_0('#skF_2')=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_195, c_228, c_362])).
% 13.93/5.77  tff(c_398, plain, (k2_struct_0('#skF_2')=k1_relat_1('#skF_4')), inference(splitLeft, [status(thm)], [c_370])).
% 13.93/5.77  tff(c_403, plain, (v1_funct_2('#skF_4', k1_relat_1('#skF_4'), k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_398, c_195])).
% 13.93/5.77  tff(c_193, plain, (k2_relset_1(k2_struct_0('#skF_2'), k2_relat_1('#skF_4'), '#skF_4')=k2_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_188, c_187])).
% 13.93/5.77  tff(c_401, plain, (k2_relset_1(k1_relat_1('#skF_4'), k2_relat_1('#skF_4'), '#skF_4')=k2_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_398, c_193])).
% 13.93/5.77  tff(c_402, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), k2_relat_1('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_398, c_194])).
% 13.93/5.77  tff(c_696, plain, (![C_117, A_118, B_119]: (v1_funct_1(k2_funct_1(C_117)) | k2_relset_1(A_118, B_119, C_117)!=B_119 | ~v2_funct_1(C_117) | ~m1_subset_1(C_117, k1_zfmisc_1(k2_zfmisc_1(A_118, B_119))) | ~v1_funct_2(C_117, A_118, B_119) | ~v1_funct_1(C_117))), inference(cnfTransformation, [status(thm)], [f_136])).
% 13.93/5.77  tff(c_702, plain, (v1_funct_1(k2_funct_1('#skF_4')) | k2_relset_1(k1_relat_1('#skF_4'), k2_relat_1('#skF_4'), '#skF_4')!=k2_relat_1('#skF_4') | ~v2_funct_1('#skF_4') | ~v1_funct_2('#skF_4', k1_relat_1('#skF_4'), k2_relat_1('#skF_4')) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_402, c_696])).
% 13.93/5.77  tff(c_712, plain, (v1_funct_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_403, c_70, c_401, c_702])).
% 13.93/5.77  tff(c_730, plain, (![C_125, B_126, A_127]: (v1_funct_2(k2_funct_1(C_125), B_126, A_127) | k2_relset_1(A_127, B_126, C_125)!=B_126 | ~v2_funct_1(C_125) | ~m1_subset_1(C_125, k1_zfmisc_1(k2_zfmisc_1(A_127, B_126))) | ~v1_funct_2(C_125, A_127, B_126) | ~v1_funct_1(C_125))), inference(cnfTransformation, [status(thm)], [f_136])).
% 13.93/5.77  tff(c_736, plain, (v1_funct_2(k2_funct_1('#skF_4'), k2_relat_1('#skF_4'), k1_relat_1('#skF_4')) | k2_relset_1(k1_relat_1('#skF_4'), k2_relat_1('#skF_4'), '#skF_4')!=k2_relat_1('#skF_4') | ~v2_funct_1('#skF_4') | ~v1_funct_2('#skF_4', k1_relat_1('#skF_4'), k2_relat_1('#skF_4')) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_402, c_730])).
% 13.93/5.77  tff(c_746, plain, (v1_funct_2(k2_funct_1('#skF_4'), k2_relat_1('#skF_4'), k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_403, c_70, c_401, c_736])).
% 13.93/5.77  tff(c_6, plain, (![A_2]: (v2_funct_1(k2_funct_1(A_2)) | ~v2_funct_1(A_2) | ~v1_funct_1(A_2) | ~v1_relat_1(A_2))), inference(cnfTransformation, [status(thm)], [f_45])).
% 13.93/5.77  tff(c_758, plain, (![A_131, B_132, C_133]: (k2_tops_2(A_131, B_132, C_133)=k2_funct_1(C_133) | ~v2_funct_1(C_133) | k2_relset_1(A_131, B_132, C_133)!=B_132 | ~m1_subset_1(C_133, k1_zfmisc_1(k2_zfmisc_1(A_131, B_132))) | ~v1_funct_2(C_133, A_131, B_132) | ~v1_funct_1(C_133))), inference(cnfTransformation, [status(thm)], [f_160])).
% 13.93/5.77  tff(c_764, plain, (k2_tops_2(k1_relat_1('#skF_4'), k2_relat_1('#skF_4'), '#skF_4')=k2_funct_1('#skF_4') | ~v2_funct_1('#skF_4') | k2_relset_1(k1_relat_1('#skF_4'), k2_relat_1('#skF_4'), '#skF_4')!=k2_relat_1('#skF_4') | ~v1_funct_2('#skF_4', k1_relat_1('#skF_4'), k2_relat_1('#skF_4')) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_402, c_758])).
% 13.93/5.77  tff(c_774, plain, (k2_tops_2(k1_relat_1('#skF_4'), k2_relat_1('#skF_4'), '#skF_4')=k2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_403, c_401, c_70, c_764])).
% 13.93/5.77  tff(c_62, plain, (![A_33, B_34, C_35]: (m1_subset_1(k2_tops_2(A_33, B_34, C_35), k1_zfmisc_1(k2_zfmisc_1(B_34, A_33))) | ~m1_subset_1(C_35, k1_zfmisc_1(k2_zfmisc_1(A_33, B_34))) | ~v1_funct_2(C_35, A_33, B_34) | ~v1_funct_1(C_35))), inference(cnfTransformation, [status(thm)], [f_172])).
% 13.93/5.77  tff(c_790, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_4'), k1_relat_1('#skF_4')))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), k2_relat_1('#skF_4')))) | ~v1_funct_2('#skF_4', k1_relat_1('#skF_4'), k2_relat_1('#skF_4')) | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_774, c_62])).
% 13.93/5.77  tff(c_794, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_4'), k1_relat_1('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_403, c_402, c_790])).
% 13.93/5.77  tff(c_22, plain, (![A_11, B_12, C_13]: (k2_relset_1(A_11, B_12, C_13)=k2_relat_1(C_13) | ~m1_subset_1(C_13, k1_zfmisc_1(k2_zfmisc_1(A_11, B_12))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 13.93/5.77  tff(c_852, plain, (k2_relset_1(k2_relat_1('#skF_4'), k1_relat_1('#skF_4'), k2_funct_1('#skF_4'))=k2_relat_1(k2_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_794, c_22])).
% 13.93/5.77  tff(c_54, plain, (![C_26, A_24, B_25]: (v1_funct_1(k2_funct_1(C_26)) | k2_relset_1(A_24, B_25, C_26)!=B_25 | ~v2_funct_1(C_26) | ~m1_subset_1(C_26, k1_zfmisc_1(k2_zfmisc_1(A_24, B_25))) | ~v1_funct_2(C_26, A_24, B_25) | ~v1_funct_1(C_26))), inference(cnfTransformation, [status(thm)], [f_136])).
% 13.93/5.77  tff(c_804, plain, (v1_funct_1(k2_funct_1(k2_funct_1('#skF_4'))) | k2_relset_1(k2_relat_1('#skF_4'), k1_relat_1('#skF_4'), k2_funct_1('#skF_4'))!=k1_relat_1('#skF_4') | ~v2_funct_1(k2_funct_1('#skF_4')) | ~v1_funct_2(k2_funct_1('#skF_4'), k2_relat_1('#skF_4'), k1_relat_1('#skF_4')) | ~v1_funct_1(k2_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_794, c_54])).
% 13.93/5.77  tff(c_836, plain, (v1_funct_1(k2_funct_1(k2_funct_1('#skF_4'))) | k2_relset_1(k2_relat_1('#skF_4'), k1_relat_1('#skF_4'), k2_funct_1('#skF_4'))!=k1_relat_1('#skF_4') | ~v2_funct_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_712, c_746, c_804])).
% 13.93/5.77  tff(c_953, plain, (v1_funct_1(k2_funct_1(k2_funct_1('#skF_4'))) | k2_relat_1(k2_funct_1('#skF_4'))!=k1_relat_1('#skF_4') | ~v2_funct_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_852, c_836])).
% 13.93/5.77  tff(c_954, plain, (~v2_funct_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_953])).
% 13.93/5.77  tff(c_957, plain, (~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_6, c_954])).
% 13.93/5.77  tff(c_961, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_121, c_78, c_70, c_957])).
% 13.93/5.77  tff(c_963, plain, (v2_funct_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_953])).
% 13.93/5.77  tff(c_12, plain, (![A_3]: (k2_relat_1(k2_funct_1(A_3))=k1_relat_1(A_3) | ~v2_funct_1(A_3) | ~v1_funct_1(A_3) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_55])).
% 13.93/5.77  tff(c_962, plain, (k2_relat_1(k2_funct_1('#skF_4'))!=k1_relat_1('#skF_4') | v1_funct_1(k2_funct_1(k2_funct_1('#skF_4')))), inference(splitRight, [status(thm)], [c_953])).
% 13.93/5.77  tff(c_991, plain, (k2_relat_1(k2_funct_1('#skF_4'))!=k1_relat_1('#skF_4')), inference(splitLeft, [status(thm)], [c_962])).
% 13.93/5.77  tff(c_994, plain, (~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_12, c_991])).
% 13.93/5.77  tff(c_998, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_121, c_78, c_70, c_994])).
% 13.93/5.77  tff(c_1000, plain, (k2_relat_1(k2_funct_1('#skF_4'))=k1_relat_1('#skF_4')), inference(splitRight, [status(thm)], [c_962])).
% 13.93/5.77  tff(c_1026, plain, (k2_relset_1(k2_relat_1('#skF_4'), k1_relat_1('#skF_4'), k2_funct_1('#skF_4'))=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1000, c_852])).
% 13.93/5.77  tff(c_999, plain, (v1_funct_1(k2_funct_1(k2_funct_1('#skF_4')))), inference(splitRight, [status(thm)], [c_962])).
% 13.93/5.77  tff(c_52, plain, (![C_26, B_25, A_24]: (v1_funct_2(k2_funct_1(C_26), B_25, A_24) | k2_relset_1(A_24, B_25, C_26)!=B_25 | ~v2_funct_1(C_26) | ~m1_subset_1(C_26, k1_zfmisc_1(k2_zfmisc_1(A_24, B_25))) | ~v1_funct_2(C_26, A_24, B_25) | ~v1_funct_1(C_26))), inference(cnfTransformation, [status(thm)], [f_136])).
% 13.93/5.77  tff(c_801, plain, (v1_funct_2(k2_funct_1(k2_funct_1('#skF_4')), k1_relat_1('#skF_4'), k2_relat_1('#skF_4')) | k2_relset_1(k2_relat_1('#skF_4'), k1_relat_1('#skF_4'), k2_funct_1('#skF_4'))!=k1_relat_1('#skF_4') | ~v2_funct_1(k2_funct_1('#skF_4')) | ~v1_funct_2(k2_funct_1('#skF_4'), k2_relat_1('#skF_4'), k1_relat_1('#skF_4')) | ~v1_funct_1(k2_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_794, c_52])).
% 13.93/5.77  tff(c_833, plain, (v1_funct_2(k2_funct_1(k2_funct_1('#skF_4')), k1_relat_1('#skF_4'), k2_relat_1('#skF_4')) | k2_relset_1(k2_relat_1('#skF_4'), k1_relat_1('#skF_4'), k2_funct_1('#skF_4'))!=k1_relat_1('#skF_4') | ~v2_funct_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_712, c_746, c_801])).
% 13.93/5.77  tff(c_1105, plain, (v1_funct_2(k2_funct_1(k2_funct_1('#skF_4')), k1_relat_1('#skF_4'), k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_963, c_1026, c_833])).
% 13.93/5.77  tff(c_16, plain, (![A_4]: (k2_funct_1(k2_funct_1(A_4))=A_4 | ~v2_funct_1(A_4) | ~v1_funct_1(A_4) | ~v1_relat_1(A_4))), inference(cnfTransformation, [status(thm)], [f_63])).
% 13.93/5.77  tff(c_50, plain, (![C_26, B_25, A_24]: (m1_subset_1(k2_funct_1(C_26), k1_zfmisc_1(k2_zfmisc_1(B_25, A_24))) | k2_relset_1(A_24, B_25, C_26)!=B_25 | ~v2_funct_1(C_26) | ~m1_subset_1(C_26, k1_zfmisc_1(k2_zfmisc_1(A_24, B_25))) | ~v1_funct_2(C_26, A_24, B_25) | ~v1_funct_1(C_26))), inference(cnfTransformation, [status(thm)], [f_136])).
% 13.93/5.77  tff(c_964, plain, (![A_137, B_138, C_139, D_140]: (r2_funct_2(A_137, B_138, C_139, C_139) | ~m1_subset_1(D_140, k1_zfmisc_1(k2_zfmisc_1(A_137, B_138))) | ~v1_funct_2(D_140, A_137, B_138) | ~v1_funct_1(D_140) | ~m1_subset_1(C_139, k1_zfmisc_1(k2_zfmisc_1(A_137, B_138))) | ~v1_funct_2(C_139, A_137, B_138) | ~v1_funct_1(C_139))), inference(cnfTransformation, [status(thm)], [f_120])).
% 13.93/5.77  tff(c_972, plain, (![C_139]: (r2_funct_2(k1_relat_1('#skF_4'), k2_relat_1('#skF_4'), C_139, C_139) | ~v1_funct_2('#skF_4', k1_relat_1('#skF_4'), k2_relat_1('#skF_4')) | ~v1_funct_1('#skF_4') | ~m1_subset_1(C_139, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), k2_relat_1('#skF_4')))) | ~v1_funct_2(C_139, k1_relat_1('#skF_4'), k2_relat_1('#skF_4')) | ~v1_funct_1(C_139))), inference(resolution, [status(thm)], [c_402, c_964])).
% 13.93/5.77  tff(c_1001, plain, (![C_141]: (r2_funct_2(k1_relat_1('#skF_4'), k2_relat_1('#skF_4'), C_141, C_141) | ~m1_subset_1(C_141, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), k2_relat_1('#skF_4')))) | ~v1_funct_2(C_141, k1_relat_1('#skF_4'), k2_relat_1('#skF_4')) | ~v1_funct_1(C_141))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_403, c_972])).
% 13.93/5.77  tff(c_1090, plain, (![C_149]: (r2_funct_2(k1_relat_1('#skF_4'), k2_relat_1('#skF_4'), k2_funct_1(C_149), k2_funct_1(C_149)) | ~v1_funct_2(k2_funct_1(C_149), k1_relat_1('#skF_4'), k2_relat_1('#skF_4')) | ~v1_funct_1(k2_funct_1(C_149)) | k2_relset_1(k2_relat_1('#skF_4'), k1_relat_1('#skF_4'), C_149)!=k1_relat_1('#skF_4') | ~v2_funct_1(C_149) | ~m1_subset_1(C_149, k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_4'), k1_relat_1('#skF_4')))) | ~v1_funct_2(C_149, k2_relat_1('#skF_4'), k1_relat_1('#skF_4')) | ~v1_funct_1(C_149))), inference(resolution, [status(thm)], [c_50, c_1001])).
% 13.93/5.77  tff(c_1205, plain, (![A_166]: (r2_funct_2(k1_relat_1('#skF_4'), k2_relat_1('#skF_4'), k2_funct_1(k2_funct_1(A_166)), A_166) | ~v1_funct_2(k2_funct_1(k2_funct_1(A_166)), k1_relat_1('#skF_4'), k2_relat_1('#skF_4')) | ~v1_funct_1(k2_funct_1(k2_funct_1(A_166))) | k2_relset_1(k2_relat_1('#skF_4'), k1_relat_1('#skF_4'), k2_funct_1(A_166))!=k1_relat_1('#skF_4') | ~v2_funct_1(k2_funct_1(A_166)) | ~m1_subset_1(k2_funct_1(A_166), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_4'), k1_relat_1('#skF_4')))) | ~v1_funct_2(k2_funct_1(A_166), k2_relat_1('#skF_4'), k1_relat_1('#skF_4')) | ~v1_funct_1(k2_funct_1(A_166)) | ~v2_funct_1(A_166) | ~v1_funct_1(A_166) | ~v1_relat_1(A_166))), inference(superposition, [status(thm), theory('equality')], [c_16, c_1090])).
% 13.93/5.77  tff(c_1210, plain, (r2_funct_2(k1_relat_1('#skF_4'), k2_relat_1('#skF_4'), k2_funct_1(k2_funct_1('#skF_4')), '#skF_4') | ~v1_funct_2(k2_funct_1(k2_funct_1('#skF_4')), k1_relat_1('#skF_4'), k2_relat_1('#skF_4')) | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_4'))) | k2_relset_1(k2_relat_1('#skF_4'), k1_relat_1('#skF_4'), k2_funct_1('#skF_4'))!=k1_relat_1('#skF_4') | ~v2_funct_1(k2_funct_1('#skF_4')) | ~v1_funct_2(k2_funct_1('#skF_4'), k2_relat_1('#skF_4'), k1_relat_1('#skF_4')) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_794, c_1205])).
% 13.93/5.77  tff(c_1216, plain, (r2_funct_2(k1_relat_1('#skF_4'), k2_relat_1('#skF_4'), k2_funct_1(k2_funct_1('#skF_4')), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_121, c_78, c_70, c_712, c_746, c_963, c_1026, c_999, c_1105, c_1210])).
% 13.93/5.77  tff(c_60, plain, (![A_30, B_31, C_32]: (k2_tops_2(A_30, B_31, C_32)=k2_funct_1(C_32) | ~v2_funct_1(C_32) | k2_relset_1(A_30, B_31, C_32)!=B_31 | ~m1_subset_1(C_32, k1_zfmisc_1(k2_zfmisc_1(A_30, B_31))) | ~v1_funct_2(C_32, A_30, B_31) | ~v1_funct_1(C_32))), inference(cnfTransformation, [status(thm)], [f_160])).
% 13.93/5.77  tff(c_798, plain, (k2_tops_2(k2_relat_1('#skF_4'), k1_relat_1('#skF_4'), k2_funct_1('#skF_4'))=k2_funct_1(k2_funct_1('#skF_4')) | ~v2_funct_1(k2_funct_1('#skF_4')) | k2_relset_1(k2_relat_1('#skF_4'), k1_relat_1('#skF_4'), k2_funct_1('#skF_4'))!=k1_relat_1('#skF_4') | ~v1_funct_2(k2_funct_1('#skF_4'), k2_relat_1('#skF_4'), k1_relat_1('#skF_4')) | ~v1_funct_1(k2_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_794, c_60])).
% 13.93/5.77  tff(c_830, plain, (k2_tops_2(k2_relat_1('#skF_4'), k1_relat_1('#skF_4'), k2_funct_1('#skF_4'))=k2_funct_1(k2_funct_1('#skF_4')) | ~v2_funct_1(k2_funct_1('#skF_4')) | k2_relset_1(k2_relat_1('#skF_4'), k1_relat_1('#skF_4'), k2_funct_1('#skF_4'))!=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_712, c_746, c_798])).
% 13.93/5.77  tff(c_1253, plain, (k2_tops_2(k2_relat_1('#skF_4'), k1_relat_1('#skF_4'), k2_funct_1('#skF_4'))=k2_funct_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1026, c_963, c_830])).
% 13.93/5.77  tff(c_196, plain, (u1_struct_0('#skF_3')=k2_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_188, c_96])).
% 13.93/5.77  tff(c_68, plain, (~r2_funct_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), k2_tops_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k2_tops_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4')), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_194])).
% 13.93/5.77  tff(c_201, plain, (~r2_funct_2(k2_struct_0('#skF_2'), u1_struct_0('#skF_3'), k2_tops_2(u1_struct_0('#skF_3'), k2_struct_0('#skF_2'), k2_tops_2(k2_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4')), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_97, c_97, c_97, c_68])).
% 13.93/5.77  tff(c_202, plain, (~r2_funct_2(k2_struct_0('#skF_2'), k2_relat_1('#skF_4'), k2_tops_2(k2_relat_1('#skF_4'), k2_struct_0('#skF_2'), k2_tops_2(k2_struct_0('#skF_2'), k2_relat_1('#skF_4'), '#skF_4')), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_196, c_196, c_196, c_201])).
% 13.93/5.77  tff(c_399, plain, (~r2_funct_2(k1_relat_1('#skF_4'), k2_relat_1('#skF_4'), k2_tops_2(k2_relat_1('#skF_4'), k1_relat_1('#skF_4'), k2_tops_2(k1_relat_1('#skF_4'), k2_relat_1('#skF_4'), '#skF_4')), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_398, c_398, c_398, c_202])).
% 13.93/5.77  tff(c_784, plain, (~r2_funct_2(k1_relat_1('#skF_4'), k2_relat_1('#skF_4'), k2_tops_2(k2_relat_1('#skF_4'), k1_relat_1('#skF_4'), k2_funct_1('#skF_4')), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_774, c_399])).
% 13.93/5.77  tff(c_1256, plain, (~r2_funct_2(k1_relat_1('#skF_4'), k2_relat_1('#skF_4'), k2_funct_1(k2_funct_1('#skF_4')), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1253, c_784])).
% 13.93/5.77  tff(c_1262, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1216, c_1256])).
% 13.93/5.77  tff(c_1263, plain, (k2_relat_1('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_370])).
% 13.93/5.77  tff(c_1288, plain, (v1_funct_2('#skF_4', k2_struct_0('#skF_2'), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1263, c_195])).
% 13.93/5.77  tff(c_1287, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_1263, c_194])).
% 13.93/5.77  tff(c_26, plain, (![C_16, A_14]: (k1_xboole_0=C_16 | ~v1_funct_2(C_16, A_14, k1_xboole_0) | k1_xboole_0=A_14 | ~m1_subset_1(C_16, k1_zfmisc_1(k2_zfmisc_1(A_14, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 13.93/5.77  tff(c_1326, plain, (k1_xboole_0='#skF_4' | ~v1_funct_2('#skF_4', k2_struct_0('#skF_2'), k1_xboole_0) | k2_struct_0('#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_1287, c_26])).
% 13.93/5.77  tff(c_1487, plain, (k1_xboole_0='#skF_4' | k2_struct_0('#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1288, c_1326])).
% 13.93/5.77  tff(c_1488, plain, (k2_struct_0('#skF_2')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_1487])).
% 13.93/5.77  tff(c_1264, plain, (k2_struct_0('#skF_2')!=k1_relat_1('#skF_4')), inference(splitRight, [status(thm)], [c_370])).
% 13.93/5.77  tff(c_1494, plain, (k1_relat_1('#skF_4')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1488, c_1264])).
% 13.93/5.77  tff(c_1493, plain, (v1_funct_2('#skF_4', k1_xboole_0, k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1488, c_1288])).
% 13.93/5.77  tff(c_1495, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_1488, c_1287])).
% 13.93/5.77  tff(c_56, plain, (![A_27, B_28]: (k1_relset_1(A_27, A_27, B_28)=A_27 | ~m1_subset_1(B_28, k1_zfmisc_1(k2_zfmisc_1(A_27, A_27))) | ~v1_funct_2(B_28, A_27, A_27) | ~v1_funct_1(B_28))), inference(cnfTransformation, [status(thm)], [f_144])).
% 13.93/5.77  tff(c_1511, plain, (k1_relset_1(k1_xboole_0, k1_xboole_0, '#skF_4')=k1_xboole_0 | ~v1_funct_2('#skF_4', k1_xboole_0, k1_xboole_0) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_1495, c_56])).
% 13.93/5.77  tff(c_1541, plain, (k1_relset_1(k1_xboole_0, k1_xboole_0, '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_78, c_1493, c_1511])).
% 13.93/5.77  tff(c_1285, plain, (k1_relset_1(k2_struct_0('#skF_2'), k1_xboole_0, '#skF_4')=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1263, c_228])).
% 13.93/5.77  tff(c_1491, plain, (k1_relset_1(k1_xboole_0, k1_xboole_0, '#skF_4')=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1488, c_1285])).
% 13.93/5.77  tff(c_1587, plain, (k1_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1541, c_1491])).
% 13.93/5.77  tff(c_1588, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1494, c_1587])).
% 13.93/5.77  tff(c_1589, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_1487])).
% 13.93/5.77  tff(c_1590, plain, (k2_struct_0('#skF_2')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_1487])).
% 13.93/5.77  tff(c_1627, plain, (k2_struct_0('#skF_2')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1589, c_1590])).
% 13.93/5.77  tff(c_1603, plain, (v1_funct_2('#skF_4', k2_struct_0('#skF_2'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1589, c_1288])).
% 13.93/5.77  tff(c_36, plain, (![A_17, B_18]: (v1_funct_2('#skF_1'(A_17, B_18), A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_106])).
% 13.93/5.77  tff(c_46, plain, (![A_17, B_18]: (m1_subset_1('#skF_1'(A_17, B_18), k1_zfmisc_1(k2_zfmisc_1(A_17, B_18))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 13.93/5.77  tff(c_253, plain, (![C_73, A_74]: (k1_xboole_0=C_73 | ~v1_funct_2(C_73, A_74, k1_xboole_0) | k1_xboole_0=A_74 | ~m1_subset_1(C_73, k1_zfmisc_1(k2_zfmisc_1(A_74, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 13.93/5.77  tff(c_257, plain, (![A_17]: ('#skF_1'(A_17, k1_xboole_0)=k1_xboole_0 | ~v1_funct_2('#skF_1'(A_17, k1_xboole_0), A_17, k1_xboole_0) | k1_xboole_0=A_17)), inference(resolution, [status(thm)], [c_46, c_253])).
% 13.93/5.77  tff(c_262, plain, (![A_75]: ('#skF_1'(A_75, k1_xboole_0)=k1_xboole_0 | k1_xboole_0=A_75)), inference(demodulation, [status(thm), theory('equality')], [c_36, c_257])).
% 13.93/5.77  tff(c_274, plain, (![A_75]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_75, k1_xboole_0))) | k1_xboole_0=A_75)), inference(superposition, [status(thm), theory('equality')], [c_262, c_46])).
% 13.93/5.77  tff(c_1610, plain, (![A_75]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_75, '#skF_4'))) | A_75='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1589, c_1589, c_1589, c_274])).
% 13.93/5.77  tff(c_1604, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_1589, c_1287])).
% 13.93/5.77  tff(c_2130, plain, (![A_223, B_224, C_225, D_226]: (r2_funct_2(A_223, B_224, C_225, C_225) | ~m1_subset_1(D_226, k1_zfmisc_1(k2_zfmisc_1(A_223, B_224))) | ~v1_funct_2(D_226, A_223, B_224) | ~v1_funct_1(D_226) | ~m1_subset_1(C_225, k1_zfmisc_1(k2_zfmisc_1(A_223, B_224))) | ~v1_funct_2(C_225, A_223, B_224) | ~v1_funct_1(C_225))), inference(cnfTransformation, [status(thm)], [f_120])).
% 13.93/5.77  tff(c_2140, plain, (![C_225]: (r2_funct_2(k2_struct_0('#skF_2'), '#skF_4', C_225, C_225) | ~v1_funct_2('#skF_4', k2_struct_0('#skF_2'), '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(C_225, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), '#skF_4'))) | ~v1_funct_2(C_225, k2_struct_0('#skF_2'), '#skF_4') | ~v1_funct_1(C_225))), inference(resolution, [status(thm)], [c_1604, c_2130])).
% 13.93/5.77  tff(c_2246, plain, (![C_233]: (r2_funct_2(k2_struct_0('#skF_2'), '#skF_4', C_233, C_233) | ~m1_subset_1(C_233, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), '#skF_4'))) | ~v1_funct_2(C_233, k2_struct_0('#skF_2'), '#skF_4') | ~v1_funct_1(C_233))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_1603, c_2140])).
% 13.93/5.77  tff(c_2252, plain, (r2_funct_2(k2_struct_0('#skF_2'), '#skF_4', '#skF_4', '#skF_4') | ~v1_funct_2('#skF_4', k2_struct_0('#skF_2'), '#skF_4') | ~v1_funct_1('#skF_4') | k2_struct_0('#skF_2')='#skF_4'), inference(resolution, [status(thm)], [c_1610, c_2246])).
% 13.93/5.77  tff(c_2264, plain, (r2_funct_2(k2_struct_0('#skF_2'), '#skF_4', '#skF_4', '#skF_4') | k2_struct_0('#skF_2')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_78, c_1603, c_2252])).
% 13.93/5.77  tff(c_2265, plain, (r2_funct_2(k2_struct_0('#skF_2'), '#skF_4', '#skF_4', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_1627, c_2264])).
% 13.93/5.77  tff(c_1286, plain, (k2_relset_1(k2_struct_0('#skF_2'), k1_xboole_0, '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1263, c_1263, c_193])).
% 13.93/5.77  tff(c_1602, plain, (k2_relset_1(k2_struct_0('#skF_2'), '#skF_4', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1589, c_1589, c_1286])).
% 13.93/5.77  tff(c_1808, plain, (![C_201, A_202, B_203]: (v1_funct_1(k2_funct_1(C_201)) | k2_relset_1(A_202, B_203, C_201)!=B_203 | ~v2_funct_1(C_201) | ~m1_subset_1(C_201, k1_zfmisc_1(k2_zfmisc_1(A_202, B_203))) | ~v1_funct_2(C_201, A_202, B_203) | ~v1_funct_1(C_201))), inference(cnfTransformation, [status(thm)], [f_136])).
% 13.93/5.77  tff(c_1814, plain, (v1_funct_1(k2_funct_1('#skF_4')) | k2_relset_1(k2_struct_0('#skF_2'), '#skF_4', '#skF_4')!='#skF_4' | ~v2_funct_1('#skF_4') | ~v1_funct_2('#skF_4', k2_struct_0('#skF_2'), '#skF_4') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_1604, c_1808])).
% 13.93/5.77  tff(c_1821, plain, (v1_funct_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_1603, c_70, c_1602, c_1814])).
% 13.93/5.77  tff(c_1910, plain, (![C_209, B_210, A_211]: (v1_funct_2(k2_funct_1(C_209), B_210, A_211) | k2_relset_1(A_211, B_210, C_209)!=B_210 | ~v2_funct_1(C_209) | ~m1_subset_1(C_209, k1_zfmisc_1(k2_zfmisc_1(A_211, B_210))) | ~v1_funct_2(C_209, A_211, B_210) | ~v1_funct_1(C_209))), inference(cnfTransformation, [status(thm)], [f_136])).
% 13.93/5.77  tff(c_1919, plain, (v1_funct_2(k2_funct_1('#skF_4'), '#skF_4', k2_struct_0('#skF_2')) | k2_relset_1(k2_struct_0('#skF_2'), '#skF_4', '#skF_4')!='#skF_4' | ~v2_funct_1('#skF_4') | ~v1_funct_2('#skF_4', k2_struct_0('#skF_2'), '#skF_4') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_1604, c_1910])).
% 13.93/5.77  tff(c_1929, plain, (v1_funct_2(k2_funct_1('#skF_4'), '#skF_4', k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_1603, c_70, c_1602, c_1919])).
% 13.93/5.77  tff(c_1975, plain, (![A_214, B_215, C_216]: (k2_tops_2(A_214, B_215, C_216)=k2_funct_1(C_216) | ~v2_funct_1(C_216) | k2_relset_1(A_214, B_215, C_216)!=B_215 | ~m1_subset_1(C_216, k1_zfmisc_1(k2_zfmisc_1(A_214, B_215))) | ~v1_funct_2(C_216, A_214, B_215) | ~v1_funct_1(C_216))), inference(cnfTransformation, [status(thm)], [f_160])).
% 13.93/5.77  tff(c_1984, plain, (k2_tops_2(k2_struct_0('#skF_2'), '#skF_4', '#skF_4')=k2_funct_1('#skF_4') | ~v2_funct_1('#skF_4') | k2_relset_1(k2_struct_0('#skF_2'), '#skF_4', '#skF_4')!='#skF_4' | ~v1_funct_2('#skF_4', k2_struct_0('#skF_2'), '#skF_4') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_1604, c_1975])).
% 13.93/5.77  tff(c_1994, plain, (k2_tops_2(k2_struct_0('#skF_2'), '#skF_4', '#skF_4')=k2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_1603, c_1602, c_70, c_1984])).
% 13.93/5.77  tff(c_2012, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', k2_struct_0('#skF_2')))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), '#skF_4'))) | ~v1_funct_2('#skF_4', k2_struct_0('#skF_2'), '#skF_4') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1994, c_62])).
% 13.93/5.77  tff(c_2020, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_1603, c_1604, c_2012])).
% 13.93/5.77  tff(c_64, plain, (![A_33, B_34, C_35]: (v1_funct_2(k2_tops_2(A_33, B_34, C_35), B_34, A_33) | ~m1_subset_1(C_35, k1_zfmisc_1(k2_zfmisc_1(A_33, B_34))) | ~v1_funct_2(C_35, A_33, B_34) | ~v1_funct_1(C_35))), inference(cnfTransformation, [status(thm)], [f_172])).
% 13.93/5.77  tff(c_2032, plain, (v1_funct_2(k2_tops_2('#skF_4', k2_struct_0('#skF_2'), k2_funct_1('#skF_4')), k2_struct_0('#skF_2'), '#skF_4') | ~v1_funct_2(k2_funct_1('#skF_4'), '#skF_4', k2_struct_0('#skF_2')) | ~v1_funct_1(k2_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_2020, c_64])).
% 13.93/5.77  tff(c_2056, plain, (v1_funct_2(k2_tops_2('#skF_4', k2_struct_0('#skF_2'), k2_funct_1('#skF_4')), k2_struct_0('#skF_2'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1821, c_1929, c_2032])).
% 13.93/5.77  tff(c_2157, plain, (![C_227, A_228]: (C_227='#skF_4' | ~v1_funct_2(C_227, A_228, '#skF_4') | A_228='#skF_4' | ~m1_subset_1(C_227, k1_zfmisc_1(k2_zfmisc_1(A_228, '#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_1589, c_1589, c_1589, c_1589, c_26])).
% 13.93/5.77  tff(c_18097, plain, (![B_873, C_874]: (k2_tops_2('#skF_4', B_873, C_874)='#skF_4' | ~v1_funct_2(k2_tops_2('#skF_4', B_873, C_874), B_873, '#skF_4') | B_873='#skF_4' | ~m1_subset_1(C_874, k1_zfmisc_1(k2_zfmisc_1('#skF_4', B_873))) | ~v1_funct_2(C_874, '#skF_4', B_873) | ~v1_funct_1(C_874))), inference(resolution, [status(thm)], [c_62, c_2157])).
% 13.93/5.77  tff(c_18124, plain, (k2_tops_2('#skF_4', k2_struct_0('#skF_2'), k2_funct_1('#skF_4'))='#skF_4' | k2_struct_0('#skF_2')='#skF_4' | ~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', k2_struct_0('#skF_2')))) | ~v1_funct_2(k2_funct_1('#skF_4'), '#skF_4', k2_struct_0('#skF_2')) | ~v1_funct_1(k2_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_2056, c_18097])).
% 13.93/5.77  tff(c_18154, plain, (k2_tops_2('#skF_4', k2_struct_0('#skF_2'), k2_funct_1('#skF_4'))='#skF_4' | k2_struct_0('#skF_2')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1821, c_1929, c_2020, c_18124])).
% 13.93/5.77  tff(c_18155, plain, (k2_tops_2('#skF_4', k2_struct_0('#skF_2'), k2_funct_1('#skF_4'))='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_1627, c_18154])).
% 13.93/5.77  tff(c_1284, plain, (~r2_funct_2(k2_struct_0('#skF_2'), k1_xboole_0, k2_tops_2(k1_xboole_0, k2_struct_0('#skF_2'), k2_tops_2(k2_struct_0('#skF_2'), k1_xboole_0, '#skF_4')), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1263, c_1263, c_1263, c_202])).
% 13.93/5.77  tff(c_1597, plain, (~r2_funct_2(k2_struct_0('#skF_2'), '#skF_4', k2_tops_2('#skF_4', k2_struct_0('#skF_2'), k2_tops_2(k2_struct_0('#skF_2'), '#skF_4', '#skF_4')), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1589, c_1589, c_1589, c_1284])).
% 13.93/5.77  tff(c_1999, plain, (~r2_funct_2(k2_struct_0('#skF_2'), '#skF_4', k2_tops_2('#skF_4', k2_struct_0('#skF_2'), k2_funct_1('#skF_4')), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1994, c_1597])).
% 13.93/5.77  tff(c_18175, plain, (~r2_funct_2(k2_struct_0('#skF_2'), '#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_18155, c_1999])).
% 13.93/5.77  tff(c_18191, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2265, c_18175])).
% 13.93/5.77  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.93/5.77  
% 13.93/5.77  Inference rules
% 13.93/5.77  ----------------------
% 13.93/5.77  #Ref     : 0
% 13.93/5.77  #Sup     : 4150
% 13.93/5.77  #Fact    : 0
% 13.93/5.77  #Define  : 0
% 13.93/5.77  #Split   : 19
% 13.93/5.77  #Chain   : 0
% 13.93/5.77  #Close   : 0
% 13.93/5.77  
% 13.93/5.77  Ordering : KBO
% 13.93/5.77  
% 13.93/5.77  Simplification rules
% 13.93/5.77  ----------------------
% 13.93/5.77  #Subsume      : 1490
% 13.93/5.77  #Demod        : 6451
% 13.93/5.77  #Tautology    : 1631
% 13.93/5.77  #SimpNegUnit  : 415
% 13.93/5.77  #BackRed      : 406
% 13.93/5.77  
% 13.93/5.77  #Partial instantiations: 0
% 13.93/5.77  #Strategies tried      : 1
% 13.93/5.77  
% 13.93/5.77  Timing (in seconds)
% 13.93/5.77  ----------------------
% 13.93/5.78  Preprocessing        : 0.38
% 13.93/5.78  Parsing              : 0.20
% 13.93/5.78  CNF conversion       : 0.03
% 13.93/5.78  Main loop            : 4.60
% 13.93/5.78  Inferencing          : 1.44
% 13.93/5.78  Reduction            : 1.70
% 13.93/5.78  Demodulation         : 1.32
% 13.93/5.78  BG Simplification    : 0.11
% 13.93/5.78  Subsumption          : 1.09
% 13.93/5.78  Abstraction          : 0.16
% 13.93/5.78  MUC search           : 0.00
% 13.93/5.78  Cooper               : 0.00
% 13.93/5.78  Total                : 5.04
% 13.93/5.78  Index Insertion      : 0.00
% 13.93/5.78  Index Deletion       : 0.00
% 13.93/5.78  Index Matching       : 0.00
% 13.93/5.78  BG Taut test         : 0.00
%------------------------------------------------------------------------------
