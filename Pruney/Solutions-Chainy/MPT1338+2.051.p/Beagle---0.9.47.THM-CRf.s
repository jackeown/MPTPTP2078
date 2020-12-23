%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:21 EST 2020

% Result     : Theorem 2.90s
% Output     : CNFRefutation 3.13s
% Verified   : 
% Statistics : Number of formulae       :  130 (3655 expanded)
%              Number of leaves         :   36 (1322 expanded)
%              Depth                    :   16
%              Number of atoms          :  229 (11459 expanded)
%              Number of equality atoms :   92 (4350 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k2_tops_2 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_130,negated_conjecture,(
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
                 => ( k1_relset_1(u1_struct_0(B),u1_struct_0(A),k2_tops_2(u1_struct_0(A),u1_struct_0(B),C)) = k2_struct_0(B)
                    & k2_relset_1(u1_struct_0(B),u1_struct_0(A),k2_tops_2(u1_struct_0(A),u1_struct_0(B),C)) = k2_struct_0(A) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_tops_2)).

tff(f_86,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_36,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_66,axiom,(
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

tff(f_82,axiom,(
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

tff(f_106,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( k2_relset_1(A,B,C) = B
          & v2_funct_1(C) )
       => k2_tops_2(A,B,C) = k2_funct_1(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_2)).

tff(f_94,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(k2_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_struct_0)).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_54,plain,(
    l1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_55,plain,(
    ! [A_26] :
      ( u1_struct_0(A_26) = k2_struct_0(A_26)
      | ~ l1_struct_0(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_63,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_54,c_55])).

tff(c_50,plain,(
    l1_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_62,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_55])).

tff(c_44,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_79,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_62,c_44])).

tff(c_80,plain,(
    ! [C_28,A_29,B_30] :
      ( v1_relat_1(C_28)
      | ~ m1_subset_1(C_28,k1_zfmisc_1(k2_zfmisc_1(A_29,B_30))) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_84,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_79,c_80])).

tff(c_48,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_40,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_4,plain,(
    ! [A_1] :
      ( k2_relat_1(k2_funct_1(A_1)) = k1_relat_1(A_1)
      | ~ v2_funct_1(A_1)
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_364,plain,(
    ! [A_71,B_72,C_73] :
      ( k2_relset_1(A_71,B_72,C_73) = k2_relat_1(C_73)
      | ~ m1_subset_1(C_73,k1_zfmisc_1(k2_zfmisc_1(A_71,B_72))) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_368,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_79,c_364])).

tff(c_42,plain,(
    k2_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_74,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_62,c_42])).

tff(c_369,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_368,c_74])).

tff(c_46,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_72,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_62,c_46])).

tff(c_377,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_369,c_72])).

tff(c_103,plain,(
    ! [A_33,B_34,C_35] :
      ( k1_relset_1(A_33,B_34,C_35) = k1_relat_1(C_35)
      | ~ m1_subset_1(C_35,k1_zfmisc_1(k2_zfmisc_1(A_33,B_34))) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_107,plain,(
    k1_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_79,c_103])).

tff(c_375,plain,(
    k1_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_369,c_107])).

tff(c_376,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_369,c_79])).

tff(c_431,plain,(
    ! [B_83,A_84,C_85] :
      ( k1_xboole_0 = B_83
      | k1_relset_1(A_84,B_83,C_85) = A_84
      | ~ v1_funct_2(C_85,A_84,B_83)
      | ~ m1_subset_1(C_85,k1_zfmisc_1(k2_zfmisc_1(A_84,B_83))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_434,plain,
    ( k2_relat_1('#skF_3') = k1_xboole_0
    | k1_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') = k2_struct_0('#skF_1')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_376,c_431])).

tff(c_437,plain,
    ( k2_relat_1('#skF_3') = k1_xboole_0
    | k2_struct_0('#skF_1') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_377,c_375,c_434])).

tff(c_438,plain,(
    k2_struct_0('#skF_1') = k1_relat_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_437])).

tff(c_444,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_438,c_377])).

tff(c_374,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_369,c_368])).

tff(c_441,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_438,c_374])).

tff(c_443,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_438,c_376])).

tff(c_530,plain,(
    ! [C_95,B_96,A_97] :
      ( m1_subset_1(k2_funct_1(C_95),k1_zfmisc_1(k2_zfmisc_1(B_96,A_97)))
      | k2_relset_1(A_97,B_96,C_95) != B_96
      | ~ v2_funct_1(C_95)
      | ~ m1_subset_1(C_95,k1_zfmisc_1(k2_zfmisc_1(A_97,B_96)))
      | ~ v1_funct_2(C_95,A_97,B_96)
      | ~ v1_funct_1(C_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_12,plain,(
    ! [A_8,B_9,C_10] :
      ( k2_relset_1(A_8,B_9,C_10) = k2_relat_1(C_10)
      | ~ m1_subset_1(C_10,k1_zfmisc_1(k2_zfmisc_1(A_8,B_9))) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_616,plain,(
    ! [B_104,A_105,C_106] :
      ( k2_relset_1(B_104,A_105,k2_funct_1(C_106)) = k2_relat_1(k2_funct_1(C_106))
      | k2_relset_1(A_105,B_104,C_106) != B_104
      | ~ v2_funct_1(C_106)
      | ~ m1_subset_1(C_106,k1_zfmisc_1(k2_zfmisc_1(A_105,B_104)))
      | ~ v1_funct_2(C_106,A_105,B_104)
      | ~ v1_funct_1(C_106) ) ),
    inference(resolution,[status(thm)],[c_530,c_12])).

tff(c_622,plain,
    ( k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_443,c_616])).

tff(c_626,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_444,c_40,c_441,c_622])).

tff(c_513,plain,(
    ! [A_92,B_93,C_94] :
      ( k2_tops_2(A_92,B_93,C_94) = k2_funct_1(C_94)
      | ~ v2_funct_1(C_94)
      | k2_relset_1(A_92,B_93,C_94) != B_93
      | ~ m1_subset_1(C_94,k1_zfmisc_1(k2_zfmisc_1(A_92,B_93)))
      | ~ v1_funct_2(C_94,A_92,B_93)
      | ~ v1_funct_1(C_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_516,plain,
    ( k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_443,c_513])).

tff(c_519,plain,(
    k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_444,c_441,c_40,c_516])).

tff(c_6,plain,(
    ! [A_1] :
      ( k1_relat_1(k2_funct_1(A_1)) = k2_relat_1(A_1)
      | ~ v2_funct_1(A_1)
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_115,plain,(
    ! [A_37,B_38,C_39] :
      ( k2_relset_1(A_37,B_38,C_39) = k2_relat_1(C_39)
      | ~ m1_subset_1(C_39,k1_zfmisc_1(k2_zfmisc_1(A_37,B_38))) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_119,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_79,c_115])).

tff(c_120,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_74])).

tff(c_128,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_72])).

tff(c_126,plain,(
    k1_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_107])).

tff(c_127,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_79])).

tff(c_177,plain,(
    ! [B_49,A_50,C_51] :
      ( k1_xboole_0 = B_49
      | k1_relset_1(A_50,B_49,C_51) = A_50
      | ~ v1_funct_2(C_51,A_50,B_49)
      | ~ m1_subset_1(C_51,k1_zfmisc_1(k2_zfmisc_1(A_50,B_49))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_180,plain,
    ( k2_relat_1('#skF_3') = k1_xboole_0
    | k1_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') = k2_struct_0('#skF_1')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_127,c_177])).

tff(c_183,plain,
    ( k2_relat_1('#skF_3') = k1_xboole_0
    | k2_struct_0('#skF_1') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_126,c_180])).

tff(c_184,plain,(
    k2_struct_0('#skF_1') = k1_relat_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_183])).

tff(c_189,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_184,c_128])).

tff(c_125,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_119])).

tff(c_188,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_184,c_125])).

tff(c_187,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_184,c_127])).

tff(c_261,plain,(
    ! [C_61,B_62,A_63] :
      ( m1_subset_1(k2_funct_1(C_61),k1_zfmisc_1(k2_zfmisc_1(B_62,A_63)))
      | k2_relset_1(A_63,B_62,C_61) != B_62
      | ~ v2_funct_1(C_61)
      | ~ m1_subset_1(C_61,k1_zfmisc_1(k2_zfmisc_1(A_63,B_62)))
      | ~ v1_funct_2(C_61,A_63,B_62)
      | ~ v1_funct_1(C_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_10,plain,(
    ! [A_5,B_6,C_7] :
      ( k1_relset_1(A_5,B_6,C_7) = k1_relat_1(C_7)
      | ~ m1_subset_1(C_7,k1_zfmisc_1(k2_zfmisc_1(A_5,B_6))) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_325,plain,(
    ! [B_67,A_68,C_69] :
      ( k1_relset_1(B_67,A_68,k2_funct_1(C_69)) = k1_relat_1(k2_funct_1(C_69))
      | k2_relset_1(A_68,B_67,C_69) != B_67
      | ~ v2_funct_1(C_69)
      | ~ m1_subset_1(C_69,k1_zfmisc_1(k2_zfmisc_1(A_68,B_67)))
      | ~ v1_funct_2(C_69,A_68,B_67)
      | ~ v1_funct_1(C_69) ) ),
    inference(resolution,[status(thm)],[c_261,c_10])).

tff(c_331,plain,
    ( k1_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_187,c_325])).

tff(c_335,plain,(
    k1_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_189,c_40,c_188,c_331])).

tff(c_254,plain,(
    ! [A_58,B_59,C_60] :
      ( k2_tops_2(A_58,B_59,C_60) = k2_funct_1(C_60)
      | ~ v2_funct_1(C_60)
      | k2_relset_1(A_58,B_59,C_60) != B_59
      | ~ m1_subset_1(C_60,k1_zfmisc_1(k2_zfmisc_1(A_58,B_59)))
      | ~ v1_funct_2(C_60,A_58,B_59)
      | ~ v1_funct_1(C_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_257,plain,
    ( k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_187,c_254])).

tff(c_260,plain,(
    k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_189,c_188,c_40,c_257])).

tff(c_38,plain,
    ( k2_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_1')
    | k1_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_112,plain,
    ( k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_1')
    | k1_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_63,c_62,c_62,c_63,c_63,c_62,c_62,c_38])).

tff(c_113,plain,(
    k1_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_112])).

tff(c_168,plain,(
    k1_relset_1(k2_relat_1('#skF_3'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_120,c_120,c_113])).

tff(c_185,plain,(
    k1_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_184,c_184,c_168])).

tff(c_309,plain,(
    k1_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_260,c_185])).

tff(c_336,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_335,c_309])).

tff(c_343,plain,
    ( ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_336])).

tff(c_347,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_48,c_40,c_343])).

tff(c_348,plain,(
    k2_relat_1('#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_183])).

tff(c_52,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_34,plain,(
    ! [A_18] :
      ( ~ v1_xboole_0(k2_struct_0(A_18))
      | ~ l1_struct_0(A_18)
      | v2_struct_0(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_133,plain,
    ( ~ v1_xboole_0(k2_relat_1('#skF_3'))
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_120,c_34])).

tff(c_137,plain,
    ( ~ v1_xboole_0(k2_relat_1('#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_133])).

tff(c_138,plain,(
    ~ v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_137])).

tff(c_356,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_348,c_138])).

tff(c_360,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_356])).

tff(c_361,plain,(
    k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_112])).

tff(c_422,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3')) != k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_369,c_369,c_361])).

tff(c_439,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_438,c_438,c_438,c_422])).

tff(c_521,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_519,c_439])).

tff(c_627,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_626,c_521])).

tff(c_634,plain,
    ( ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_627])).

tff(c_638,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_48,c_40,c_634])).

tff(c_639,plain,(
    k2_relat_1('#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_437])).

tff(c_382,plain,
    ( ~ v1_xboole_0(k2_relat_1('#skF_3'))
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_369,c_34])).

tff(c_386,plain,
    ( ~ v1_xboole_0(k2_relat_1('#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_382])).

tff(c_387,plain,(
    ~ v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_386])).

tff(c_648,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_639,c_387])).

tff(c_652,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_648])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:17:51 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.90/1.39  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.90/1.40  
% 2.90/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.90/1.40  %$ v1_funct_2 > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k2_tops_2 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.90/1.40  
% 2.90/1.40  %Foreground sorts:
% 2.90/1.40  
% 2.90/1.40  
% 2.90/1.40  %Background operators:
% 2.90/1.40  
% 2.90/1.40  
% 2.90/1.40  %Foreground operators:
% 2.90/1.40  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.90/1.40  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.90/1.40  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.90/1.40  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 2.90/1.40  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 2.90/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.90/1.40  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.90/1.40  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.90/1.40  tff(k2_tops_2, type, k2_tops_2: ($i * $i * $i) > $i).
% 2.90/1.40  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.90/1.40  tff('#skF_2', type, '#skF_2': $i).
% 2.90/1.40  tff('#skF_3', type, '#skF_3': $i).
% 2.90/1.40  tff('#skF_1', type, '#skF_1': $i).
% 2.90/1.40  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.90/1.40  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.90/1.40  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.90/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.90/1.40  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.90/1.40  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.90/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.90/1.40  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.90/1.40  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.90/1.40  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.90/1.40  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.90/1.40  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.90/1.40  
% 3.13/1.42  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.13/1.42  tff(f_130, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: ((~v2_struct_0(B) & l1_struct_0(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B)) & v2_funct_1(C)) => ((k1_relset_1(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)) = k2_struct_0(B)) & (k2_relset_1(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)) = k2_struct_0(A)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_tops_2)).
% 3.13/1.42  tff(f_86, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 3.13/1.42  tff(f_40, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.13/1.42  tff(f_36, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 3.13/1.42  tff(f_48, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.13/1.42  tff(f_44, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.13/1.42  tff(f_66, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 3.13/1.42  tff(f_82, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_funct_2)).
% 3.13/1.42  tff(f_106, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => (k2_tops_2(A, B, C) = k2_funct_1(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tops_2)).
% 3.13/1.42  tff(f_94, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(k2_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc5_struct_0)).
% 3.13/1.42  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 3.13/1.42  tff(c_54, plain, (l1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_130])).
% 3.13/1.42  tff(c_55, plain, (![A_26]: (u1_struct_0(A_26)=k2_struct_0(A_26) | ~l1_struct_0(A_26))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.13/1.42  tff(c_63, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_54, c_55])).
% 3.13/1.42  tff(c_50, plain, (l1_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_130])).
% 3.13/1.42  tff(c_62, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_50, c_55])).
% 3.13/1.42  tff(c_44, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_130])).
% 3.13/1.42  tff(c_79, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_63, c_62, c_44])).
% 3.13/1.42  tff(c_80, plain, (![C_28, A_29, B_30]: (v1_relat_1(C_28) | ~m1_subset_1(C_28, k1_zfmisc_1(k2_zfmisc_1(A_29, B_30))))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.13/1.42  tff(c_84, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_79, c_80])).
% 3.13/1.42  tff(c_48, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_130])).
% 3.13/1.42  tff(c_40, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_130])).
% 3.13/1.42  tff(c_4, plain, (![A_1]: (k2_relat_1(k2_funct_1(A_1))=k1_relat_1(A_1) | ~v2_funct_1(A_1) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.13/1.42  tff(c_364, plain, (![A_71, B_72, C_73]: (k2_relset_1(A_71, B_72, C_73)=k2_relat_1(C_73) | ~m1_subset_1(C_73, k1_zfmisc_1(k2_zfmisc_1(A_71, B_72))))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.13/1.42  tff(c_368, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_79, c_364])).
% 3.13/1.42  tff(c_42, plain, (k2_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_130])).
% 3.13/1.42  tff(c_74, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_63, c_62, c_42])).
% 3.13/1.42  tff(c_369, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_368, c_74])).
% 3.13/1.42  tff(c_46, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_130])).
% 3.13/1.42  tff(c_72, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_63, c_62, c_46])).
% 3.13/1.42  tff(c_377, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_369, c_72])).
% 3.13/1.42  tff(c_103, plain, (![A_33, B_34, C_35]: (k1_relset_1(A_33, B_34, C_35)=k1_relat_1(C_35) | ~m1_subset_1(C_35, k1_zfmisc_1(k2_zfmisc_1(A_33, B_34))))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.13/1.42  tff(c_107, plain, (k1_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_79, c_103])).
% 3.13/1.42  tff(c_375, plain, (k1_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_369, c_107])).
% 3.13/1.42  tff(c_376, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_369, c_79])).
% 3.13/1.42  tff(c_431, plain, (![B_83, A_84, C_85]: (k1_xboole_0=B_83 | k1_relset_1(A_84, B_83, C_85)=A_84 | ~v1_funct_2(C_85, A_84, B_83) | ~m1_subset_1(C_85, k1_zfmisc_1(k2_zfmisc_1(A_84, B_83))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.13/1.42  tff(c_434, plain, (k2_relat_1('#skF_3')=k1_xboole_0 | k1_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')=k2_struct_0('#skF_1') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_376, c_431])).
% 3.13/1.42  tff(c_437, plain, (k2_relat_1('#skF_3')=k1_xboole_0 | k2_struct_0('#skF_1')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_377, c_375, c_434])).
% 3.13/1.42  tff(c_438, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3')), inference(splitLeft, [status(thm)], [c_437])).
% 3.13/1.42  tff(c_444, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_438, c_377])).
% 3.13/1.42  tff(c_374, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_369, c_368])).
% 3.13/1.42  tff(c_441, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_438, c_374])).
% 3.13/1.42  tff(c_443, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_438, c_376])).
% 3.13/1.42  tff(c_530, plain, (![C_95, B_96, A_97]: (m1_subset_1(k2_funct_1(C_95), k1_zfmisc_1(k2_zfmisc_1(B_96, A_97))) | k2_relset_1(A_97, B_96, C_95)!=B_96 | ~v2_funct_1(C_95) | ~m1_subset_1(C_95, k1_zfmisc_1(k2_zfmisc_1(A_97, B_96))) | ~v1_funct_2(C_95, A_97, B_96) | ~v1_funct_1(C_95))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.13/1.42  tff(c_12, plain, (![A_8, B_9, C_10]: (k2_relset_1(A_8, B_9, C_10)=k2_relat_1(C_10) | ~m1_subset_1(C_10, k1_zfmisc_1(k2_zfmisc_1(A_8, B_9))))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.13/1.42  tff(c_616, plain, (![B_104, A_105, C_106]: (k2_relset_1(B_104, A_105, k2_funct_1(C_106))=k2_relat_1(k2_funct_1(C_106)) | k2_relset_1(A_105, B_104, C_106)!=B_104 | ~v2_funct_1(C_106) | ~m1_subset_1(C_106, k1_zfmisc_1(k2_zfmisc_1(A_105, B_104))) | ~v1_funct_2(C_106, A_105, B_104) | ~v1_funct_1(C_106))), inference(resolution, [status(thm)], [c_530, c_12])).
% 3.13/1.42  tff(c_622, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_443, c_616])).
% 3.13/1.42  tff(c_626, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_444, c_40, c_441, c_622])).
% 3.13/1.42  tff(c_513, plain, (![A_92, B_93, C_94]: (k2_tops_2(A_92, B_93, C_94)=k2_funct_1(C_94) | ~v2_funct_1(C_94) | k2_relset_1(A_92, B_93, C_94)!=B_93 | ~m1_subset_1(C_94, k1_zfmisc_1(k2_zfmisc_1(A_92, B_93))) | ~v1_funct_2(C_94, A_92, B_93) | ~v1_funct_1(C_94))), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.13/1.42  tff(c_516, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_443, c_513])).
% 3.13/1.42  tff(c_519, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_444, c_441, c_40, c_516])).
% 3.13/1.42  tff(c_6, plain, (![A_1]: (k1_relat_1(k2_funct_1(A_1))=k2_relat_1(A_1) | ~v2_funct_1(A_1) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.13/1.42  tff(c_115, plain, (![A_37, B_38, C_39]: (k2_relset_1(A_37, B_38, C_39)=k2_relat_1(C_39) | ~m1_subset_1(C_39, k1_zfmisc_1(k2_zfmisc_1(A_37, B_38))))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.13/1.42  tff(c_119, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_79, c_115])).
% 3.13/1.42  tff(c_120, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_119, c_74])).
% 3.13/1.42  tff(c_128, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_120, c_72])).
% 3.13/1.42  tff(c_126, plain, (k1_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_120, c_107])).
% 3.13/1.42  tff(c_127, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_120, c_79])).
% 3.13/1.42  tff(c_177, plain, (![B_49, A_50, C_51]: (k1_xboole_0=B_49 | k1_relset_1(A_50, B_49, C_51)=A_50 | ~v1_funct_2(C_51, A_50, B_49) | ~m1_subset_1(C_51, k1_zfmisc_1(k2_zfmisc_1(A_50, B_49))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.13/1.42  tff(c_180, plain, (k2_relat_1('#skF_3')=k1_xboole_0 | k1_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')=k2_struct_0('#skF_1') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_127, c_177])).
% 3.13/1.42  tff(c_183, plain, (k2_relat_1('#skF_3')=k1_xboole_0 | k2_struct_0('#skF_1')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_128, c_126, c_180])).
% 3.13/1.42  tff(c_184, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3')), inference(splitLeft, [status(thm)], [c_183])).
% 3.13/1.42  tff(c_189, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_184, c_128])).
% 3.13/1.42  tff(c_125, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_120, c_119])).
% 3.13/1.42  tff(c_188, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_184, c_125])).
% 3.13/1.42  tff(c_187, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_184, c_127])).
% 3.13/1.42  tff(c_261, plain, (![C_61, B_62, A_63]: (m1_subset_1(k2_funct_1(C_61), k1_zfmisc_1(k2_zfmisc_1(B_62, A_63))) | k2_relset_1(A_63, B_62, C_61)!=B_62 | ~v2_funct_1(C_61) | ~m1_subset_1(C_61, k1_zfmisc_1(k2_zfmisc_1(A_63, B_62))) | ~v1_funct_2(C_61, A_63, B_62) | ~v1_funct_1(C_61))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.13/1.42  tff(c_10, plain, (![A_5, B_6, C_7]: (k1_relset_1(A_5, B_6, C_7)=k1_relat_1(C_7) | ~m1_subset_1(C_7, k1_zfmisc_1(k2_zfmisc_1(A_5, B_6))))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.13/1.42  tff(c_325, plain, (![B_67, A_68, C_69]: (k1_relset_1(B_67, A_68, k2_funct_1(C_69))=k1_relat_1(k2_funct_1(C_69)) | k2_relset_1(A_68, B_67, C_69)!=B_67 | ~v2_funct_1(C_69) | ~m1_subset_1(C_69, k1_zfmisc_1(k2_zfmisc_1(A_68, B_67))) | ~v1_funct_2(C_69, A_68, B_67) | ~v1_funct_1(C_69))), inference(resolution, [status(thm)], [c_261, c_10])).
% 3.13/1.42  tff(c_331, plain, (k1_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_187, c_325])).
% 3.13/1.42  tff(c_335, plain, (k1_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_189, c_40, c_188, c_331])).
% 3.13/1.42  tff(c_254, plain, (![A_58, B_59, C_60]: (k2_tops_2(A_58, B_59, C_60)=k2_funct_1(C_60) | ~v2_funct_1(C_60) | k2_relset_1(A_58, B_59, C_60)!=B_59 | ~m1_subset_1(C_60, k1_zfmisc_1(k2_zfmisc_1(A_58, B_59))) | ~v1_funct_2(C_60, A_58, B_59) | ~v1_funct_1(C_60))), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.13/1.42  tff(c_257, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_187, c_254])).
% 3.13/1.42  tff(c_260, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_189, c_188, c_40, c_257])).
% 3.13/1.42  tff(c_38, plain, (k2_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_1') | k1_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_130])).
% 3.13/1.42  tff(c_112, plain, (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_1') | k1_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_63, c_63, c_62, c_62, c_63, c_63, c_62, c_62, c_38])).
% 3.13/1.42  tff(c_113, plain, (k1_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_112])).
% 3.13/1.42  tff(c_168, plain, (k1_relset_1(k2_relat_1('#skF_3'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_120, c_120, c_120, c_113])).
% 3.13/1.42  tff(c_185, plain, (k1_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_184, c_184, c_168])).
% 3.13/1.42  tff(c_309, plain, (k1_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_260, c_185])).
% 3.13/1.43  tff(c_336, plain, (k1_relat_1(k2_funct_1('#skF_3'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_335, c_309])).
% 3.13/1.43  tff(c_343, plain, (~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_6, c_336])).
% 3.13/1.43  tff(c_347, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_84, c_48, c_40, c_343])).
% 3.13/1.43  tff(c_348, plain, (k2_relat_1('#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_183])).
% 3.13/1.43  tff(c_52, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_130])).
% 3.13/1.43  tff(c_34, plain, (![A_18]: (~v1_xboole_0(k2_struct_0(A_18)) | ~l1_struct_0(A_18) | v2_struct_0(A_18))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.13/1.43  tff(c_133, plain, (~v1_xboole_0(k2_relat_1('#skF_3')) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_120, c_34])).
% 3.13/1.43  tff(c_137, plain, (~v1_xboole_0(k2_relat_1('#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_133])).
% 3.13/1.43  tff(c_138, plain, (~v1_xboole_0(k2_relat_1('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_52, c_137])).
% 3.13/1.43  tff(c_356, plain, (~v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_348, c_138])).
% 3.13/1.43  tff(c_360, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_356])).
% 3.13/1.43  tff(c_361, plain, (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_112])).
% 3.13/1.43  tff(c_422, plain, (k2_relset_1(k2_relat_1('#skF_3'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3'))!=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_369, c_369, c_361])).
% 3.13/1.43  tff(c_439, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_438, c_438, c_438, c_422])).
% 3.13/1.43  tff(c_521, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_519, c_439])).
% 3.13/1.43  tff(c_627, plain, (k2_relat_1(k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_626, c_521])).
% 3.13/1.43  tff(c_634, plain, (~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_4, c_627])).
% 3.13/1.43  tff(c_638, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_84, c_48, c_40, c_634])).
% 3.13/1.43  tff(c_639, plain, (k2_relat_1('#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_437])).
% 3.13/1.43  tff(c_382, plain, (~v1_xboole_0(k2_relat_1('#skF_3')) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_369, c_34])).
% 3.13/1.43  tff(c_386, plain, (~v1_xboole_0(k2_relat_1('#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_382])).
% 3.13/1.43  tff(c_387, plain, (~v1_xboole_0(k2_relat_1('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_52, c_386])).
% 3.13/1.43  tff(c_648, plain, (~v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_639, c_387])).
% 3.13/1.43  tff(c_652, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_648])).
% 3.13/1.43  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.13/1.43  
% 3.13/1.43  Inference rules
% 3.13/1.43  ----------------------
% 3.13/1.43  #Ref     : 0
% 3.13/1.43  #Sup     : 136
% 3.13/1.43  #Fact    : 0
% 3.13/1.43  #Define  : 0
% 3.13/1.43  #Split   : 5
% 3.13/1.43  #Chain   : 0
% 3.13/1.43  #Close   : 0
% 3.13/1.43  
% 3.13/1.43  Ordering : KBO
% 3.13/1.43  
% 3.13/1.43  Simplification rules
% 3.13/1.43  ----------------------
% 3.13/1.43  #Subsume      : 4
% 3.13/1.43  #Demod        : 169
% 3.13/1.43  #Tautology    : 84
% 3.13/1.43  #SimpNegUnit  : 2
% 3.13/1.43  #BackRed      : 47
% 3.13/1.43  
% 3.13/1.43  #Partial instantiations: 0
% 3.13/1.43  #Strategies tried      : 1
% 3.13/1.43  
% 3.13/1.43  Timing (in seconds)
% 3.13/1.43  ----------------------
% 3.13/1.43  Preprocessing        : 0.34
% 3.13/1.43  Parsing              : 0.18
% 3.13/1.43  CNF conversion       : 0.02
% 3.13/1.43  Main loop            : 0.33
% 3.13/1.43  Inferencing          : 0.11
% 3.13/1.43  Reduction            : 0.11
% 3.13/1.43  Demodulation         : 0.08
% 3.13/1.43  BG Simplification    : 0.02
% 3.13/1.43  Subsumption          : 0.06
% 3.13/1.43  Abstraction          : 0.02
% 3.13/1.43  MUC search           : 0.00
% 3.13/1.43  Cooper               : 0.00
% 3.13/1.43  Total                : 0.72
% 3.13/1.43  Index Insertion      : 0.00
% 3.13/1.43  Index Deletion       : 0.00
% 3.13/1.43  Index Matching       : 0.00
% 3.13/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
