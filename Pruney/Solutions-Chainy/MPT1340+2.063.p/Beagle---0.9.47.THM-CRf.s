%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:39 EST 2020

% Result     : Theorem 4.37s
% Output     : CNFRefutation 4.79s
% Verified   : 
% Statistics : Number of formulae       :  178 (69992 expanded)
%              Number of leaves         :   46 (24343 expanded)
%              Depth                    :   28
%              Number of atoms          :  446 (200810 expanded)
%              Number of equality atoms :   88 (43280 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k2_tops_2 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k6_relat_1 > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

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

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tops_2,type,(
    k2_tops_2: ( $i * $i * $i ) > $i )).

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

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(r2_funct_2,type,(
    r2_funct_2: ( $i * $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_243,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_tops_2)).

tff(f_201,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_133,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_209,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_34,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_129,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_155,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_147,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_171,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_funct_2(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_funct_2)).

tff(f_187,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( v2_funct_1(C)
          & k2_relset_1(A,B,C) = B )
       => ( v1_funct_1(k2_funct_1(C))
          & v1_funct_2(k2_funct_1(C),B,A)
          & m1_subset_1(k2_funct_1(C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).

tff(f_54,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A)
        & v2_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A))
        & v2_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_funct_1)).

tff(f_96,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_197,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_106,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_123,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( ( v2_funct_1(A)
              & k2_relat_1(B) = k1_relat_1(A)
              & k5_relat_1(B,A) = k6_relat_1(k2_relat_1(A)) )
           => B = k2_funct_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_1)).

tff(f_221,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( k2_relset_1(A,B,C) = B
          & v2_funct_1(C) )
       => k2_tops_2(A,B,C) = k2_funct_1(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_2)).

tff(c_78,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_243])).

tff(c_84,plain,(
    l1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_243])).

tff(c_86,plain,(
    ! [A_50] :
      ( u1_struct_0(A_50) = k2_struct_0(A_50)
      | ~ l1_struct_0(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_94,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_84,c_86])).

tff(c_80,plain,(
    l1_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_243])).

tff(c_93,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_80,c_86])).

tff(c_74,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_243])).

tff(c_124,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_93,c_74])).

tff(c_206,plain,(
    ! [A_71,B_72,C_73] :
      ( k2_relset_1(A_71,B_72,C_73) = k2_relat_1(C_73)
      | ~ m1_subset_1(C_73,k1_zfmisc_1(k2_zfmisc_1(A_71,B_72))) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_214,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_124,c_206])).

tff(c_72,plain,(
    k2_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_243])).

tff(c_119,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_93,c_72])).

tff(c_228,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_214,c_119])).

tff(c_82,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_243])).

tff(c_106,plain,(
    ! [A_53] :
      ( ~ v1_xboole_0(u1_struct_0(A_53))
      | ~ l1_struct_0(A_53)
      | v2_struct_0(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_112,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_2'))
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_93,c_106])).

tff(c_116,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_2'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_112])).

tff(c_117,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_116])).

tff(c_237,plain,(
    ~ v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_228,c_117])).

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_125,plain,(
    ! [B_54,A_55] :
      ( v1_relat_1(B_54)
      | ~ m1_subset_1(B_54,k1_zfmisc_1(A_55))
      | ~ v1_relat_1(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_128,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_124,c_125])).

tff(c_131,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_128])).

tff(c_133,plain,(
    ! [C_56,A_57,B_58] :
      ( v4_relat_1(C_56,A_57)
      | ~ m1_subset_1(C_56,k1_zfmisc_1(k2_zfmisc_1(A_57,B_58))) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_137,plain,(
    v4_relat_1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_124,c_133])).

tff(c_146,plain,(
    ! [B_65,A_66] :
      ( k1_relat_1(B_65) = A_66
      | ~ v1_partfun1(B_65,A_66)
      | ~ v4_relat_1(B_65,A_66)
      | ~ v1_relat_1(B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_149,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_137,c_146])).

tff(c_152,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_149])).

tff(c_153,plain,(
    ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_152])).

tff(c_76,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_243])).

tff(c_103,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_93,c_76])).

tff(c_238,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_228,c_103])).

tff(c_236,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_228,c_124])).

tff(c_332,plain,(
    ! [C_84,A_85,B_86] :
      ( v1_partfun1(C_84,A_85)
      | ~ v1_funct_2(C_84,A_85,B_86)
      | ~ v1_funct_1(C_84)
      | ~ m1_subset_1(C_84,k1_zfmisc_1(k2_zfmisc_1(A_85,B_86)))
      | v1_xboole_0(B_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_335,plain,
    ( v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3')
    | v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_236,c_332])).

tff(c_341,plain,
    ( v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_238,c_335])).

tff(c_343,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_237,c_153,c_341])).

tff(c_344,plain,(
    k2_struct_0('#skF_1') = k1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_152])).

tff(c_348,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_344,c_124])).

tff(c_470,plain,(
    ! [A_93,B_94,C_95] :
      ( k2_relset_1(A_93,B_94,C_95) = k2_relat_1(C_95)
      | ~ m1_subset_1(C_95,k1_zfmisc_1(k2_zfmisc_1(A_93,B_94))) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_478,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_348,c_470])).

tff(c_350,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_344,c_119])).

tff(c_479,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_478,c_350])).

tff(c_351,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_344,c_103])).

tff(c_487,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_479,c_351])).

tff(c_486,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_479,c_348])).

tff(c_594,plain,(
    ! [A_104,B_105,D_106] :
      ( r2_funct_2(A_104,B_105,D_106,D_106)
      | ~ m1_subset_1(D_106,k1_zfmisc_1(k2_zfmisc_1(A_104,B_105)))
      | ~ v1_funct_2(D_106,A_104,B_105)
      | ~ v1_funct_1(D_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_596,plain,
    ( r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3','#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_486,c_594])).

tff(c_601,plain,(
    r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_487,c_596])).

tff(c_70,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_243])).

tff(c_484,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_479,c_478])).

tff(c_854,plain,(
    ! [C_137,B_138,A_139] :
      ( m1_subset_1(k2_funct_1(C_137),k1_zfmisc_1(k2_zfmisc_1(B_138,A_139)))
      | k2_relset_1(A_139,B_138,C_137) != B_138
      | ~ v2_funct_1(C_137)
      | ~ m1_subset_1(C_137,k1_zfmisc_1(k2_zfmisc_1(A_139,B_138)))
      | ~ v1_funct_2(C_137,A_139,B_138)
      | ~ v1_funct_1(C_137) ) ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_2,plain,(
    ! [B_3,A_1] :
      ( v1_relat_1(B_3)
      | ~ m1_subset_1(B_3,k1_zfmisc_1(A_1))
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_880,plain,(
    ! [C_137,B_138,A_139] :
      ( v1_relat_1(k2_funct_1(C_137))
      | ~ v1_relat_1(k2_zfmisc_1(B_138,A_139))
      | k2_relset_1(A_139,B_138,C_137) != B_138
      | ~ v2_funct_1(C_137)
      | ~ m1_subset_1(C_137,k1_zfmisc_1(k2_zfmisc_1(A_139,B_138)))
      | ~ v1_funct_2(C_137,A_139,B_138)
      | ~ v1_funct_1(C_137) ) ),
    inference(resolution,[status(thm)],[c_854,c_2])).

tff(c_892,plain,(
    ! [C_140,A_141,B_142] :
      ( v1_relat_1(k2_funct_1(C_140))
      | k2_relset_1(A_141,B_142,C_140) != B_142
      | ~ v2_funct_1(C_140)
      | ~ m1_subset_1(C_140,k1_zfmisc_1(k2_zfmisc_1(A_141,B_142)))
      | ~ v1_funct_2(C_140,A_141,B_142)
      | ~ v1_funct_1(C_140) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_880])).

tff(c_904,plain,
    ( v1_relat_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_486,c_892])).

tff(c_913,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_487,c_70,c_484,c_904])).

tff(c_652,plain,(
    ! [C_116,A_117,B_118] :
      ( v1_funct_1(k2_funct_1(C_116))
      | k2_relset_1(A_117,B_118,C_116) != B_118
      | ~ v2_funct_1(C_116)
      | ~ m1_subset_1(C_116,k1_zfmisc_1(k2_zfmisc_1(A_117,B_118)))
      | ~ v1_funct_2(C_116,A_117,B_118)
      | ~ v1_funct_1(C_116) ) ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_655,plain,
    ( v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_486,c_652])).

tff(c_661,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_487,c_70,c_484,c_655])).

tff(c_10,plain,(
    ! [A_7] :
      ( v2_funct_1(k2_funct_1(A_7))
      | ~ v2_funct_1(A_7)
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_34,plain,(
    ! [C_21,A_19,B_20] :
      ( v4_relat_1(C_21,A_19)
      | ~ m1_subset_1(C_21,k1_zfmisc_1(k2_zfmisc_1(A_19,B_20))) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_938,plain,(
    ! [C_146,B_147,A_148] :
      ( v4_relat_1(k2_funct_1(C_146),B_147)
      | k2_relset_1(A_148,B_147,C_146) != B_147
      | ~ v2_funct_1(C_146)
      | ~ m1_subset_1(C_146,k1_zfmisc_1(k2_zfmisc_1(A_148,B_147)))
      | ~ v1_funct_2(C_146,A_148,B_147)
      | ~ v1_funct_1(C_146) ) ),
    inference(resolution,[status(thm)],[c_854,c_34])).

tff(c_950,plain,
    ( v4_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_486,c_938])).

tff(c_959,plain,(
    v4_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_487,c_70,c_484,c_950])).

tff(c_24,plain,(
    ! [A_14] :
      ( k1_relat_1(k2_funct_1(A_14)) = k2_relat_1(A_14)
      | ~ v2_funct_1(A_14)
      | ~ v1_funct_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_413,plain,(
    ! [A_88] :
      ( k1_relat_1(k2_funct_1(A_88)) = k2_relat_1(A_88)
      | ~ v2_funct_1(A_88)
      | ~ v1_funct_1(A_88)
      | ~ v1_relat_1(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_42,plain,(
    ! [B_30] :
      ( v1_partfun1(B_30,k1_relat_1(B_30))
      | ~ v4_relat_1(B_30,k1_relat_1(B_30))
      | ~ v1_relat_1(B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_648,plain,(
    ! [A_115] :
      ( v1_partfun1(k2_funct_1(A_115),k1_relat_1(k2_funct_1(A_115)))
      | ~ v4_relat_1(k2_funct_1(A_115),k2_relat_1(A_115))
      | ~ v1_relat_1(k2_funct_1(A_115))
      | ~ v2_funct_1(A_115)
      | ~ v1_funct_1(A_115)
      | ~ v1_relat_1(A_115) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_413,c_42])).

tff(c_651,plain,(
    ! [A_14] :
      ( v1_partfun1(k2_funct_1(A_14),k2_relat_1(A_14))
      | ~ v4_relat_1(k2_funct_1(A_14),k2_relat_1(A_14))
      | ~ v1_relat_1(k2_funct_1(A_14))
      | ~ v2_funct_1(A_14)
      | ~ v1_funct_1(A_14)
      | ~ v1_relat_1(A_14)
      | ~ v2_funct_1(A_14)
      | ~ v1_funct_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_648])).

tff(c_963,plain,
    ( v1_partfun1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_959,c_651])).

tff(c_969,plain,(
    v1_partfun1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_78,c_70,c_913,c_963])).

tff(c_44,plain,(
    ! [B_30,A_29] :
      ( k1_relat_1(B_30) = A_29
      | ~ v1_partfun1(B_30,A_29)
      | ~ v4_relat_1(B_30,A_29)
      | ~ v1_relat_1(B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_966,plain,
    ( k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3')
    | ~ v1_partfun1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_959,c_44])).

tff(c_972,plain,
    ( k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3')
    | ~ v1_partfun1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_913,c_966])).

tff(c_974,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_969,c_972])).

tff(c_22,plain,(
    ! [A_14] :
      ( k2_relat_1(k2_funct_1(A_14)) = k1_relat_1(A_14)
      | ~ v2_funct_1(A_14)
      | ~ v1_funct_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_56,plain,(
    ! [A_38] :
      ( m1_subset_1(A_38,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_38),k2_relat_1(A_38))))
      | ~ v1_funct_1(A_38)
      | ~ v1_relat_1(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_539,plain,(
    ! [A_97] :
      ( k2_relset_1(k1_relat_1(A_97),k2_relat_1(A_97),A_97) = k2_relat_1(A_97)
      | ~ v1_funct_1(A_97)
      | ~ v1_relat_1(A_97) ) ),
    inference(resolution,[status(thm)],[c_56,c_470])).

tff(c_557,plain,(
    ! [A_14] :
      ( k2_relset_1(k1_relat_1(k2_funct_1(A_14)),k1_relat_1(A_14),k2_funct_1(A_14)) = k2_relat_1(k2_funct_1(A_14))
      | ~ v1_funct_1(k2_funct_1(A_14))
      | ~ v1_relat_1(k2_funct_1(A_14))
      | ~ v2_funct_1(A_14)
      | ~ v1_funct_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_539])).

tff(c_984,plain,
    ( k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_974,c_557])).

tff(c_1040,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_78,c_70,c_913,c_661,c_984])).

tff(c_788,plain,(
    ! [C_127,B_128,A_129] :
      ( v1_funct_2(k2_funct_1(C_127),B_128,A_129)
      | k2_relset_1(A_129,B_128,C_127) != B_128
      | ~ v2_funct_1(C_127)
      | ~ m1_subset_1(C_127,k1_zfmisc_1(k2_zfmisc_1(A_129,B_128)))
      | ~ v1_funct_2(C_127,A_129,B_128)
      | ~ v1_funct_1(C_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_797,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_486,c_788])).

tff(c_805,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_487,c_70,c_484,c_797])).

tff(c_428,plain,(
    ! [A_89] :
      ( m1_subset_1(A_89,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_89),k2_relat_1(A_89))))
      | ~ v1_funct_1(A_89)
      | ~ v1_relat_1(A_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_443,plain,(
    ! [A_14] :
      ( m1_subset_1(k2_funct_1(A_14),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(A_14)),k1_relat_1(A_14))))
      | ~ v1_funct_1(k2_funct_1(A_14))
      | ~ v1_relat_1(k2_funct_1(A_14))
      | ~ v2_funct_1(A_14)
      | ~ v1_funct_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_428])).

tff(c_990,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_974,c_443])).

tff(c_1044,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_78,c_70,c_913,c_661,c_990])).

tff(c_891,plain,(
    ! [C_137,A_139,B_138] :
      ( v1_relat_1(k2_funct_1(C_137))
      | k2_relset_1(A_139,B_138,C_137) != B_138
      | ~ v2_funct_1(C_137)
      | ~ m1_subset_1(C_137,k1_zfmisc_1(k2_zfmisc_1(A_139,B_138)))
      | ~ v1_funct_2(C_137,A_139,B_138)
      | ~ v1_funct_1(C_137) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_880])).

tff(c_1100,plain,
    ( v1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))
    | k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) != k1_relat_1('#skF_3')
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_1044,c_891])).

tff(c_1135,plain,
    ( v1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))
    | k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) != k1_relat_1('#skF_3')
    | ~ v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_661,c_805,c_1100])).

tff(c_1315,plain,
    ( v1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))
    | k2_relat_1(k2_funct_1('#skF_3')) != k1_relat_1('#skF_3')
    | ~ v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1040,c_1135])).

tff(c_1316,plain,(
    ~ v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1315])).

tff(c_1319,plain,
    ( ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_10,c_1316])).

tff(c_1323,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_78,c_70,c_1319])).

tff(c_1325,plain,(
    v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1315])).

tff(c_888,plain,(
    ! [C_137,B_138,A_139] :
      ( v4_relat_1(k2_funct_1(C_137),B_138)
      | k2_relset_1(A_139,B_138,C_137) != B_138
      | ~ v2_funct_1(C_137)
      | ~ m1_subset_1(C_137,k1_zfmisc_1(k2_zfmisc_1(A_139,B_138)))
      | ~ v1_funct_2(C_137,A_139,B_138)
      | ~ v1_funct_1(C_137) ) ),
    inference(resolution,[status(thm)],[c_854,c_34])).

tff(c_1094,plain,
    ( v4_relat_1(k2_funct_1(k2_funct_1('#skF_3')),k1_relat_1('#skF_3'))
    | k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) != k1_relat_1('#skF_3')
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_1044,c_888])).

tff(c_1129,plain,
    ( v4_relat_1(k2_funct_1(k2_funct_1('#skF_3')),k1_relat_1('#skF_3'))
    | k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) != k1_relat_1('#skF_3')
    | ~ v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_661,c_805,c_1094])).

tff(c_1486,plain,
    ( v4_relat_1(k2_funct_1(k2_funct_1('#skF_3')),k1_relat_1('#skF_3'))
    | k2_relat_1(k2_funct_1('#skF_3')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1325,c_1040,c_1129])).

tff(c_1487,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) != k1_relat_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_1486])).

tff(c_1490,plain,
    ( ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_1487])).

tff(c_1494,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_78,c_70,c_1490])).

tff(c_1496,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_1486])).

tff(c_28,plain,(
    ! [A_15] :
      ( k5_relat_1(A_15,k2_funct_1(A_15)) = k6_relat_1(k1_relat_1(A_15))
      | ~ v2_funct_1(A_15)
      | ~ v1_funct_1(A_15)
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_677,plain,(
    ! [A_121,B_122] :
      ( k2_funct_1(A_121) = B_122
      | k6_relat_1(k2_relat_1(A_121)) != k5_relat_1(B_122,A_121)
      | k2_relat_1(B_122) != k1_relat_1(A_121)
      | ~ v2_funct_1(A_121)
      | ~ v1_funct_1(B_122)
      | ~ v1_relat_1(B_122)
      | ~ v1_funct_1(A_121)
      | ~ v1_relat_1(A_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_1983,plain,(
    ! [A_166] :
      ( k2_funct_1(k2_funct_1(A_166)) = A_166
      | k6_relat_1(k2_relat_1(k2_funct_1(A_166))) != k6_relat_1(k1_relat_1(A_166))
      | k1_relat_1(k2_funct_1(A_166)) != k2_relat_1(A_166)
      | ~ v2_funct_1(k2_funct_1(A_166))
      | ~ v1_funct_1(A_166)
      | ~ v1_relat_1(A_166)
      | ~ v1_funct_1(k2_funct_1(A_166))
      | ~ v1_relat_1(k2_funct_1(A_166))
      | ~ v2_funct_1(A_166)
      | ~ v1_funct_1(A_166)
      | ~ v1_relat_1(A_166) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_677])).

tff(c_1989,plain,
    ( k2_funct_1(k2_funct_1('#skF_3')) = '#skF_3'
    | k1_relat_1(k2_funct_1('#skF_3')) != k2_relat_1('#skF_3')
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1496,c_1983])).

tff(c_1997,plain,(
    k2_funct_1(k2_funct_1('#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_78,c_70,c_913,c_661,c_1325,c_974,c_1989])).

tff(c_58,plain,(
    ! [A_38] :
      ( v1_funct_2(A_38,k1_relat_1(A_38),k2_relat_1(A_38))
      | ~ v1_funct_1(A_38)
      | ~ v1_relat_1(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_1029,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k2_relat_1(k2_funct_1('#skF_3')))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_974,c_58])).

tff(c_1071,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k2_relat_1(k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_913,c_661,c_1029])).

tff(c_477,plain,(
    ! [A_38] :
      ( k2_relset_1(k1_relat_1(A_38),k2_relat_1(A_38),A_38) = k2_relat_1(A_38)
      | ~ v1_funct_1(A_38)
      | ~ v1_relat_1(A_38) ) ),
    inference(resolution,[status(thm)],[c_56,c_470])).

tff(c_1011,plain,
    ( k2_relset_1(k2_relat_1('#skF_3'),k2_relat_1(k2_funct_1('#skF_3')),k2_funct_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_974,c_477])).

tff(c_1058,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k2_relat_1(k2_funct_1('#skF_3')),k2_funct_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_913,c_661,c_1011])).

tff(c_807,plain,(
    ! [A_130,B_131,C_132] :
      ( k2_tops_2(A_130,B_131,C_132) = k2_funct_1(C_132)
      | ~ v2_funct_1(C_132)
      | k2_relset_1(A_130,B_131,C_132) != B_131
      | ~ m1_subset_1(C_132,k1_zfmisc_1(k2_zfmisc_1(A_130,B_131)))
      | ~ v1_funct_2(C_132,A_130,B_131)
      | ~ v1_funct_1(C_132) ) ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_1387,plain,(
    ! [A_157] :
      ( k2_tops_2(k1_relat_1(A_157),k2_relat_1(A_157),A_157) = k2_funct_1(A_157)
      | ~ v2_funct_1(A_157)
      | k2_relset_1(k1_relat_1(A_157),k2_relat_1(A_157),A_157) != k2_relat_1(A_157)
      | ~ v1_funct_2(A_157,k1_relat_1(A_157),k2_relat_1(A_157))
      | ~ v1_funct_1(A_157)
      | ~ v1_relat_1(A_157) ) ),
    inference(resolution,[status(thm)],[c_56,c_807])).

tff(c_1390,plain,
    ( k2_tops_2(k1_relat_1(k2_funct_1('#skF_3')),k2_relat_1(k2_funct_1('#skF_3')),k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1(k2_funct_1('#skF_3')),k2_relat_1(k2_funct_1('#skF_3')),k2_funct_1('#skF_3')) != k2_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k2_relat_1(k2_funct_1('#skF_3')))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_974,c_1387])).

tff(c_1404,plain,(
    k2_tops_2(k2_relat_1('#skF_3'),k2_relat_1(k2_funct_1('#skF_3')),k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_913,c_661,c_1071,c_1058,c_974,c_1325,c_974,c_1390])).

tff(c_1413,plain,
    ( k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_1404])).

tff(c_1417,plain,(
    k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_78,c_70,c_1413])).

tff(c_816,plain,
    ( k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_486,c_807])).

tff(c_824,plain,(
    k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_487,c_484,c_70,c_816])).

tff(c_68,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),k2_tops_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_243])).

tff(c_132,plain,(
    ~ r2_funct_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_94,c_94,c_93,c_93,c_93,c_68])).

tff(c_347,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),k2_tops_2(k2_struct_0('#skF_2'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_344,c_344,c_344,c_132])).

tff(c_485,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_479,c_479,c_479,c_347])).

tff(c_826,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_824,c_485])).

tff(c_1418,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),k2_funct_1(k2_funct_1('#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1417,c_826])).

tff(c_2008,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1997,c_1418])).

tff(c_2023,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_601,c_2008])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:06:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.37/1.74  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.37/1.76  
% 4.37/1.76  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.37/1.76  %$ r2_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k2_tops_2 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k6_relat_1 > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 4.37/1.76  
% 4.37/1.76  %Foreground sorts:
% 4.37/1.76  
% 4.37/1.76  
% 4.37/1.76  %Background operators:
% 4.37/1.76  
% 4.37/1.76  
% 4.37/1.76  %Foreground operators:
% 4.37/1.76  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.37/1.76  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.37/1.76  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.37/1.76  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 4.37/1.76  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 4.37/1.76  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.37/1.76  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 4.37/1.76  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.37/1.76  tff(k2_tops_2, type, k2_tops_2: ($i * $i * $i) > $i).
% 4.37/1.76  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.37/1.76  tff('#skF_2', type, '#skF_2': $i).
% 4.37/1.76  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 4.37/1.76  tff('#skF_3', type, '#skF_3': $i).
% 4.37/1.76  tff('#skF_1', type, '#skF_1': $i).
% 4.37/1.76  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.37/1.76  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.37/1.76  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 4.37/1.76  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.37/1.76  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.37/1.76  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.37/1.76  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 4.37/1.76  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.37/1.76  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.37/1.76  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.37/1.76  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 4.37/1.76  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.37/1.76  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.37/1.76  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 4.37/1.76  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.37/1.76  
% 4.79/1.79  tff(f_243, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: ((~v2_struct_0(B) & l1_struct_0(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B)) & v2_funct_1(C)) => r2_funct_2(u1_struct_0(A), u1_struct_0(B), k2_tops_2(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)), C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_tops_2)).
% 4.79/1.79  tff(f_201, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 4.79/1.79  tff(f_133, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 4.79/1.79  tff(f_209, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 4.79/1.79  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 4.79/1.79  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 4.79/1.79  tff(f_129, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.79/1.79  tff(f_155, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_partfun1)).
% 4.79/1.79  tff(f_147, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc5_funct_2)).
% 4.79/1.79  tff(f_171, axiom, (![A, B, C, D]: ((((((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(D)) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_funct_2(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_funct_2)).
% 4.79/1.79  tff(f_187, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_funct_2)).
% 4.79/1.79  tff(f_54, axiom, (![A]: (((v1_relat_1(A) & v1_funct_1(A)) & v2_funct_1(A)) => ((v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))) & v2_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_funct_1)).
% 4.79/1.79  tff(f_96, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 4.79/1.79  tff(f_197, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_funct_2)).
% 4.79/1.79  tff(f_106, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_funct_1)).
% 4.79/1.79  tff(f_123, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(B) = k1_relat_1(A))) & (k5_relat_1(B, A) = k6_relat_1(k2_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_funct_1)).
% 4.79/1.79  tff(f_221, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => (k2_tops_2(A, B, C) = k2_funct_1(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tops_2)).
% 4.79/1.79  tff(c_78, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_243])).
% 4.79/1.79  tff(c_84, plain, (l1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_243])).
% 4.79/1.79  tff(c_86, plain, (![A_50]: (u1_struct_0(A_50)=k2_struct_0(A_50) | ~l1_struct_0(A_50))), inference(cnfTransformation, [status(thm)], [f_201])).
% 4.79/1.79  tff(c_94, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_84, c_86])).
% 4.79/1.79  tff(c_80, plain, (l1_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_243])).
% 4.79/1.79  tff(c_93, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_80, c_86])).
% 4.79/1.79  tff(c_74, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_243])).
% 4.79/1.79  tff(c_124, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_93, c_74])).
% 4.79/1.79  tff(c_206, plain, (![A_71, B_72, C_73]: (k2_relset_1(A_71, B_72, C_73)=k2_relat_1(C_73) | ~m1_subset_1(C_73, k1_zfmisc_1(k2_zfmisc_1(A_71, B_72))))), inference(cnfTransformation, [status(thm)], [f_133])).
% 4.79/1.79  tff(c_214, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_124, c_206])).
% 4.79/1.79  tff(c_72, plain, (k2_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_243])).
% 4.79/1.79  tff(c_119, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_93, c_72])).
% 4.79/1.79  tff(c_228, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_214, c_119])).
% 4.79/1.79  tff(c_82, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_243])).
% 4.79/1.79  tff(c_106, plain, (![A_53]: (~v1_xboole_0(u1_struct_0(A_53)) | ~l1_struct_0(A_53) | v2_struct_0(A_53))), inference(cnfTransformation, [status(thm)], [f_209])).
% 4.79/1.79  tff(c_112, plain, (~v1_xboole_0(k2_struct_0('#skF_2')) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_93, c_106])).
% 4.79/1.79  tff(c_116, plain, (~v1_xboole_0(k2_struct_0('#skF_2')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_112])).
% 4.79/1.79  tff(c_117, plain, (~v1_xboole_0(k2_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_82, c_116])).
% 4.79/1.79  tff(c_237, plain, (~v1_xboole_0(k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_228, c_117])).
% 4.79/1.79  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.79/1.79  tff(c_125, plain, (![B_54, A_55]: (v1_relat_1(B_54) | ~m1_subset_1(B_54, k1_zfmisc_1(A_55)) | ~v1_relat_1(A_55))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.79/1.79  tff(c_128, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_124, c_125])).
% 4.79/1.79  tff(c_131, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_128])).
% 4.79/1.79  tff(c_133, plain, (![C_56, A_57, B_58]: (v4_relat_1(C_56, A_57) | ~m1_subset_1(C_56, k1_zfmisc_1(k2_zfmisc_1(A_57, B_58))))), inference(cnfTransformation, [status(thm)], [f_129])).
% 4.79/1.79  tff(c_137, plain, (v4_relat_1('#skF_3', k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_124, c_133])).
% 4.79/1.79  tff(c_146, plain, (![B_65, A_66]: (k1_relat_1(B_65)=A_66 | ~v1_partfun1(B_65, A_66) | ~v4_relat_1(B_65, A_66) | ~v1_relat_1(B_65))), inference(cnfTransformation, [status(thm)], [f_155])).
% 4.79/1.79  tff(c_149, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_137, c_146])).
% 4.79/1.79  tff(c_152, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_131, c_149])).
% 4.79/1.79  tff(c_153, plain, (~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_152])).
% 4.79/1.79  tff(c_76, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_243])).
% 4.79/1.79  tff(c_103, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_93, c_76])).
% 4.79/1.79  tff(c_238, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_228, c_103])).
% 4.79/1.79  tff(c_236, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_228, c_124])).
% 4.79/1.79  tff(c_332, plain, (![C_84, A_85, B_86]: (v1_partfun1(C_84, A_85) | ~v1_funct_2(C_84, A_85, B_86) | ~v1_funct_1(C_84) | ~m1_subset_1(C_84, k1_zfmisc_1(k2_zfmisc_1(A_85, B_86))) | v1_xboole_0(B_86))), inference(cnfTransformation, [status(thm)], [f_147])).
% 4.79/1.79  tff(c_335, plain, (v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3') | v1_xboole_0(k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_236, c_332])).
% 4.79/1.79  tff(c_341, plain, (v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | v1_xboole_0(k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_238, c_335])).
% 4.79/1.79  tff(c_343, plain, $false, inference(negUnitSimplification, [status(thm)], [c_237, c_153, c_341])).
% 4.79/1.79  tff(c_344, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_152])).
% 4.79/1.79  tff(c_348, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_344, c_124])).
% 4.79/1.79  tff(c_470, plain, (![A_93, B_94, C_95]: (k2_relset_1(A_93, B_94, C_95)=k2_relat_1(C_95) | ~m1_subset_1(C_95, k1_zfmisc_1(k2_zfmisc_1(A_93, B_94))))), inference(cnfTransformation, [status(thm)], [f_133])).
% 4.79/1.79  tff(c_478, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_348, c_470])).
% 4.79/1.79  tff(c_350, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_344, c_119])).
% 4.79/1.79  tff(c_479, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_478, c_350])).
% 4.79/1.79  tff(c_351, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_344, c_103])).
% 4.79/1.79  tff(c_487, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_479, c_351])).
% 4.79/1.79  tff(c_486, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_479, c_348])).
% 4.79/1.79  tff(c_594, plain, (![A_104, B_105, D_106]: (r2_funct_2(A_104, B_105, D_106, D_106) | ~m1_subset_1(D_106, k1_zfmisc_1(k2_zfmisc_1(A_104, B_105))) | ~v1_funct_2(D_106, A_104, B_105) | ~v1_funct_1(D_106))), inference(cnfTransformation, [status(thm)], [f_171])).
% 4.79/1.79  tff(c_596, plain, (r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3', '#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_486, c_594])).
% 4.79/1.79  tff(c_601, plain, (r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_487, c_596])).
% 4.79/1.79  tff(c_70, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_243])).
% 4.79/1.79  tff(c_484, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_479, c_478])).
% 4.79/1.79  tff(c_854, plain, (![C_137, B_138, A_139]: (m1_subset_1(k2_funct_1(C_137), k1_zfmisc_1(k2_zfmisc_1(B_138, A_139))) | k2_relset_1(A_139, B_138, C_137)!=B_138 | ~v2_funct_1(C_137) | ~m1_subset_1(C_137, k1_zfmisc_1(k2_zfmisc_1(A_139, B_138))) | ~v1_funct_2(C_137, A_139, B_138) | ~v1_funct_1(C_137))), inference(cnfTransformation, [status(thm)], [f_187])).
% 4.79/1.79  tff(c_2, plain, (![B_3, A_1]: (v1_relat_1(B_3) | ~m1_subset_1(B_3, k1_zfmisc_1(A_1)) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.79/1.79  tff(c_880, plain, (![C_137, B_138, A_139]: (v1_relat_1(k2_funct_1(C_137)) | ~v1_relat_1(k2_zfmisc_1(B_138, A_139)) | k2_relset_1(A_139, B_138, C_137)!=B_138 | ~v2_funct_1(C_137) | ~m1_subset_1(C_137, k1_zfmisc_1(k2_zfmisc_1(A_139, B_138))) | ~v1_funct_2(C_137, A_139, B_138) | ~v1_funct_1(C_137))), inference(resolution, [status(thm)], [c_854, c_2])).
% 4.79/1.79  tff(c_892, plain, (![C_140, A_141, B_142]: (v1_relat_1(k2_funct_1(C_140)) | k2_relset_1(A_141, B_142, C_140)!=B_142 | ~v2_funct_1(C_140) | ~m1_subset_1(C_140, k1_zfmisc_1(k2_zfmisc_1(A_141, B_142))) | ~v1_funct_2(C_140, A_141, B_142) | ~v1_funct_1(C_140))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_880])).
% 4.79/1.79  tff(c_904, plain, (v1_relat_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_486, c_892])).
% 4.79/1.79  tff(c_913, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_487, c_70, c_484, c_904])).
% 4.79/1.79  tff(c_652, plain, (![C_116, A_117, B_118]: (v1_funct_1(k2_funct_1(C_116)) | k2_relset_1(A_117, B_118, C_116)!=B_118 | ~v2_funct_1(C_116) | ~m1_subset_1(C_116, k1_zfmisc_1(k2_zfmisc_1(A_117, B_118))) | ~v1_funct_2(C_116, A_117, B_118) | ~v1_funct_1(C_116))), inference(cnfTransformation, [status(thm)], [f_187])).
% 4.79/1.79  tff(c_655, plain, (v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_486, c_652])).
% 4.79/1.79  tff(c_661, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_487, c_70, c_484, c_655])).
% 4.79/1.79  tff(c_10, plain, (![A_7]: (v2_funct_1(k2_funct_1(A_7)) | ~v2_funct_1(A_7) | ~v1_funct_1(A_7) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.79/1.79  tff(c_34, plain, (![C_21, A_19, B_20]: (v4_relat_1(C_21, A_19) | ~m1_subset_1(C_21, k1_zfmisc_1(k2_zfmisc_1(A_19, B_20))))), inference(cnfTransformation, [status(thm)], [f_129])).
% 4.79/1.79  tff(c_938, plain, (![C_146, B_147, A_148]: (v4_relat_1(k2_funct_1(C_146), B_147) | k2_relset_1(A_148, B_147, C_146)!=B_147 | ~v2_funct_1(C_146) | ~m1_subset_1(C_146, k1_zfmisc_1(k2_zfmisc_1(A_148, B_147))) | ~v1_funct_2(C_146, A_148, B_147) | ~v1_funct_1(C_146))), inference(resolution, [status(thm)], [c_854, c_34])).
% 4.79/1.79  tff(c_950, plain, (v4_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_486, c_938])).
% 4.79/1.79  tff(c_959, plain, (v4_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_487, c_70, c_484, c_950])).
% 4.79/1.79  tff(c_24, plain, (![A_14]: (k1_relat_1(k2_funct_1(A_14))=k2_relat_1(A_14) | ~v2_funct_1(A_14) | ~v1_funct_1(A_14) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.79/1.79  tff(c_413, plain, (![A_88]: (k1_relat_1(k2_funct_1(A_88))=k2_relat_1(A_88) | ~v2_funct_1(A_88) | ~v1_funct_1(A_88) | ~v1_relat_1(A_88))), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.79/1.79  tff(c_42, plain, (![B_30]: (v1_partfun1(B_30, k1_relat_1(B_30)) | ~v4_relat_1(B_30, k1_relat_1(B_30)) | ~v1_relat_1(B_30))), inference(cnfTransformation, [status(thm)], [f_155])).
% 4.79/1.79  tff(c_648, plain, (![A_115]: (v1_partfun1(k2_funct_1(A_115), k1_relat_1(k2_funct_1(A_115))) | ~v4_relat_1(k2_funct_1(A_115), k2_relat_1(A_115)) | ~v1_relat_1(k2_funct_1(A_115)) | ~v2_funct_1(A_115) | ~v1_funct_1(A_115) | ~v1_relat_1(A_115))), inference(superposition, [status(thm), theory('equality')], [c_413, c_42])).
% 4.79/1.79  tff(c_651, plain, (![A_14]: (v1_partfun1(k2_funct_1(A_14), k2_relat_1(A_14)) | ~v4_relat_1(k2_funct_1(A_14), k2_relat_1(A_14)) | ~v1_relat_1(k2_funct_1(A_14)) | ~v2_funct_1(A_14) | ~v1_funct_1(A_14) | ~v1_relat_1(A_14) | ~v2_funct_1(A_14) | ~v1_funct_1(A_14) | ~v1_relat_1(A_14))), inference(superposition, [status(thm), theory('equality')], [c_24, c_648])).
% 4.79/1.79  tff(c_963, plain, (v1_partfun1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_959, c_651])).
% 4.79/1.79  tff(c_969, plain, (v1_partfun1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_131, c_78, c_70, c_913, c_963])).
% 4.79/1.79  tff(c_44, plain, (![B_30, A_29]: (k1_relat_1(B_30)=A_29 | ~v1_partfun1(B_30, A_29) | ~v4_relat_1(B_30, A_29) | ~v1_relat_1(B_30))), inference(cnfTransformation, [status(thm)], [f_155])).
% 4.79/1.79  tff(c_966, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3') | ~v1_partfun1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_959, c_44])).
% 4.79/1.79  tff(c_972, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3') | ~v1_partfun1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_913, c_966])).
% 4.79/1.79  tff(c_974, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_969, c_972])).
% 4.79/1.79  tff(c_22, plain, (![A_14]: (k2_relat_1(k2_funct_1(A_14))=k1_relat_1(A_14) | ~v2_funct_1(A_14) | ~v1_funct_1(A_14) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.79/1.79  tff(c_56, plain, (![A_38]: (m1_subset_1(A_38, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_38), k2_relat_1(A_38)))) | ~v1_funct_1(A_38) | ~v1_relat_1(A_38))), inference(cnfTransformation, [status(thm)], [f_197])).
% 4.79/1.79  tff(c_539, plain, (![A_97]: (k2_relset_1(k1_relat_1(A_97), k2_relat_1(A_97), A_97)=k2_relat_1(A_97) | ~v1_funct_1(A_97) | ~v1_relat_1(A_97))), inference(resolution, [status(thm)], [c_56, c_470])).
% 4.79/1.79  tff(c_557, plain, (![A_14]: (k2_relset_1(k1_relat_1(k2_funct_1(A_14)), k1_relat_1(A_14), k2_funct_1(A_14))=k2_relat_1(k2_funct_1(A_14)) | ~v1_funct_1(k2_funct_1(A_14)) | ~v1_relat_1(k2_funct_1(A_14)) | ~v2_funct_1(A_14) | ~v1_funct_1(A_14) | ~v1_relat_1(A_14))), inference(superposition, [status(thm), theory('equality')], [c_22, c_539])).
% 4.79/1.79  tff(c_984, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_974, c_557])).
% 4.79/1.79  tff(c_1040, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_131, c_78, c_70, c_913, c_661, c_984])).
% 4.79/1.79  tff(c_788, plain, (![C_127, B_128, A_129]: (v1_funct_2(k2_funct_1(C_127), B_128, A_129) | k2_relset_1(A_129, B_128, C_127)!=B_128 | ~v2_funct_1(C_127) | ~m1_subset_1(C_127, k1_zfmisc_1(k2_zfmisc_1(A_129, B_128))) | ~v1_funct_2(C_127, A_129, B_128) | ~v1_funct_1(C_127))), inference(cnfTransformation, [status(thm)], [f_187])).
% 4.79/1.79  tff(c_797, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_486, c_788])).
% 4.79/1.79  tff(c_805, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_487, c_70, c_484, c_797])).
% 4.79/1.79  tff(c_428, plain, (![A_89]: (m1_subset_1(A_89, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_89), k2_relat_1(A_89)))) | ~v1_funct_1(A_89) | ~v1_relat_1(A_89))), inference(cnfTransformation, [status(thm)], [f_197])).
% 4.79/1.79  tff(c_443, plain, (![A_14]: (m1_subset_1(k2_funct_1(A_14), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(A_14)), k1_relat_1(A_14)))) | ~v1_funct_1(k2_funct_1(A_14)) | ~v1_relat_1(k2_funct_1(A_14)) | ~v2_funct_1(A_14) | ~v1_funct_1(A_14) | ~v1_relat_1(A_14))), inference(superposition, [status(thm), theory('equality')], [c_22, c_428])).
% 4.79/1.79  tff(c_990, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3')))) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_974, c_443])).
% 4.79/1.79  tff(c_1044, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_131, c_78, c_70, c_913, c_661, c_990])).
% 4.79/1.79  tff(c_891, plain, (![C_137, A_139, B_138]: (v1_relat_1(k2_funct_1(C_137)) | k2_relset_1(A_139, B_138, C_137)!=B_138 | ~v2_funct_1(C_137) | ~m1_subset_1(C_137, k1_zfmisc_1(k2_zfmisc_1(A_139, B_138))) | ~v1_funct_2(C_137, A_139, B_138) | ~v1_funct_1(C_137))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_880])).
% 4.79/1.79  tff(c_1100, plain, (v1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) | k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3') | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_1044, c_891])).
% 4.79/1.79  tff(c_1135, plain, (v1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) | k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3') | ~v2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_661, c_805, c_1100])).
% 4.79/1.79  tff(c_1315, plain, (v1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) | k2_relat_1(k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3') | ~v2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1040, c_1135])).
% 4.79/1.79  tff(c_1316, plain, (~v2_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_1315])).
% 4.79/1.79  tff(c_1319, plain, (~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_10, c_1316])).
% 4.79/1.79  tff(c_1323, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_131, c_78, c_70, c_1319])).
% 4.79/1.79  tff(c_1325, plain, (v2_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_1315])).
% 4.79/1.79  tff(c_888, plain, (![C_137, B_138, A_139]: (v4_relat_1(k2_funct_1(C_137), B_138) | k2_relset_1(A_139, B_138, C_137)!=B_138 | ~v2_funct_1(C_137) | ~m1_subset_1(C_137, k1_zfmisc_1(k2_zfmisc_1(A_139, B_138))) | ~v1_funct_2(C_137, A_139, B_138) | ~v1_funct_1(C_137))), inference(resolution, [status(thm)], [c_854, c_34])).
% 4.79/1.79  tff(c_1094, plain, (v4_relat_1(k2_funct_1(k2_funct_1('#skF_3')), k1_relat_1('#skF_3')) | k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3') | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_1044, c_888])).
% 4.79/1.79  tff(c_1129, plain, (v4_relat_1(k2_funct_1(k2_funct_1('#skF_3')), k1_relat_1('#skF_3')) | k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3') | ~v2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_661, c_805, c_1094])).
% 4.79/1.79  tff(c_1486, plain, (v4_relat_1(k2_funct_1(k2_funct_1('#skF_3')), k1_relat_1('#skF_3')) | k2_relat_1(k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1325, c_1040, c_1129])).
% 4.79/1.79  tff(c_1487, plain, (k2_relat_1(k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3')), inference(splitLeft, [status(thm)], [c_1486])).
% 4.79/1.79  tff(c_1490, plain, (~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_22, c_1487])).
% 4.79/1.79  tff(c_1494, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_131, c_78, c_70, c_1490])).
% 4.79/1.79  tff(c_1496, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_1486])).
% 4.79/1.79  tff(c_28, plain, (![A_15]: (k5_relat_1(A_15, k2_funct_1(A_15))=k6_relat_1(k1_relat_1(A_15)) | ~v2_funct_1(A_15) | ~v1_funct_1(A_15) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_106])).
% 4.79/1.79  tff(c_677, plain, (![A_121, B_122]: (k2_funct_1(A_121)=B_122 | k6_relat_1(k2_relat_1(A_121))!=k5_relat_1(B_122, A_121) | k2_relat_1(B_122)!=k1_relat_1(A_121) | ~v2_funct_1(A_121) | ~v1_funct_1(B_122) | ~v1_relat_1(B_122) | ~v1_funct_1(A_121) | ~v1_relat_1(A_121))), inference(cnfTransformation, [status(thm)], [f_123])).
% 4.79/1.79  tff(c_1983, plain, (![A_166]: (k2_funct_1(k2_funct_1(A_166))=A_166 | k6_relat_1(k2_relat_1(k2_funct_1(A_166)))!=k6_relat_1(k1_relat_1(A_166)) | k1_relat_1(k2_funct_1(A_166))!=k2_relat_1(A_166) | ~v2_funct_1(k2_funct_1(A_166)) | ~v1_funct_1(A_166) | ~v1_relat_1(A_166) | ~v1_funct_1(k2_funct_1(A_166)) | ~v1_relat_1(k2_funct_1(A_166)) | ~v2_funct_1(A_166) | ~v1_funct_1(A_166) | ~v1_relat_1(A_166))), inference(superposition, [status(thm), theory('equality')], [c_28, c_677])).
% 4.79/1.79  tff(c_1989, plain, (k2_funct_1(k2_funct_1('#skF_3'))='#skF_3' | k1_relat_1(k2_funct_1('#skF_3'))!=k2_relat_1('#skF_3') | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1496, c_1983])).
% 4.79/1.79  tff(c_1997, plain, (k2_funct_1(k2_funct_1('#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_131, c_78, c_70, c_913, c_661, c_1325, c_974, c_1989])).
% 4.79/1.79  tff(c_58, plain, (![A_38]: (v1_funct_2(A_38, k1_relat_1(A_38), k2_relat_1(A_38)) | ~v1_funct_1(A_38) | ~v1_relat_1(A_38))), inference(cnfTransformation, [status(thm)], [f_197])).
% 4.79/1.79  tff(c_1029, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k2_relat_1(k2_funct_1('#skF_3'))) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_974, c_58])).
% 4.79/1.79  tff(c_1071, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k2_relat_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_913, c_661, c_1029])).
% 4.79/1.79  tff(c_477, plain, (![A_38]: (k2_relset_1(k1_relat_1(A_38), k2_relat_1(A_38), A_38)=k2_relat_1(A_38) | ~v1_funct_1(A_38) | ~v1_relat_1(A_38))), inference(resolution, [status(thm)], [c_56, c_470])).
% 4.79/1.79  tff(c_1011, plain, (k2_relset_1(k2_relat_1('#skF_3'), k2_relat_1(k2_funct_1('#skF_3')), k2_funct_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_974, c_477])).
% 4.79/1.79  tff(c_1058, plain, (k2_relset_1(k2_relat_1('#skF_3'), k2_relat_1(k2_funct_1('#skF_3')), k2_funct_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_913, c_661, c_1011])).
% 4.79/1.79  tff(c_807, plain, (![A_130, B_131, C_132]: (k2_tops_2(A_130, B_131, C_132)=k2_funct_1(C_132) | ~v2_funct_1(C_132) | k2_relset_1(A_130, B_131, C_132)!=B_131 | ~m1_subset_1(C_132, k1_zfmisc_1(k2_zfmisc_1(A_130, B_131))) | ~v1_funct_2(C_132, A_130, B_131) | ~v1_funct_1(C_132))), inference(cnfTransformation, [status(thm)], [f_221])).
% 4.79/1.79  tff(c_1387, plain, (![A_157]: (k2_tops_2(k1_relat_1(A_157), k2_relat_1(A_157), A_157)=k2_funct_1(A_157) | ~v2_funct_1(A_157) | k2_relset_1(k1_relat_1(A_157), k2_relat_1(A_157), A_157)!=k2_relat_1(A_157) | ~v1_funct_2(A_157, k1_relat_1(A_157), k2_relat_1(A_157)) | ~v1_funct_1(A_157) | ~v1_relat_1(A_157))), inference(resolution, [status(thm)], [c_56, c_807])).
% 4.79/1.79  tff(c_1390, plain, (k2_tops_2(k1_relat_1(k2_funct_1('#skF_3')), k2_relat_1(k2_funct_1('#skF_3')), k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3')) | ~v2_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1(k2_funct_1('#skF_3')), k2_relat_1(k2_funct_1('#skF_3')), k2_funct_1('#skF_3'))!=k2_relat_1(k2_funct_1('#skF_3')) | ~v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k2_relat_1(k2_funct_1('#skF_3'))) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_974, c_1387])).
% 4.79/1.79  tff(c_1404, plain, (k2_tops_2(k2_relat_1('#skF_3'), k2_relat_1(k2_funct_1('#skF_3')), k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_913, c_661, c_1071, c_1058, c_974, c_1325, c_974, c_1390])).
% 4.79/1.79  tff(c_1413, plain, (k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_22, c_1404])).
% 4.79/1.79  tff(c_1417, plain, (k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_131, c_78, c_70, c_1413])).
% 4.79/1.79  tff(c_816, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_486, c_807])).
% 4.79/1.79  tff(c_824, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_487, c_484, c_70, c_816])).
% 4.79/1.79  tff(c_68, plain, (~r2_funct_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), k2_tops_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_243])).
% 4.79/1.79  tff(c_132, plain, (~r2_funct_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_94, c_94, c_93, c_93, c_93, c_68])).
% 4.79/1.79  tff(c_347, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), k2_tops_2(k2_struct_0('#skF_2'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_344, c_344, c_344, c_132])).
% 4.79/1.79  tff(c_485, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_479, c_479, c_479, c_347])).
% 4.79/1.79  tff(c_826, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_824, c_485])).
% 4.79/1.79  tff(c_1418, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), k2_funct_1(k2_funct_1('#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1417, c_826])).
% 4.79/1.79  tff(c_2008, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1997, c_1418])).
% 4.79/1.79  tff(c_2023, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_601, c_2008])).
% 4.79/1.79  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.79/1.79  
% 4.79/1.79  Inference rules
% 4.79/1.79  ----------------------
% 4.79/1.79  #Ref     : 0
% 4.79/1.79  #Sup     : 406
% 4.79/1.79  #Fact    : 0
% 4.79/1.79  #Define  : 0
% 4.79/1.79  #Split   : 9
% 4.79/1.79  #Chain   : 0
% 4.79/1.79  #Close   : 0
% 4.79/1.79  
% 4.79/1.79  Ordering : KBO
% 4.79/1.79  
% 4.79/1.79  Simplification rules
% 4.79/1.79  ----------------------
% 4.79/1.79  #Subsume      : 26
% 4.79/1.79  #Demod        : 827
% 4.79/1.79  #Tautology    : 208
% 4.79/1.79  #SimpNegUnit  : 11
% 4.79/1.79  #BackRed      : 50
% 4.79/1.79  
% 4.79/1.79  #Partial instantiations: 0
% 4.79/1.79  #Strategies tried      : 1
% 4.79/1.79  
% 4.79/1.79  Timing (in seconds)
% 4.79/1.79  ----------------------
% 4.79/1.79  Preprocessing        : 0.37
% 4.79/1.79  Parsing              : 0.19
% 4.79/1.79  CNF conversion       : 0.03
% 4.79/1.79  Main loop            : 0.63
% 4.79/1.79  Inferencing          : 0.21
% 4.79/1.80  Reduction            : 0.23
% 4.79/1.80  Demodulation         : 0.17
% 4.79/1.80  BG Simplification    : 0.03
% 4.79/1.80  Subsumption          : 0.10
% 4.79/1.80  Abstraction          : 0.03
% 4.79/1.80  MUC search           : 0.00
% 4.79/1.80  Cooper               : 0.00
% 4.79/1.80  Total                : 1.06
% 4.79/1.80  Index Insertion      : 0.00
% 4.79/1.80  Index Deletion       : 0.00
% 4.79/1.80  Index Matching       : 0.00
% 4.79/1.80  BG Taut test         : 0.00
%------------------------------------------------------------------------------
