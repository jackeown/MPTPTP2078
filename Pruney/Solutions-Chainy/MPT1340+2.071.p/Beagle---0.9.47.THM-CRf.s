%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:40 EST 2020

% Result     : Theorem 4.57s
% Output     : CNFRefutation 4.81s
% Verified   : 
% Statistics : Number of formulae       :  177 (20423 expanded)
%              Number of leaves         :   48 (7104 expanded)
%              Depth                    :   26
%              Number of atoms          :  456 (58392 expanded)
%              Number of equality atoms :   86 (12646 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k2_tops_2 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k6_relat_1 > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(r2_funct_2,type,(
    r2_funct_2: ( $i * $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_34,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_204,negated_conjecture,(
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

tff(f_162,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_93,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_170,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_89,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_115,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_107,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_128,axiom,(
    ! [A,B] :
    ? [C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
      & v1_relat_1(C)
      & v4_relat_1(C,A)
      & v5_relat_1(C,B)
      & v1_funct_1(C)
      & v1_funct_2(C,A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_funct_2)).

tff(f_142,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_funct_2(A,B,C,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_funct_2)).

tff(f_83,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(k2_funct_1(A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_1)).

tff(f_158,axiom,(
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

tff(f_65,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_75,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_55,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( ( v2_funct_1(k5_relat_1(B,A))
              & k2_relat_1(B) = k1_relat_1(A) )
           => ( v2_funct_1(B)
              & v2_funct_1(A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_funct_1)).

tff(f_182,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( k2_relset_1(A,B,C) = B
          & v2_funct_1(C) )
       => k2_tops_2(A,B,C) = k2_funct_1(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_2)).

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_80,plain,(
    l1_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_89,plain,(
    ! [A_58] :
      ( u1_struct_0(A_58) = k2_struct_0(A_58)
      | ~ l1_struct_0(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_97,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_80,c_89])).

tff(c_76,plain,(
    l1_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_96,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_76,c_89])).

tff(c_70,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_119,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_96,c_70])).

tff(c_127,plain,(
    ! [B_60,A_61] :
      ( v1_relat_1(B_60)
      | ~ m1_subset_1(B_60,k1_zfmisc_1(A_61))
      | ~ v1_relat_1(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_130,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_119,c_127])).

tff(c_133,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_130])).

tff(c_74,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_66,plain,(
    v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_222,plain,(
    ! [A_78,B_79,C_80] :
      ( k2_relset_1(A_78,B_79,C_80) = k2_relat_1(C_80)
      | ~ m1_subset_1(C_80,k1_zfmisc_1(k2_zfmisc_1(A_78,B_79))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_230,plain,(
    k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_3'),'#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_119,c_222])).

tff(c_68,plain,(
    k2_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4') = k2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_122,plain,(
    k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_3'),'#skF_4') = k2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_96,c_68])).

tff(c_231,plain,(
    k2_struct_0('#skF_3') = k2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_230,c_122])).

tff(c_78,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_60,plain,(
    ! [A_36] :
      ( ~ v1_xboole_0(u1_struct_0(A_36))
      | ~ l1_struct_0(A_36)
      | v2_struct_0(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_103,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_3'))
    | ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_60])).

tff(c_107,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_3'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_103])).

tff(c_108,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_107])).

tff(c_241,plain,(
    ~ v1_xboole_0(k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_231,c_108])).

tff(c_152,plain,(
    ! [C_67,A_68,B_69] :
      ( v4_relat_1(C_67,A_68)
      | ~ m1_subset_1(C_67,k1_zfmisc_1(k2_zfmisc_1(A_68,B_69))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_161,plain,(
    v4_relat_1('#skF_4',k2_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_119,c_152])).

tff(c_180,plain,(
    ! [B_72,A_73] :
      ( k1_relat_1(B_72) = A_73
      | ~ v1_partfun1(B_72,A_73)
      | ~ v4_relat_1(B_72,A_73)
      | ~ v1_relat_1(B_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_183,plain,
    ( k2_struct_0('#skF_2') = k1_relat_1('#skF_4')
    | ~ v1_partfun1('#skF_4',k2_struct_0('#skF_2'))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_161,c_180])).

tff(c_189,plain,
    ( k2_struct_0('#skF_2') = k1_relat_1('#skF_4')
    | ~ v1_partfun1('#skF_4',k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_183])).

tff(c_205,plain,(
    ~ v1_partfun1('#skF_4',k2_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_189])).

tff(c_72,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_99,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_2'),k2_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_72])).

tff(c_121,plain,(
    v1_funct_2('#skF_4',k2_struct_0('#skF_2'),k2_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_99])).

tff(c_239,plain,(
    v1_funct_2('#skF_4',k2_struct_0('#skF_2'),k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_231,c_121])).

tff(c_240,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),k2_relat_1('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_231,c_119])).

tff(c_315,plain,(
    ! [C_85,A_86,B_87] :
      ( v1_partfun1(C_85,A_86)
      | ~ v1_funct_2(C_85,A_86,B_87)
      | ~ v1_funct_1(C_85)
      | ~ m1_subset_1(C_85,k1_zfmisc_1(k2_zfmisc_1(A_86,B_87)))
      | v1_xboole_0(B_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_318,plain,
    ( v1_partfun1('#skF_4',k2_struct_0('#skF_2'))
    | ~ v1_funct_2('#skF_4',k2_struct_0('#skF_2'),k2_relat_1('#skF_4'))
    | ~ v1_funct_1('#skF_4')
    | v1_xboole_0(k2_relat_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_240,c_315])).

tff(c_324,plain,
    ( v1_partfun1('#skF_4',k2_struct_0('#skF_2'))
    | v1_xboole_0(k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_239,c_318])).

tff(c_326,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_241,c_205,c_324])).

tff(c_327,plain,(
    k2_struct_0('#skF_2') = k1_relat_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_189])).

tff(c_349,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),k2_struct_0('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_327,c_119])).

tff(c_399,plain,(
    ! [A_91,B_92,C_93] :
      ( k2_relset_1(A_91,B_92,C_93) = k2_relat_1(C_93)
      | ~ m1_subset_1(C_93,k1_zfmisc_1(k2_zfmisc_1(A_91,B_92))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_406,plain,(
    k2_relset_1(k1_relat_1('#skF_4'),k2_struct_0('#skF_3'),'#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_349,c_399])).

tff(c_346,plain,(
    k2_relset_1(k1_relat_1('#skF_4'),k2_struct_0('#skF_3'),'#skF_4') = k2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_327,c_122])).

tff(c_408,plain,(
    k2_struct_0('#skF_3') = k2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_406,c_346])).

tff(c_347,plain,(
    v1_funct_2('#skF_4',k1_relat_1('#skF_4'),k2_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_327,c_121])).

tff(c_415,plain,(
    v1_funct_2('#skF_4',k1_relat_1('#skF_4'),k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_408,c_347])).

tff(c_414,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),k2_relat_1('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_408,c_349])).

tff(c_40,plain,(
    ! [A_25,B_26] : v1_funct_1('#skF_1'(A_25,B_26)) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_38,plain,(
    ! [A_25,B_26] : v1_funct_2('#skF_1'(A_25,B_26),A_25,B_26) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_48,plain,(
    ! [A_25,B_26] : m1_subset_1('#skF_1'(A_25,B_26),k1_zfmisc_1(k2_zfmisc_1(A_25,B_26))) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_747,plain,(
    ! [A_140,B_141,C_142,D_143] :
      ( r2_funct_2(A_140,B_141,C_142,C_142)
      | ~ m1_subset_1(D_143,k1_zfmisc_1(k2_zfmisc_1(A_140,B_141)))
      | ~ v1_funct_2(D_143,A_140,B_141)
      | ~ v1_funct_1(D_143)
      | ~ m1_subset_1(C_142,k1_zfmisc_1(k2_zfmisc_1(A_140,B_141)))
      | ~ v1_funct_2(C_142,A_140,B_141)
      | ~ v1_funct_1(C_142) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_753,plain,(
    ! [A_25,B_26,C_142] :
      ( r2_funct_2(A_25,B_26,C_142,C_142)
      | ~ v1_funct_2('#skF_1'(A_25,B_26),A_25,B_26)
      | ~ v1_funct_1('#skF_1'(A_25,B_26))
      | ~ m1_subset_1(C_142,k1_zfmisc_1(k2_zfmisc_1(A_25,B_26)))
      | ~ v1_funct_2(C_142,A_25,B_26)
      | ~ v1_funct_1(C_142) ) ),
    inference(resolution,[status(thm)],[c_48,c_747])).

tff(c_761,plain,(
    ! [A_144,B_145,C_146] :
      ( r2_funct_2(A_144,B_145,C_146,C_146)
      | ~ m1_subset_1(C_146,k1_zfmisc_1(k2_zfmisc_1(A_144,B_145)))
      | ~ v1_funct_2(C_146,A_144,B_145)
      | ~ v1_funct_1(C_146) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_753])).

tff(c_765,plain,
    ( r2_funct_2(k1_relat_1('#skF_4'),k2_relat_1('#skF_4'),'#skF_4','#skF_4')
    | ~ v1_funct_2('#skF_4',k1_relat_1('#skF_4'),k2_relat_1('#skF_4'))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_414,c_761])).

tff(c_771,plain,(
    r2_funct_2(k1_relat_1('#skF_4'),k2_relat_1('#skF_4'),'#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_415,c_765])).

tff(c_22,plain,(
    ! [A_12] :
      ( k2_funct_1(k2_funct_1(A_12)) = A_12
      | ~ v2_funct_1(A_12)
      | ~ v1_funct_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_413,plain,(
    k2_relset_1(k1_relat_1('#skF_4'),k2_relat_1('#skF_4'),'#skF_4') = k2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_408,c_406])).

tff(c_555,plain,(
    ! [C_112,A_113,B_114] :
      ( v1_funct_1(k2_funct_1(C_112))
      | k2_relset_1(A_113,B_114,C_112) != B_114
      | ~ v2_funct_1(C_112)
      | ~ m1_subset_1(C_112,k1_zfmisc_1(k2_zfmisc_1(A_113,B_114)))
      | ~ v1_funct_2(C_112,A_113,B_114)
      | ~ v1_funct_1(C_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_558,plain,
    ( v1_funct_1(k2_funct_1('#skF_4'))
    | k2_relset_1(k1_relat_1('#skF_4'),k2_relat_1('#skF_4'),'#skF_4') != k2_relat_1('#skF_4')
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_2('#skF_4',k1_relat_1('#skF_4'),k2_relat_1('#skF_4'))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_414,c_555])).

tff(c_564,plain,(
    v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_415,c_66,c_413,c_558])).

tff(c_569,plain,(
    ! [C_117,B_118,A_119] :
      ( v1_funct_2(k2_funct_1(C_117),B_118,A_119)
      | k2_relset_1(A_119,B_118,C_117) != B_118
      | ~ v2_funct_1(C_117)
      | ~ m1_subset_1(C_117,k1_zfmisc_1(k2_zfmisc_1(A_119,B_118)))
      | ~ v1_funct_2(C_117,A_119,B_118)
      | ~ v1_funct_1(C_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_572,plain,
    ( v1_funct_2(k2_funct_1('#skF_4'),k2_relat_1('#skF_4'),k1_relat_1('#skF_4'))
    | k2_relset_1(k1_relat_1('#skF_4'),k2_relat_1('#skF_4'),'#skF_4') != k2_relat_1('#skF_4')
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_2('#skF_4',k1_relat_1('#skF_4'),k2_relat_1('#skF_4'))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_414,c_569])).

tff(c_578,plain,(
    v1_funct_2(k2_funct_1('#skF_4'),k2_relat_1('#skF_4'),k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_415,c_66,c_413,c_572])).

tff(c_14,plain,(
    ! [A_10] :
      ( k2_relat_1(k2_funct_1(A_10)) = k1_relat_1(A_10)
      | ~ v2_funct_1(A_10)
      | ~ v1_funct_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_659,plain,(
    ! [C_130,B_131,A_132] :
      ( m1_subset_1(k2_funct_1(C_130),k1_zfmisc_1(k2_zfmisc_1(B_131,A_132)))
      | k2_relset_1(A_132,B_131,C_130) != B_131
      | ~ v2_funct_1(C_130)
      | ~ m1_subset_1(C_130,k1_zfmisc_1(k2_zfmisc_1(A_132,B_131)))
      | ~ v1_funct_2(C_130,A_132,B_131)
      | ~ v1_funct_1(C_130) ) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_2,plain,(
    ! [B_3,A_1] :
      ( v1_relat_1(B_3)
      | ~ m1_subset_1(B_3,k1_zfmisc_1(A_1))
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_683,plain,(
    ! [C_130,B_131,A_132] :
      ( v1_relat_1(k2_funct_1(C_130))
      | ~ v1_relat_1(k2_zfmisc_1(B_131,A_132))
      | k2_relset_1(A_132,B_131,C_130) != B_131
      | ~ v2_funct_1(C_130)
      | ~ m1_subset_1(C_130,k1_zfmisc_1(k2_zfmisc_1(A_132,B_131)))
      | ~ v1_funct_2(C_130,A_132,B_131)
      | ~ v1_funct_1(C_130) ) ),
    inference(resolution,[status(thm)],[c_659,c_2])).

tff(c_729,plain,(
    ! [C_135,A_136,B_137] :
      ( v1_relat_1(k2_funct_1(C_135))
      | k2_relset_1(A_136,B_137,C_135) != B_137
      | ~ v2_funct_1(C_135)
      | ~ m1_subset_1(C_135,k1_zfmisc_1(k2_zfmisc_1(A_136,B_137)))
      | ~ v1_funct_2(C_135,A_136,B_137)
      | ~ v1_funct_1(C_135) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_683])).

tff(c_735,plain,
    ( v1_relat_1(k2_funct_1('#skF_4'))
    | k2_relset_1(k1_relat_1('#skF_4'),k2_relat_1('#skF_4'),'#skF_4') != k2_relat_1('#skF_4')
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_2('#skF_4',k1_relat_1('#skF_4'),k2_relat_1('#skF_4'))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_414,c_729])).

tff(c_742,plain,(
    v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_415,c_66,c_413,c_735])).

tff(c_26,plain,(
    ! [C_15,A_13,B_14] :
      ( v4_relat_1(C_15,A_13)
      | ~ m1_subset_1(C_15,k1_zfmisc_1(k2_zfmisc_1(A_13,B_14))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_776,plain,(
    ! [C_149,B_150,A_151] :
      ( v4_relat_1(k2_funct_1(C_149),B_150)
      | k2_relset_1(A_151,B_150,C_149) != B_150
      | ~ v2_funct_1(C_149)
      | ~ m1_subset_1(C_149,k1_zfmisc_1(k2_zfmisc_1(A_151,B_150)))
      | ~ v1_funct_2(C_149,A_151,B_150)
      | ~ v1_funct_1(C_149) ) ),
    inference(resolution,[status(thm)],[c_659,c_26])).

tff(c_782,plain,
    ( v4_relat_1(k2_funct_1('#skF_4'),k2_relat_1('#skF_4'))
    | k2_relset_1(k1_relat_1('#skF_4'),k2_relat_1('#skF_4'),'#skF_4') != k2_relat_1('#skF_4')
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_2('#skF_4',k1_relat_1('#skF_4'),k2_relat_1('#skF_4'))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_414,c_776])).

tff(c_789,plain,(
    v4_relat_1(k2_funct_1('#skF_4'),k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_415,c_66,c_413,c_782])).

tff(c_36,plain,(
    ! [B_24,A_23] :
      ( k1_relat_1(B_24) = A_23
      | ~ v1_partfun1(B_24,A_23)
      | ~ v4_relat_1(B_24,A_23)
      | ~ v1_relat_1(B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_795,plain,
    ( k1_relat_1(k2_funct_1('#skF_4')) = k2_relat_1('#skF_4')
    | ~ v1_partfun1(k2_funct_1('#skF_4'),k2_relat_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_789,c_36])).

tff(c_798,plain,
    ( k1_relat_1(k2_funct_1('#skF_4')) = k2_relat_1('#skF_4')
    | ~ v1_partfun1(k2_funct_1('#skF_4'),k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_742,c_795])).

tff(c_799,plain,(
    ~ v1_partfun1(k2_funct_1('#skF_4'),k2_relat_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_798])).

tff(c_16,plain,(
    ! [A_10] :
      ( k1_relat_1(k2_funct_1(A_10)) = k2_relat_1(A_10)
      | ~ v2_funct_1(A_10)
      | ~ v1_funct_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_329,plain,(
    ! [A_88] :
      ( k1_relat_1(k2_funct_1(A_88)) = k2_relat_1(A_88)
      | ~ v2_funct_1(A_88)
      | ~ v1_funct_1(A_88)
      | ~ v1_relat_1(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_34,plain,(
    ! [B_24] :
      ( v1_partfun1(B_24,k1_relat_1(B_24))
      | ~ v4_relat_1(B_24,k1_relat_1(B_24))
      | ~ v1_relat_1(B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_583,plain,(
    ! [A_122] :
      ( v1_partfun1(k2_funct_1(A_122),k1_relat_1(k2_funct_1(A_122)))
      | ~ v4_relat_1(k2_funct_1(A_122),k2_relat_1(A_122))
      | ~ v1_relat_1(k2_funct_1(A_122))
      | ~ v2_funct_1(A_122)
      | ~ v1_funct_1(A_122)
      | ~ v1_relat_1(A_122) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_329,c_34])).

tff(c_898,plain,(
    ! [A_162] :
      ( v1_partfun1(k2_funct_1(A_162),k2_relat_1(A_162))
      | ~ v4_relat_1(k2_funct_1(A_162),k2_relat_1(A_162))
      | ~ v1_relat_1(k2_funct_1(A_162))
      | ~ v2_funct_1(A_162)
      | ~ v1_funct_1(A_162)
      | ~ v1_relat_1(A_162)
      | ~ v2_funct_1(A_162)
      | ~ v1_funct_1(A_162)
      | ~ v1_relat_1(A_162) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_583])).

tff(c_901,plain,
    ( v1_partfun1(k2_funct_1('#skF_4'),k2_relat_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_789,c_898])).

tff(c_910,plain,(
    v1_partfun1(k2_funct_1('#skF_4'),k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_74,c_66,c_742,c_901])).

tff(c_912,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_799,c_910])).

tff(c_913,plain,(
    k1_relat_1(k2_funct_1('#skF_4')) = k2_relat_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_798])).

tff(c_8,plain,(
    ! [A_6] : v2_funct_1(k6_relat_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_20,plain,(
    ! [A_11] :
      ( k5_relat_1(A_11,k2_funct_1(A_11)) = k6_relat_1(k1_relat_1(A_11))
      | ~ v2_funct_1(A_11)
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_540,plain,(
    ! [A_109,B_110] :
      ( v2_funct_1(A_109)
      | k2_relat_1(B_110) != k1_relat_1(A_109)
      | ~ v2_funct_1(k5_relat_1(B_110,A_109))
      | ~ v1_funct_1(B_110)
      | ~ v1_relat_1(B_110)
      | ~ v1_funct_1(A_109)
      | ~ v1_relat_1(A_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_543,plain,(
    ! [A_11] :
      ( v2_funct_1(k2_funct_1(A_11))
      | k1_relat_1(k2_funct_1(A_11)) != k2_relat_1(A_11)
      | ~ v2_funct_1(k6_relat_1(k1_relat_1(A_11)))
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11)
      | ~ v1_funct_1(k2_funct_1(A_11))
      | ~ v1_relat_1(k2_funct_1(A_11))
      | ~ v2_funct_1(A_11)
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_540])).

tff(c_548,plain,(
    ! [A_11] :
      ( v2_funct_1(k2_funct_1(A_11))
      | k1_relat_1(k2_funct_1(A_11)) != k2_relat_1(A_11)
      | ~ v1_funct_1(k2_funct_1(A_11))
      | ~ v1_relat_1(k2_funct_1(A_11))
      | ~ v2_funct_1(A_11)
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_543])).

tff(c_479,plain,(
    ! [A_97] :
      ( k5_relat_1(A_97,k2_funct_1(A_97)) = k6_relat_1(k1_relat_1(A_97))
      | ~ v2_funct_1(A_97)
      | ~ v1_funct_1(A_97)
      | ~ v1_relat_1(A_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_942,plain,(
    ! [A_163] :
      ( k6_relat_1(k1_relat_1(k2_funct_1(A_163))) = k5_relat_1(k2_funct_1(A_163),A_163)
      | ~ v2_funct_1(k2_funct_1(A_163))
      | ~ v1_funct_1(k2_funct_1(A_163))
      | ~ v1_relat_1(k2_funct_1(A_163))
      | ~ v2_funct_1(A_163)
      | ~ v1_funct_1(A_163)
      | ~ v1_relat_1(A_163) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_479])).

tff(c_970,plain,
    ( k5_relat_1(k2_funct_1('#skF_4'),'#skF_4') = k6_relat_1(k2_relat_1('#skF_4'))
    | ~ v2_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_913,c_942])).

tff(c_989,plain,
    ( k5_relat_1(k2_funct_1('#skF_4'),'#skF_4') = k6_relat_1(k2_relat_1('#skF_4'))
    | ~ v2_funct_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_74,c_66,c_742,c_564,c_970])).

tff(c_991,plain,(
    ~ v2_funct_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_989])).

tff(c_994,plain,
    ( k1_relat_1(k2_funct_1('#skF_4')) != k2_relat_1('#skF_4')
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_548,c_991])).

tff(c_1001,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_74,c_66,c_742,c_564,c_913,c_994])).

tff(c_1003,plain,(
    v2_funct_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_989])).

tff(c_28,plain,(
    ! [A_16,B_17,C_18] :
      ( k2_relset_1(A_16,B_17,C_18) = k2_relat_1(C_18)
      | ~ m1_subset_1(C_18,k1_zfmisc_1(k2_zfmisc_1(A_16,B_17))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_1094,plain,(
    ! [B_171,A_172,C_173] :
      ( k2_relset_1(B_171,A_172,k2_funct_1(C_173)) = k2_relat_1(k2_funct_1(C_173))
      | k2_relset_1(A_172,B_171,C_173) != B_171
      | ~ v2_funct_1(C_173)
      | ~ m1_subset_1(C_173,k1_zfmisc_1(k2_zfmisc_1(A_172,B_171)))
      | ~ v1_funct_2(C_173,A_172,B_171)
      | ~ v1_funct_1(C_173) ) ),
    inference(resolution,[status(thm)],[c_659,c_28])).

tff(c_1100,plain,
    ( k2_relset_1(k2_relat_1('#skF_4'),k1_relat_1('#skF_4'),k2_funct_1('#skF_4')) = k2_relat_1(k2_funct_1('#skF_4'))
    | k2_relset_1(k1_relat_1('#skF_4'),k2_relat_1('#skF_4'),'#skF_4') != k2_relat_1('#skF_4')
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_2('#skF_4',k1_relat_1('#skF_4'),k2_relat_1('#skF_4'))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_414,c_1094])).

tff(c_1107,plain,(
    k2_relset_1(k2_relat_1('#skF_4'),k1_relat_1('#skF_4'),k2_funct_1('#skF_4')) = k2_relat_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_415,c_66,c_413,c_1100])).

tff(c_56,plain,(
    ! [C_34,A_32,B_33] :
      ( v1_funct_1(k2_funct_1(C_34))
      | k2_relset_1(A_32,B_33,C_34) != B_33
      | ~ v2_funct_1(C_34)
      | ~ m1_subset_1(C_34,k1_zfmisc_1(k2_zfmisc_1(A_32,B_33)))
      | ~ v1_funct_2(C_34,A_32,B_33)
      | ~ v1_funct_1(C_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_1497,plain,(
    ! [C_215,B_216,A_217] :
      ( v1_funct_1(k2_funct_1(k2_funct_1(C_215)))
      | k2_relset_1(B_216,A_217,k2_funct_1(C_215)) != A_217
      | ~ v2_funct_1(k2_funct_1(C_215))
      | ~ v1_funct_2(k2_funct_1(C_215),B_216,A_217)
      | ~ v1_funct_1(k2_funct_1(C_215))
      | k2_relset_1(A_217,B_216,C_215) != B_216
      | ~ v2_funct_1(C_215)
      | ~ m1_subset_1(C_215,k1_zfmisc_1(k2_zfmisc_1(A_217,B_216)))
      | ~ v1_funct_2(C_215,A_217,B_216)
      | ~ v1_funct_1(C_215) ) ),
    inference(resolution,[status(thm)],[c_659,c_56])).

tff(c_1503,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1('#skF_4')))
    | k2_relset_1(k2_relat_1('#skF_4'),k1_relat_1('#skF_4'),k2_funct_1('#skF_4')) != k1_relat_1('#skF_4')
    | ~ v2_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_funct_2(k2_funct_1('#skF_4'),k2_relat_1('#skF_4'),k1_relat_1('#skF_4'))
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | k2_relset_1(k1_relat_1('#skF_4'),k2_relat_1('#skF_4'),'#skF_4') != k2_relat_1('#skF_4')
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_2('#skF_4',k1_relat_1('#skF_4'),k2_relat_1('#skF_4'))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_414,c_1497])).

tff(c_1510,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1('#skF_4')))
    | k2_relat_1(k2_funct_1('#skF_4')) != k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_415,c_66,c_413,c_564,c_578,c_1003,c_1107,c_1503])).

tff(c_1514,plain,(
    k2_relat_1(k2_funct_1('#skF_4')) != k1_relat_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1510])).

tff(c_1517,plain,
    ( ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_1514])).

tff(c_1521,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_74,c_66,c_1517])).

tff(c_1523,plain,(
    k2_relat_1(k2_funct_1('#skF_4')) = k1_relat_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_1510])).

tff(c_1529,plain,(
    k2_relset_1(k2_relat_1('#skF_4'),k1_relat_1('#skF_4'),k2_funct_1('#skF_4')) = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1523,c_1107])).

tff(c_62,plain,(
    ! [A_37,B_38,C_39] :
      ( k2_tops_2(A_37,B_38,C_39) = k2_funct_1(C_39)
      | ~ v2_funct_1(C_39)
      | k2_relset_1(A_37,B_38,C_39) != B_38
      | ~ m1_subset_1(C_39,k1_zfmisc_1(k2_zfmisc_1(A_37,B_38)))
      | ~ v1_funct_2(C_39,A_37,B_38)
      | ~ v1_funct_1(C_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_1687,plain,(
    ! [B_221,A_222,C_223] :
      ( k2_tops_2(B_221,A_222,k2_funct_1(C_223)) = k2_funct_1(k2_funct_1(C_223))
      | ~ v2_funct_1(k2_funct_1(C_223))
      | k2_relset_1(B_221,A_222,k2_funct_1(C_223)) != A_222
      | ~ v1_funct_2(k2_funct_1(C_223),B_221,A_222)
      | ~ v1_funct_1(k2_funct_1(C_223))
      | k2_relset_1(A_222,B_221,C_223) != B_221
      | ~ v2_funct_1(C_223)
      | ~ m1_subset_1(C_223,k1_zfmisc_1(k2_zfmisc_1(A_222,B_221)))
      | ~ v1_funct_2(C_223,A_222,B_221)
      | ~ v1_funct_1(C_223) ) ),
    inference(resolution,[status(thm)],[c_659,c_62])).

tff(c_1693,plain,
    ( k2_tops_2(k2_relat_1('#skF_4'),k1_relat_1('#skF_4'),k2_funct_1('#skF_4')) = k2_funct_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1(k2_funct_1('#skF_4'))
    | k2_relset_1(k2_relat_1('#skF_4'),k1_relat_1('#skF_4'),k2_funct_1('#skF_4')) != k1_relat_1('#skF_4')
    | ~ v1_funct_2(k2_funct_1('#skF_4'),k2_relat_1('#skF_4'),k1_relat_1('#skF_4'))
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | k2_relset_1(k1_relat_1('#skF_4'),k2_relat_1('#skF_4'),'#skF_4') != k2_relat_1('#skF_4')
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_2('#skF_4',k1_relat_1('#skF_4'),k2_relat_1('#skF_4'))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_414,c_1687])).

tff(c_1700,plain,(
    k2_tops_2(k2_relat_1('#skF_4'),k1_relat_1('#skF_4'),k2_funct_1('#skF_4')) = k2_funct_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_415,c_66,c_413,c_564,c_578,c_1529,c_1003,c_1693])).

tff(c_640,plain,(
    ! [A_125,B_126,C_127] :
      ( k2_tops_2(A_125,B_126,C_127) = k2_funct_1(C_127)
      | ~ v2_funct_1(C_127)
      | k2_relset_1(A_125,B_126,C_127) != B_126
      | ~ m1_subset_1(C_127,k1_zfmisc_1(k2_zfmisc_1(A_125,B_126)))
      | ~ v1_funct_2(C_127,A_125,B_126)
      | ~ v1_funct_1(C_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_643,plain,
    ( k2_tops_2(k1_relat_1('#skF_4'),k2_relat_1('#skF_4'),'#skF_4') = k2_funct_1('#skF_4')
    | ~ v2_funct_1('#skF_4')
    | k2_relset_1(k1_relat_1('#skF_4'),k2_relat_1('#skF_4'),'#skF_4') != k2_relat_1('#skF_4')
    | ~ v1_funct_2('#skF_4',k1_relat_1('#skF_4'),k2_relat_1('#skF_4'))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_414,c_640])).

tff(c_649,plain,(
    k2_tops_2(k1_relat_1('#skF_4'),k2_relat_1('#skF_4'),'#skF_4') = k2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_415,c_413,c_66,c_643])).

tff(c_64,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k2_tops_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4')),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_151,plain,(
    ~ r2_funct_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_3'),k2_tops_2(k2_struct_0('#skF_3'),k2_struct_0('#skF_2'),k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_3'),'#skF_4')),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_97,c_97,c_96,c_96,c_96,c_64])).

tff(c_345,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_4'),k2_struct_0('#skF_3'),k2_tops_2(k2_struct_0('#skF_3'),k1_relat_1('#skF_4'),k2_tops_2(k1_relat_1('#skF_4'),k2_struct_0('#skF_3'),'#skF_4')),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_327,c_327,c_327,c_151])).

tff(c_510,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_4'),k2_relat_1('#skF_4'),k2_tops_2(k2_relat_1('#skF_4'),k1_relat_1('#skF_4'),k2_tops_2(k1_relat_1('#skF_4'),k2_relat_1('#skF_4'),'#skF_4')),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_408,c_408,c_408,c_345])).

tff(c_653,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_4'),k2_relat_1('#skF_4'),k2_tops_2(k2_relat_1('#skF_4'),k1_relat_1('#skF_4'),k2_funct_1('#skF_4')),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_649,c_510])).

tff(c_1751,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_4'),k2_relat_1('#skF_4'),k2_funct_1(k2_funct_1('#skF_4')),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1700,c_653])).

tff(c_1758,plain,
    ( ~ r2_funct_2(k1_relat_1('#skF_4'),k2_relat_1('#skF_4'),'#skF_4','#skF_4')
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_1751])).

tff(c_1761,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_74,c_66,c_771,c_1758])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:39:57 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.57/1.78  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.57/1.79  
% 4.57/1.79  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.57/1.79  %$ r2_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k2_tops_2 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k6_relat_1 > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 4.57/1.79  
% 4.57/1.79  %Foreground sorts:
% 4.57/1.79  
% 4.57/1.79  
% 4.57/1.79  %Background operators:
% 4.57/1.79  
% 4.57/1.79  
% 4.57/1.79  %Foreground operators:
% 4.57/1.79  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.57/1.79  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.57/1.79  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.57/1.79  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 4.57/1.79  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 4.57/1.79  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.57/1.79  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 4.57/1.79  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.57/1.79  tff(k2_tops_2, type, k2_tops_2: ($i * $i * $i) > $i).
% 4.57/1.79  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.57/1.79  tff('#skF_2', type, '#skF_2': $i).
% 4.57/1.79  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 4.57/1.79  tff('#skF_3', type, '#skF_3': $i).
% 4.57/1.79  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.57/1.79  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.57/1.79  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 4.57/1.79  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.57/1.79  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.57/1.79  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.57/1.79  tff('#skF_4', type, '#skF_4': $i).
% 4.57/1.79  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 4.57/1.79  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.57/1.79  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.57/1.79  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.57/1.79  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.57/1.79  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 4.57/1.79  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.57/1.79  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.57/1.79  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 4.57/1.79  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.57/1.79  
% 4.81/1.82  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 4.81/1.82  tff(f_204, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: ((~v2_struct_0(B) & l1_struct_0(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B)) & v2_funct_1(C)) => r2_funct_2(u1_struct_0(A), u1_struct_0(B), k2_tops_2(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)), C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_tops_2)).
% 4.81/1.82  tff(f_162, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 4.81/1.82  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 4.81/1.82  tff(f_93, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 4.81/1.82  tff(f_170, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 4.81/1.82  tff(f_89, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.81/1.82  tff(f_115, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_partfun1)).
% 4.81/1.82  tff(f_107, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc5_funct_2)).
% 4.81/1.82  tff(f_128, axiom, (![A, B]: (?[C]: (((((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & v1_relat_1(C)) & v4_relat_1(C, A)) & v5_relat_1(C, B)) & v1_funct_1(C)) & v1_funct_2(C, A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc1_funct_2)).
% 4.81/1.82  tff(f_142, axiom, (![A, B, C, D]: ((((((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(D)) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_funct_2(A, B, C, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', reflexivity_r2_funct_2)).
% 4.81/1.82  tff(f_83, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(k2_funct_1(A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_1)).
% 4.81/1.82  tff(f_158, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_funct_2)).
% 4.81/1.82  tff(f_65, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 4.81/1.82  tff(f_38, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_funct_1)).
% 4.81/1.82  tff(f_75, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_funct_1)).
% 4.81/1.82  tff(f_55, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v2_funct_1(k5_relat_1(B, A)) & (k2_relat_1(B) = k1_relat_1(A))) => (v2_funct_1(B) & v2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_funct_1)).
% 4.81/1.82  tff(f_182, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => (k2_tops_2(A, B, C) = k2_funct_1(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tops_2)).
% 4.81/1.82  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.81/1.82  tff(c_80, plain, (l1_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_204])).
% 4.81/1.82  tff(c_89, plain, (![A_58]: (u1_struct_0(A_58)=k2_struct_0(A_58) | ~l1_struct_0(A_58))), inference(cnfTransformation, [status(thm)], [f_162])).
% 4.81/1.82  tff(c_97, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_80, c_89])).
% 4.81/1.82  tff(c_76, plain, (l1_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_204])).
% 4.81/1.82  tff(c_96, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_76, c_89])).
% 4.81/1.82  tff(c_70, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_204])).
% 4.81/1.82  tff(c_119, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_97, c_96, c_70])).
% 4.81/1.82  tff(c_127, plain, (![B_60, A_61]: (v1_relat_1(B_60) | ~m1_subset_1(B_60, k1_zfmisc_1(A_61)) | ~v1_relat_1(A_61))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.81/1.82  tff(c_130, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_119, c_127])).
% 4.81/1.82  tff(c_133, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_130])).
% 4.81/1.82  tff(c_74, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_204])).
% 4.81/1.82  tff(c_66, plain, (v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_204])).
% 4.81/1.82  tff(c_222, plain, (![A_78, B_79, C_80]: (k2_relset_1(A_78, B_79, C_80)=k2_relat_1(C_80) | ~m1_subset_1(C_80, k1_zfmisc_1(k2_zfmisc_1(A_78, B_79))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 4.81/1.82  tff(c_230, plain, (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_3'), '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_119, c_222])).
% 4.81/1.82  tff(c_68, plain, (k2_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4')=k2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_204])).
% 4.81/1.82  tff(c_122, plain, (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_3'), '#skF_4')=k2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_97, c_96, c_68])).
% 4.81/1.82  tff(c_231, plain, (k2_struct_0('#skF_3')=k2_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_230, c_122])).
% 4.81/1.82  tff(c_78, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_204])).
% 4.81/1.82  tff(c_60, plain, (![A_36]: (~v1_xboole_0(u1_struct_0(A_36)) | ~l1_struct_0(A_36) | v2_struct_0(A_36))), inference(cnfTransformation, [status(thm)], [f_170])).
% 4.81/1.82  tff(c_103, plain, (~v1_xboole_0(k2_struct_0('#skF_3')) | ~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_96, c_60])).
% 4.81/1.82  tff(c_107, plain, (~v1_xboole_0(k2_struct_0('#skF_3')) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_103])).
% 4.81/1.82  tff(c_108, plain, (~v1_xboole_0(k2_struct_0('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_78, c_107])).
% 4.81/1.82  tff(c_241, plain, (~v1_xboole_0(k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_231, c_108])).
% 4.81/1.82  tff(c_152, plain, (![C_67, A_68, B_69]: (v4_relat_1(C_67, A_68) | ~m1_subset_1(C_67, k1_zfmisc_1(k2_zfmisc_1(A_68, B_69))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.81/1.82  tff(c_161, plain, (v4_relat_1('#skF_4', k2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_119, c_152])).
% 4.81/1.82  tff(c_180, plain, (![B_72, A_73]: (k1_relat_1(B_72)=A_73 | ~v1_partfun1(B_72, A_73) | ~v4_relat_1(B_72, A_73) | ~v1_relat_1(B_72))), inference(cnfTransformation, [status(thm)], [f_115])).
% 4.81/1.82  tff(c_183, plain, (k2_struct_0('#skF_2')=k1_relat_1('#skF_4') | ~v1_partfun1('#skF_4', k2_struct_0('#skF_2')) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_161, c_180])).
% 4.81/1.82  tff(c_189, plain, (k2_struct_0('#skF_2')=k1_relat_1('#skF_4') | ~v1_partfun1('#skF_4', k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_133, c_183])).
% 4.81/1.82  tff(c_205, plain, (~v1_partfun1('#skF_4', k2_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_189])).
% 4.81/1.82  tff(c_72, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_204])).
% 4.81/1.82  tff(c_99, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_2'), k2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_72])).
% 4.81/1.82  tff(c_121, plain, (v1_funct_2('#skF_4', k2_struct_0('#skF_2'), k2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_97, c_99])).
% 4.81/1.82  tff(c_239, plain, (v1_funct_2('#skF_4', k2_struct_0('#skF_2'), k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_231, c_121])).
% 4.81/1.82  tff(c_240, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), k2_relat_1('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_231, c_119])).
% 4.81/1.82  tff(c_315, plain, (![C_85, A_86, B_87]: (v1_partfun1(C_85, A_86) | ~v1_funct_2(C_85, A_86, B_87) | ~v1_funct_1(C_85) | ~m1_subset_1(C_85, k1_zfmisc_1(k2_zfmisc_1(A_86, B_87))) | v1_xboole_0(B_87))), inference(cnfTransformation, [status(thm)], [f_107])).
% 4.81/1.82  tff(c_318, plain, (v1_partfun1('#skF_4', k2_struct_0('#skF_2')) | ~v1_funct_2('#skF_4', k2_struct_0('#skF_2'), k2_relat_1('#skF_4')) | ~v1_funct_1('#skF_4') | v1_xboole_0(k2_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_240, c_315])).
% 4.81/1.82  tff(c_324, plain, (v1_partfun1('#skF_4', k2_struct_0('#skF_2')) | v1_xboole_0(k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_239, c_318])).
% 4.81/1.82  tff(c_326, plain, $false, inference(negUnitSimplification, [status(thm)], [c_241, c_205, c_324])).
% 4.81/1.82  tff(c_327, plain, (k2_struct_0('#skF_2')=k1_relat_1('#skF_4')), inference(splitRight, [status(thm)], [c_189])).
% 4.81/1.82  tff(c_349, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), k2_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_327, c_119])).
% 4.81/1.82  tff(c_399, plain, (![A_91, B_92, C_93]: (k2_relset_1(A_91, B_92, C_93)=k2_relat_1(C_93) | ~m1_subset_1(C_93, k1_zfmisc_1(k2_zfmisc_1(A_91, B_92))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 4.81/1.82  tff(c_406, plain, (k2_relset_1(k1_relat_1('#skF_4'), k2_struct_0('#skF_3'), '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_349, c_399])).
% 4.81/1.82  tff(c_346, plain, (k2_relset_1(k1_relat_1('#skF_4'), k2_struct_0('#skF_3'), '#skF_4')=k2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_327, c_122])).
% 4.81/1.82  tff(c_408, plain, (k2_struct_0('#skF_3')=k2_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_406, c_346])).
% 4.81/1.82  tff(c_347, plain, (v1_funct_2('#skF_4', k1_relat_1('#skF_4'), k2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_327, c_121])).
% 4.81/1.82  tff(c_415, plain, (v1_funct_2('#skF_4', k1_relat_1('#skF_4'), k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_408, c_347])).
% 4.81/1.82  tff(c_414, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), k2_relat_1('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_408, c_349])).
% 4.81/1.82  tff(c_40, plain, (![A_25, B_26]: (v1_funct_1('#skF_1'(A_25, B_26)))), inference(cnfTransformation, [status(thm)], [f_128])).
% 4.81/1.82  tff(c_38, plain, (![A_25, B_26]: (v1_funct_2('#skF_1'(A_25, B_26), A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_128])).
% 4.81/1.82  tff(c_48, plain, (![A_25, B_26]: (m1_subset_1('#skF_1'(A_25, B_26), k1_zfmisc_1(k2_zfmisc_1(A_25, B_26))))), inference(cnfTransformation, [status(thm)], [f_128])).
% 4.81/1.82  tff(c_747, plain, (![A_140, B_141, C_142, D_143]: (r2_funct_2(A_140, B_141, C_142, C_142) | ~m1_subset_1(D_143, k1_zfmisc_1(k2_zfmisc_1(A_140, B_141))) | ~v1_funct_2(D_143, A_140, B_141) | ~v1_funct_1(D_143) | ~m1_subset_1(C_142, k1_zfmisc_1(k2_zfmisc_1(A_140, B_141))) | ~v1_funct_2(C_142, A_140, B_141) | ~v1_funct_1(C_142))), inference(cnfTransformation, [status(thm)], [f_142])).
% 4.81/1.82  tff(c_753, plain, (![A_25, B_26, C_142]: (r2_funct_2(A_25, B_26, C_142, C_142) | ~v1_funct_2('#skF_1'(A_25, B_26), A_25, B_26) | ~v1_funct_1('#skF_1'(A_25, B_26)) | ~m1_subset_1(C_142, k1_zfmisc_1(k2_zfmisc_1(A_25, B_26))) | ~v1_funct_2(C_142, A_25, B_26) | ~v1_funct_1(C_142))), inference(resolution, [status(thm)], [c_48, c_747])).
% 4.81/1.82  tff(c_761, plain, (![A_144, B_145, C_146]: (r2_funct_2(A_144, B_145, C_146, C_146) | ~m1_subset_1(C_146, k1_zfmisc_1(k2_zfmisc_1(A_144, B_145))) | ~v1_funct_2(C_146, A_144, B_145) | ~v1_funct_1(C_146))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_753])).
% 4.81/1.82  tff(c_765, plain, (r2_funct_2(k1_relat_1('#skF_4'), k2_relat_1('#skF_4'), '#skF_4', '#skF_4') | ~v1_funct_2('#skF_4', k1_relat_1('#skF_4'), k2_relat_1('#skF_4')) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_414, c_761])).
% 4.81/1.82  tff(c_771, plain, (r2_funct_2(k1_relat_1('#skF_4'), k2_relat_1('#skF_4'), '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_415, c_765])).
% 4.81/1.82  tff(c_22, plain, (![A_12]: (k2_funct_1(k2_funct_1(A_12))=A_12 | ~v2_funct_1(A_12) | ~v1_funct_1(A_12) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.81/1.82  tff(c_413, plain, (k2_relset_1(k1_relat_1('#skF_4'), k2_relat_1('#skF_4'), '#skF_4')=k2_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_408, c_406])).
% 4.81/1.82  tff(c_555, plain, (![C_112, A_113, B_114]: (v1_funct_1(k2_funct_1(C_112)) | k2_relset_1(A_113, B_114, C_112)!=B_114 | ~v2_funct_1(C_112) | ~m1_subset_1(C_112, k1_zfmisc_1(k2_zfmisc_1(A_113, B_114))) | ~v1_funct_2(C_112, A_113, B_114) | ~v1_funct_1(C_112))), inference(cnfTransformation, [status(thm)], [f_158])).
% 4.81/1.82  tff(c_558, plain, (v1_funct_1(k2_funct_1('#skF_4')) | k2_relset_1(k1_relat_1('#skF_4'), k2_relat_1('#skF_4'), '#skF_4')!=k2_relat_1('#skF_4') | ~v2_funct_1('#skF_4') | ~v1_funct_2('#skF_4', k1_relat_1('#skF_4'), k2_relat_1('#skF_4')) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_414, c_555])).
% 4.81/1.82  tff(c_564, plain, (v1_funct_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_415, c_66, c_413, c_558])).
% 4.81/1.82  tff(c_569, plain, (![C_117, B_118, A_119]: (v1_funct_2(k2_funct_1(C_117), B_118, A_119) | k2_relset_1(A_119, B_118, C_117)!=B_118 | ~v2_funct_1(C_117) | ~m1_subset_1(C_117, k1_zfmisc_1(k2_zfmisc_1(A_119, B_118))) | ~v1_funct_2(C_117, A_119, B_118) | ~v1_funct_1(C_117))), inference(cnfTransformation, [status(thm)], [f_158])).
% 4.81/1.82  tff(c_572, plain, (v1_funct_2(k2_funct_1('#skF_4'), k2_relat_1('#skF_4'), k1_relat_1('#skF_4')) | k2_relset_1(k1_relat_1('#skF_4'), k2_relat_1('#skF_4'), '#skF_4')!=k2_relat_1('#skF_4') | ~v2_funct_1('#skF_4') | ~v1_funct_2('#skF_4', k1_relat_1('#skF_4'), k2_relat_1('#skF_4')) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_414, c_569])).
% 4.81/1.82  tff(c_578, plain, (v1_funct_2(k2_funct_1('#skF_4'), k2_relat_1('#skF_4'), k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_415, c_66, c_413, c_572])).
% 4.81/1.82  tff(c_14, plain, (![A_10]: (k2_relat_1(k2_funct_1(A_10))=k1_relat_1(A_10) | ~v2_funct_1(A_10) | ~v1_funct_1(A_10) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.81/1.82  tff(c_659, plain, (![C_130, B_131, A_132]: (m1_subset_1(k2_funct_1(C_130), k1_zfmisc_1(k2_zfmisc_1(B_131, A_132))) | k2_relset_1(A_132, B_131, C_130)!=B_131 | ~v2_funct_1(C_130) | ~m1_subset_1(C_130, k1_zfmisc_1(k2_zfmisc_1(A_132, B_131))) | ~v1_funct_2(C_130, A_132, B_131) | ~v1_funct_1(C_130))), inference(cnfTransformation, [status(thm)], [f_158])).
% 4.81/1.82  tff(c_2, plain, (![B_3, A_1]: (v1_relat_1(B_3) | ~m1_subset_1(B_3, k1_zfmisc_1(A_1)) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.81/1.82  tff(c_683, plain, (![C_130, B_131, A_132]: (v1_relat_1(k2_funct_1(C_130)) | ~v1_relat_1(k2_zfmisc_1(B_131, A_132)) | k2_relset_1(A_132, B_131, C_130)!=B_131 | ~v2_funct_1(C_130) | ~m1_subset_1(C_130, k1_zfmisc_1(k2_zfmisc_1(A_132, B_131))) | ~v1_funct_2(C_130, A_132, B_131) | ~v1_funct_1(C_130))), inference(resolution, [status(thm)], [c_659, c_2])).
% 4.81/1.82  tff(c_729, plain, (![C_135, A_136, B_137]: (v1_relat_1(k2_funct_1(C_135)) | k2_relset_1(A_136, B_137, C_135)!=B_137 | ~v2_funct_1(C_135) | ~m1_subset_1(C_135, k1_zfmisc_1(k2_zfmisc_1(A_136, B_137))) | ~v1_funct_2(C_135, A_136, B_137) | ~v1_funct_1(C_135))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_683])).
% 4.81/1.82  tff(c_735, plain, (v1_relat_1(k2_funct_1('#skF_4')) | k2_relset_1(k1_relat_1('#skF_4'), k2_relat_1('#skF_4'), '#skF_4')!=k2_relat_1('#skF_4') | ~v2_funct_1('#skF_4') | ~v1_funct_2('#skF_4', k1_relat_1('#skF_4'), k2_relat_1('#skF_4')) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_414, c_729])).
% 4.81/1.82  tff(c_742, plain, (v1_relat_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_415, c_66, c_413, c_735])).
% 4.81/1.82  tff(c_26, plain, (![C_15, A_13, B_14]: (v4_relat_1(C_15, A_13) | ~m1_subset_1(C_15, k1_zfmisc_1(k2_zfmisc_1(A_13, B_14))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.81/1.82  tff(c_776, plain, (![C_149, B_150, A_151]: (v4_relat_1(k2_funct_1(C_149), B_150) | k2_relset_1(A_151, B_150, C_149)!=B_150 | ~v2_funct_1(C_149) | ~m1_subset_1(C_149, k1_zfmisc_1(k2_zfmisc_1(A_151, B_150))) | ~v1_funct_2(C_149, A_151, B_150) | ~v1_funct_1(C_149))), inference(resolution, [status(thm)], [c_659, c_26])).
% 4.81/1.82  tff(c_782, plain, (v4_relat_1(k2_funct_1('#skF_4'), k2_relat_1('#skF_4')) | k2_relset_1(k1_relat_1('#skF_4'), k2_relat_1('#skF_4'), '#skF_4')!=k2_relat_1('#skF_4') | ~v2_funct_1('#skF_4') | ~v1_funct_2('#skF_4', k1_relat_1('#skF_4'), k2_relat_1('#skF_4')) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_414, c_776])).
% 4.81/1.82  tff(c_789, plain, (v4_relat_1(k2_funct_1('#skF_4'), k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_415, c_66, c_413, c_782])).
% 4.81/1.82  tff(c_36, plain, (![B_24, A_23]: (k1_relat_1(B_24)=A_23 | ~v1_partfun1(B_24, A_23) | ~v4_relat_1(B_24, A_23) | ~v1_relat_1(B_24))), inference(cnfTransformation, [status(thm)], [f_115])).
% 4.81/1.82  tff(c_795, plain, (k1_relat_1(k2_funct_1('#skF_4'))=k2_relat_1('#skF_4') | ~v1_partfun1(k2_funct_1('#skF_4'), k2_relat_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_789, c_36])).
% 4.81/1.82  tff(c_798, plain, (k1_relat_1(k2_funct_1('#skF_4'))=k2_relat_1('#skF_4') | ~v1_partfun1(k2_funct_1('#skF_4'), k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_742, c_795])).
% 4.81/1.82  tff(c_799, plain, (~v1_partfun1(k2_funct_1('#skF_4'), k2_relat_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_798])).
% 4.81/1.82  tff(c_16, plain, (![A_10]: (k1_relat_1(k2_funct_1(A_10))=k2_relat_1(A_10) | ~v2_funct_1(A_10) | ~v1_funct_1(A_10) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.81/1.82  tff(c_329, plain, (![A_88]: (k1_relat_1(k2_funct_1(A_88))=k2_relat_1(A_88) | ~v2_funct_1(A_88) | ~v1_funct_1(A_88) | ~v1_relat_1(A_88))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.81/1.82  tff(c_34, plain, (![B_24]: (v1_partfun1(B_24, k1_relat_1(B_24)) | ~v4_relat_1(B_24, k1_relat_1(B_24)) | ~v1_relat_1(B_24))), inference(cnfTransformation, [status(thm)], [f_115])).
% 4.81/1.82  tff(c_583, plain, (![A_122]: (v1_partfun1(k2_funct_1(A_122), k1_relat_1(k2_funct_1(A_122))) | ~v4_relat_1(k2_funct_1(A_122), k2_relat_1(A_122)) | ~v1_relat_1(k2_funct_1(A_122)) | ~v2_funct_1(A_122) | ~v1_funct_1(A_122) | ~v1_relat_1(A_122))), inference(superposition, [status(thm), theory('equality')], [c_329, c_34])).
% 4.81/1.82  tff(c_898, plain, (![A_162]: (v1_partfun1(k2_funct_1(A_162), k2_relat_1(A_162)) | ~v4_relat_1(k2_funct_1(A_162), k2_relat_1(A_162)) | ~v1_relat_1(k2_funct_1(A_162)) | ~v2_funct_1(A_162) | ~v1_funct_1(A_162) | ~v1_relat_1(A_162) | ~v2_funct_1(A_162) | ~v1_funct_1(A_162) | ~v1_relat_1(A_162))), inference(superposition, [status(thm), theory('equality')], [c_16, c_583])).
% 4.81/1.82  tff(c_901, plain, (v1_partfun1(k2_funct_1('#skF_4'), k2_relat_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_789, c_898])).
% 4.81/1.82  tff(c_910, plain, (v1_partfun1(k2_funct_1('#skF_4'), k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_133, c_74, c_66, c_742, c_901])).
% 4.81/1.82  tff(c_912, plain, $false, inference(negUnitSimplification, [status(thm)], [c_799, c_910])).
% 4.81/1.82  tff(c_913, plain, (k1_relat_1(k2_funct_1('#skF_4'))=k2_relat_1('#skF_4')), inference(splitRight, [status(thm)], [c_798])).
% 4.81/1.82  tff(c_8, plain, (![A_6]: (v2_funct_1(k6_relat_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.81/1.82  tff(c_20, plain, (![A_11]: (k5_relat_1(A_11, k2_funct_1(A_11))=k6_relat_1(k1_relat_1(A_11)) | ~v2_funct_1(A_11) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.81/1.82  tff(c_540, plain, (![A_109, B_110]: (v2_funct_1(A_109) | k2_relat_1(B_110)!=k1_relat_1(A_109) | ~v2_funct_1(k5_relat_1(B_110, A_109)) | ~v1_funct_1(B_110) | ~v1_relat_1(B_110) | ~v1_funct_1(A_109) | ~v1_relat_1(A_109))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.81/1.82  tff(c_543, plain, (![A_11]: (v2_funct_1(k2_funct_1(A_11)) | k1_relat_1(k2_funct_1(A_11))!=k2_relat_1(A_11) | ~v2_funct_1(k6_relat_1(k1_relat_1(A_11))) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11) | ~v1_funct_1(k2_funct_1(A_11)) | ~v1_relat_1(k2_funct_1(A_11)) | ~v2_funct_1(A_11) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(superposition, [status(thm), theory('equality')], [c_20, c_540])).
% 4.81/1.82  tff(c_548, plain, (![A_11]: (v2_funct_1(k2_funct_1(A_11)) | k1_relat_1(k2_funct_1(A_11))!=k2_relat_1(A_11) | ~v1_funct_1(k2_funct_1(A_11)) | ~v1_relat_1(k2_funct_1(A_11)) | ~v2_funct_1(A_11) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_543])).
% 4.81/1.82  tff(c_479, plain, (![A_97]: (k5_relat_1(A_97, k2_funct_1(A_97))=k6_relat_1(k1_relat_1(A_97)) | ~v2_funct_1(A_97) | ~v1_funct_1(A_97) | ~v1_relat_1(A_97))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.81/1.82  tff(c_942, plain, (![A_163]: (k6_relat_1(k1_relat_1(k2_funct_1(A_163)))=k5_relat_1(k2_funct_1(A_163), A_163) | ~v2_funct_1(k2_funct_1(A_163)) | ~v1_funct_1(k2_funct_1(A_163)) | ~v1_relat_1(k2_funct_1(A_163)) | ~v2_funct_1(A_163) | ~v1_funct_1(A_163) | ~v1_relat_1(A_163))), inference(superposition, [status(thm), theory('equality')], [c_22, c_479])).
% 4.81/1.82  tff(c_970, plain, (k5_relat_1(k2_funct_1('#skF_4'), '#skF_4')=k6_relat_1(k2_relat_1('#skF_4')) | ~v2_funct_1(k2_funct_1('#skF_4')) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_913, c_942])).
% 4.81/1.82  tff(c_989, plain, (k5_relat_1(k2_funct_1('#skF_4'), '#skF_4')=k6_relat_1(k2_relat_1('#skF_4')) | ~v2_funct_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_133, c_74, c_66, c_742, c_564, c_970])).
% 4.81/1.82  tff(c_991, plain, (~v2_funct_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_989])).
% 4.81/1.82  tff(c_994, plain, (k1_relat_1(k2_funct_1('#skF_4'))!=k2_relat_1('#skF_4') | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_548, c_991])).
% 4.81/1.82  tff(c_1001, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_133, c_74, c_66, c_742, c_564, c_913, c_994])).
% 4.81/1.82  tff(c_1003, plain, (v2_funct_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_989])).
% 4.81/1.82  tff(c_28, plain, (![A_16, B_17, C_18]: (k2_relset_1(A_16, B_17, C_18)=k2_relat_1(C_18) | ~m1_subset_1(C_18, k1_zfmisc_1(k2_zfmisc_1(A_16, B_17))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 4.81/1.82  tff(c_1094, plain, (![B_171, A_172, C_173]: (k2_relset_1(B_171, A_172, k2_funct_1(C_173))=k2_relat_1(k2_funct_1(C_173)) | k2_relset_1(A_172, B_171, C_173)!=B_171 | ~v2_funct_1(C_173) | ~m1_subset_1(C_173, k1_zfmisc_1(k2_zfmisc_1(A_172, B_171))) | ~v1_funct_2(C_173, A_172, B_171) | ~v1_funct_1(C_173))), inference(resolution, [status(thm)], [c_659, c_28])).
% 4.81/1.82  tff(c_1100, plain, (k2_relset_1(k2_relat_1('#skF_4'), k1_relat_1('#skF_4'), k2_funct_1('#skF_4'))=k2_relat_1(k2_funct_1('#skF_4')) | k2_relset_1(k1_relat_1('#skF_4'), k2_relat_1('#skF_4'), '#skF_4')!=k2_relat_1('#skF_4') | ~v2_funct_1('#skF_4') | ~v1_funct_2('#skF_4', k1_relat_1('#skF_4'), k2_relat_1('#skF_4')) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_414, c_1094])).
% 4.81/1.82  tff(c_1107, plain, (k2_relset_1(k2_relat_1('#skF_4'), k1_relat_1('#skF_4'), k2_funct_1('#skF_4'))=k2_relat_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_415, c_66, c_413, c_1100])).
% 4.81/1.82  tff(c_56, plain, (![C_34, A_32, B_33]: (v1_funct_1(k2_funct_1(C_34)) | k2_relset_1(A_32, B_33, C_34)!=B_33 | ~v2_funct_1(C_34) | ~m1_subset_1(C_34, k1_zfmisc_1(k2_zfmisc_1(A_32, B_33))) | ~v1_funct_2(C_34, A_32, B_33) | ~v1_funct_1(C_34))), inference(cnfTransformation, [status(thm)], [f_158])).
% 4.81/1.82  tff(c_1497, plain, (![C_215, B_216, A_217]: (v1_funct_1(k2_funct_1(k2_funct_1(C_215))) | k2_relset_1(B_216, A_217, k2_funct_1(C_215))!=A_217 | ~v2_funct_1(k2_funct_1(C_215)) | ~v1_funct_2(k2_funct_1(C_215), B_216, A_217) | ~v1_funct_1(k2_funct_1(C_215)) | k2_relset_1(A_217, B_216, C_215)!=B_216 | ~v2_funct_1(C_215) | ~m1_subset_1(C_215, k1_zfmisc_1(k2_zfmisc_1(A_217, B_216))) | ~v1_funct_2(C_215, A_217, B_216) | ~v1_funct_1(C_215))), inference(resolution, [status(thm)], [c_659, c_56])).
% 4.81/1.82  tff(c_1503, plain, (v1_funct_1(k2_funct_1(k2_funct_1('#skF_4'))) | k2_relset_1(k2_relat_1('#skF_4'), k1_relat_1('#skF_4'), k2_funct_1('#skF_4'))!=k1_relat_1('#skF_4') | ~v2_funct_1(k2_funct_1('#skF_4')) | ~v1_funct_2(k2_funct_1('#skF_4'), k2_relat_1('#skF_4'), k1_relat_1('#skF_4')) | ~v1_funct_1(k2_funct_1('#skF_4')) | k2_relset_1(k1_relat_1('#skF_4'), k2_relat_1('#skF_4'), '#skF_4')!=k2_relat_1('#skF_4') | ~v2_funct_1('#skF_4') | ~v1_funct_2('#skF_4', k1_relat_1('#skF_4'), k2_relat_1('#skF_4')) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_414, c_1497])).
% 4.81/1.82  tff(c_1510, plain, (v1_funct_1(k2_funct_1(k2_funct_1('#skF_4'))) | k2_relat_1(k2_funct_1('#skF_4'))!=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_415, c_66, c_413, c_564, c_578, c_1003, c_1107, c_1503])).
% 4.81/1.82  tff(c_1514, plain, (k2_relat_1(k2_funct_1('#skF_4'))!=k1_relat_1('#skF_4')), inference(splitLeft, [status(thm)], [c_1510])).
% 4.81/1.82  tff(c_1517, plain, (~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_14, c_1514])).
% 4.81/1.82  tff(c_1521, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_133, c_74, c_66, c_1517])).
% 4.81/1.82  tff(c_1523, plain, (k2_relat_1(k2_funct_1('#skF_4'))=k1_relat_1('#skF_4')), inference(splitRight, [status(thm)], [c_1510])).
% 4.81/1.82  tff(c_1529, plain, (k2_relset_1(k2_relat_1('#skF_4'), k1_relat_1('#skF_4'), k2_funct_1('#skF_4'))=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1523, c_1107])).
% 4.81/1.82  tff(c_62, plain, (![A_37, B_38, C_39]: (k2_tops_2(A_37, B_38, C_39)=k2_funct_1(C_39) | ~v2_funct_1(C_39) | k2_relset_1(A_37, B_38, C_39)!=B_38 | ~m1_subset_1(C_39, k1_zfmisc_1(k2_zfmisc_1(A_37, B_38))) | ~v1_funct_2(C_39, A_37, B_38) | ~v1_funct_1(C_39))), inference(cnfTransformation, [status(thm)], [f_182])).
% 4.81/1.82  tff(c_1687, plain, (![B_221, A_222, C_223]: (k2_tops_2(B_221, A_222, k2_funct_1(C_223))=k2_funct_1(k2_funct_1(C_223)) | ~v2_funct_1(k2_funct_1(C_223)) | k2_relset_1(B_221, A_222, k2_funct_1(C_223))!=A_222 | ~v1_funct_2(k2_funct_1(C_223), B_221, A_222) | ~v1_funct_1(k2_funct_1(C_223)) | k2_relset_1(A_222, B_221, C_223)!=B_221 | ~v2_funct_1(C_223) | ~m1_subset_1(C_223, k1_zfmisc_1(k2_zfmisc_1(A_222, B_221))) | ~v1_funct_2(C_223, A_222, B_221) | ~v1_funct_1(C_223))), inference(resolution, [status(thm)], [c_659, c_62])).
% 4.81/1.82  tff(c_1693, plain, (k2_tops_2(k2_relat_1('#skF_4'), k1_relat_1('#skF_4'), k2_funct_1('#skF_4'))=k2_funct_1(k2_funct_1('#skF_4')) | ~v2_funct_1(k2_funct_1('#skF_4')) | k2_relset_1(k2_relat_1('#skF_4'), k1_relat_1('#skF_4'), k2_funct_1('#skF_4'))!=k1_relat_1('#skF_4') | ~v1_funct_2(k2_funct_1('#skF_4'), k2_relat_1('#skF_4'), k1_relat_1('#skF_4')) | ~v1_funct_1(k2_funct_1('#skF_4')) | k2_relset_1(k1_relat_1('#skF_4'), k2_relat_1('#skF_4'), '#skF_4')!=k2_relat_1('#skF_4') | ~v2_funct_1('#skF_4') | ~v1_funct_2('#skF_4', k1_relat_1('#skF_4'), k2_relat_1('#skF_4')) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_414, c_1687])).
% 4.81/1.82  tff(c_1700, plain, (k2_tops_2(k2_relat_1('#skF_4'), k1_relat_1('#skF_4'), k2_funct_1('#skF_4'))=k2_funct_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_415, c_66, c_413, c_564, c_578, c_1529, c_1003, c_1693])).
% 4.81/1.82  tff(c_640, plain, (![A_125, B_126, C_127]: (k2_tops_2(A_125, B_126, C_127)=k2_funct_1(C_127) | ~v2_funct_1(C_127) | k2_relset_1(A_125, B_126, C_127)!=B_126 | ~m1_subset_1(C_127, k1_zfmisc_1(k2_zfmisc_1(A_125, B_126))) | ~v1_funct_2(C_127, A_125, B_126) | ~v1_funct_1(C_127))), inference(cnfTransformation, [status(thm)], [f_182])).
% 4.81/1.82  tff(c_643, plain, (k2_tops_2(k1_relat_1('#skF_4'), k2_relat_1('#skF_4'), '#skF_4')=k2_funct_1('#skF_4') | ~v2_funct_1('#skF_4') | k2_relset_1(k1_relat_1('#skF_4'), k2_relat_1('#skF_4'), '#skF_4')!=k2_relat_1('#skF_4') | ~v1_funct_2('#skF_4', k1_relat_1('#skF_4'), k2_relat_1('#skF_4')) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_414, c_640])).
% 4.81/1.82  tff(c_649, plain, (k2_tops_2(k1_relat_1('#skF_4'), k2_relat_1('#skF_4'), '#skF_4')=k2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_415, c_413, c_66, c_643])).
% 4.81/1.82  tff(c_64, plain, (~r2_funct_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), k2_tops_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k2_tops_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4')), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_204])).
% 4.81/1.82  tff(c_151, plain, (~r2_funct_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_3'), k2_tops_2(k2_struct_0('#skF_3'), k2_struct_0('#skF_2'), k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_3'), '#skF_4')), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_97, c_97, c_97, c_96, c_96, c_96, c_64])).
% 4.81/1.82  tff(c_345, plain, (~r2_funct_2(k1_relat_1('#skF_4'), k2_struct_0('#skF_3'), k2_tops_2(k2_struct_0('#skF_3'), k1_relat_1('#skF_4'), k2_tops_2(k1_relat_1('#skF_4'), k2_struct_0('#skF_3'), '#skF_4')), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_327, c_327, c_327, c_151])).
% 4.81/1.82  tff(c_510, plain, (~r2_funct_2(k1_relat_1('#skF_4'), k2_relat_1('#skF_4'), k2_tops_2(k2_relat_1('#skF_4'), k1_relat_1('#skF_4'), k2_tops_2(k1_relat_1('#skF_4'), k2_relat_1('#skF_4'), '#skF_4')), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_408, c_408, c_408, c_345])).
% 4.81/1.82  tff(c_653, plain, (~r2_funct_2(k1_relat_1('#skF_4'), k2_relat_1('#skF_4'), k2_tops_2(k2_relat_1('#skF_4'), k1_relat_1('#skF_4'), k2_funct_1('#skF_4')), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_649, c_510])).
% 4.81/1.82  tff(c_1751, plain, (~r2_funct_2(k1_relat_1('#skF_4'), k2_relat_1('#skF_4'), k2_funct_1(k2_funct_1('#skF_4')), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1700, c_653])).
% 4.81/1.82  tff(c_1758, plain, (~r2_funct_2(k1_relat_1('#skF_4'), k2_relat_1('#skF_4'), '#skF_4', '#skF_4') | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_22, c_1751])).
% 4.81/1.82  tff(c_1761, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_133, c_74, c_66, c_771, c_1758])).
% 4.81/1.82  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.81/1.82  
% 4.81/1.82  Inference rules
% 4.81/1.82  ----------------------
% 4.81/1.82  #Ref     : 0
% 4.81/1.82  #Sup     : 382
% 4.81/1.82  #Fact    : 0
% 4.81/1.82  #Define  : 0
% 4.81/1.82  #Split   : 8
% 4.81/1.82  #Chain   : 0
% 4.81/1.82  #Close   : 0
% 4.81/1.82  
% 4.81/1.82  Ordering : KBO
% 4.81/1.82  
% 4.81/1.82  Simplification rules
% 4.81/1.82  ----------------------
% 4.81/1.82  #Subsume      : 53
% 4.81/1.82  #Demod        : 490
% 4.81/1.82  #Tautology    : 193
% 4.81/1.82  #SimpNegUnit  : 7
% 4.81/1.82  #BackRed      : 27
% 4.81/1.82  
% 4.81/1.82  #Partial instantiations: 0
% 4.81/1.82  #Strategies tried      : 1
% 4.81/1.82  
% 4.81/1.82  Timing (in seconds)
% 4.81/1.82  ----------------------
% 4.81/1.82  Preprocessing        : 0.36
% 4.81/1.82  Parsing              : 0.19
% 4.81/1.82  CNF conversion       : 0.02
% 4.81/1.82  Main loop            : 0.68
% 4.81/1.82  Inferencing          : 0.24
% 4.81/1.82  Reduction            : 0.24
% 4.81/1.82  Demodulation         : 0.18
% 4.81/1.82  BG Simplification    : 0.03
% 4.81/1.82  Subsumption          : 0.11
% 4.81/1.82  Abstraction          : 0.03
% 4.81/1.82  MUC search           : 0.00
% 4.81/1.82  Cooper               : 0.00
% 4.81/1.82  Total                : 1.09
% 4.81/1.82  Index Insertion      : 0.00
% 4.81/1.82  Index Deletion       : 0.00
% 4.81/1.82  Index Matching       : 0.00
% 4.81/1.82  BG Taut test         : 0.00
%------------------------------------------------------------------------------
