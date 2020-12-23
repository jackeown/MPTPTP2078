%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:45 EST 2020

% Result     : Theorem 4.42s
% Output     : CNFRefutation 4.70s
% Verified   : 
% Statistics : Number of formulae       :  134 (13208 expanded)
%              Number of leaves         :   40 (4786 expanded)
%              Depth                    :   21
%              Number of atoms          :  361 (40165 expanded)
%              Number of equality atoms :   87 (10303 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_funct_2 > v1_funct_2 > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k2_tops_2 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k6_relat_1 > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

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

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(r2_funct_2,type,(
    r2_funct_2: ( $i * $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_34,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_180,negated_conjecture,(
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

tff(f_123,axiom,(
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

tff(f_87,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_119,axiom,(
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

tff(f_135,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( k2_relset_1(A,B,C) = B
          & v2_funct_1(C) )
       => k2_tops_2(A,B,C) = k2_funct_1(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_2)).

tff(f_158,axiom,(
    ! [A] :
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_tops_2)).

tff(f_65,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_103,axiom,(
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

tff(f_83,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(k2_funct_1(A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_1)).

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

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_60,plain,(
    l1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_64,plain,(
    ! [A_42] :
      ( u1_struct_0(A_42) = k2_struct_0(A_42)
      | ~ l1_struct_0(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_72,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_60,c_64])).

tff(c_56,plain,(
    l1_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_71,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_56,c_64])).

tff(c_50,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_88,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_71,c_50])).

tff(c_89,plain,(
    ! [B_43,A_44] :
      ( v1_relat_1(B_43)
      | ~ m1_subset_1(B_43,k1_zfmisc_1(A_44))
      | ~ v1_relat_1(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_92,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_88,c_89])).

tff(c_95,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_92])).

tff(c_54,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_46,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_138,plain,(
    ! [A_48,B_49,C_50] :
      ( k2_relset_1(A_48,B_49,C_50) = k2_relat_1(C_50)
      | ~ m1_subset_1(C_50,k1_zfmisc_1(k2_zfmisc_1(A_48,B_49))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_142,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_88,c_138])).

tff(c_48,plain,(
    k2_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_83,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_71,c_48])).

tff(c_143,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_83])).

tff(c_52,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_73,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_52])).

tff(c_82,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_73])).

tff(c_151,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_143,c_82])).

tff(c_150,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_143,c_88])).

tff(c_148,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_143,c_142])).

tff(c_380,plain,(
    ! [C_75,B_76,A_77] :
      ( m1_subset_1(k2_funct_1(C_75),k1_zfmisc_1(k2_zfmisc_1(B_76,A_77)))
      | k2_relset_1(A_77,B_76,C_75) != B_76
      | ~ v2_funct_1(C_75)
      | ~ m1_subset_1(C_75,k1_zfmisc_1(k2_zfmisc_1(A_77,B_76)))
      | ~ v1_funct_2(C_75,A_77,B_76)
      | ~ v1_funct_1(C_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_24,plain,(
    ! [A_13,B_14,C_15] :
      ( k2_relset_1(A_13,B_14,C_15) = k2_relat_1(C_15)
      | ~ m1_subset_1(C_15,k1_zfmisc_1(k2_zfmisc_1(A_13,B_14))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_452,plain,(
    ! [B_83,A_84,C_85] :
      ( k2_relset_1(B_83,A_84,k2_funct_1(C_85)) = k2_relat_1(k2_funct_1(C_85))
      | k2_relset_1(A_84,B_83,C_85) != B_83
      | ~ v2_funct_1(C_85)
      | ~ m1_subset_1(C_85,k1_zfmisc_1(k2_zfmisc_1(A_84,B_83)))
      | ~ v1_funct_2(C_85,A_84,B_83)
      | ~ v1_funct_1(C_85) ) ),
    inference(resolution,[status(thm)],[c_380,c_24])).

tff(c_458,plain,
    ( k2_relset_1(k2_relat_1('#skF_3'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_150,c_452])).

tff(c_462,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_151,c_46,c_148,c_458])).

tff(c_325,plain,(
    ! [A_71,B_72,C_73] :
      ( k2_tops_2(A_71,B_72,C_73) = k2_funct_1(C_73)
      | ~ v2_funct_1(C_73)
      | k2_relset_1(A_71,B_72,C_73) != B_72
      | ~ m1_subset_1(C_73,k1_zfmisc_1(k2_zfmisc_1(A_71,B_72)))
      | ~ v1_funct_2(C_73,A_71,B_72)
      | ~ v1_funct_1(C_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_328,plain,
    ( k2_tops_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_150,c_325])).

tff(c_331,plain,(
    k2_tops_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_151,c_148,c_46,c_328])).

tff(c_58,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_152,plain,(
    u1_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_143,c_71])).

tff(c_502,plain,(
    ! [B_91,A_92,C_93] :
      ( k2_relset_1(u1_struct_0(B_91),u1_struct_0(A_92),k2_tops_2(u1_struct_0(A_92),u1_struct_0(B_91),C_93)) = k2_struct_0(A_92)
      | ~ v2_funct_1(C_93)
      | k2_relset_1(u1_struct_0(A_92),u1_struct_0(B_91),C_93) != k2_struct_0(B_91)
      | ~ m1_subset_1(C_93,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_92),u1_struct_0(B_91))))
      | ~ v1_funct_2(C_93,u1_struct_0(A_92),u1_struct_0(B_91))
      | ~ v1_funct_1(C_93)
      | ~ l1_struct_0(B_91)
      | v2_struct_0(B_91)
      | ~ l1_struct_0(A_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_511,plain,(
    ! [A_92,C_93] :
      ( k2_relset_1(k2_relat_1('#skF_3'),u1_struct_0(A_92),k2_tops_2(u1_struct_0(A_92),u1_struct_0('#skF_2'),C_93)) = k2_struct_0(A_92)
      | ~ v2_funct_1(C_93)
      | k2_relset_1(u1_struct_0(A_92),u1_struct_0('#skF_2'),C_93) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_93,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_92),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_93,u1_struct_0(A_92),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_93)
      | ~ l1_struct_0('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_struct_0(A_92) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_152,c_502])).

tff(c_536,plain,(
    ! [A_92,C_93] :
      ( k2_relset_1(k2_relat_1('#skF_3'),u1_struct_0(A_92),k2_tops_2(u1_struct_0(A_92),k2_relat_1('#skF_3'),C_93)) = k2_struct_0(A_92)
      | ~ v2_funct_1(C_93)
      | k2_relset_1(u1_struct_0(A_92),k2_relat_1('#skF_3'),C_93) != k2_relat_1('#skF_3')
      | ~ m1_subset_1(C_93,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_92),k2_relat_1('#skF_3'))))
      | ~ v1_funct_2(C_93,u1_struct_0(A_92),k2_relat_1('#skF_3'))
      | ~ v1_funct_1(C_93)
      | v2_struct_0('#skF_2')
      | ~ l1_struct_0(A_92) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_152,c_152,c_152,c_143,c_152,c_511])).

tff(c_789,plain,(
    ! [A_106,C_107] :
      ( k2_relset_1(k2_relat_1('#skF_3'),u1_struct_0(A_106),k2_tops_2(u1_struct_0(A_106),k2_relat_1('#skF_3'),C_107)) = k2_struct_0(A_106)
      | ~ v2_funct_1(C_107)
      | k2_relset_1(u1_struct_0(A_106),k2_relat_1('#skF_3'),C_107) != k2_relat_1('#skF_3')
      | ~ m1_subset_1(C_107,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_106),k2_relat_1('#skF_3'))))
      | ~ v1_funct_2(C_107,u1_struct_0(A_106),k2_relat_1('#skF_3'))
      | ~ v1_funct_1(C_107)
      | ~ l1_struct_0(A_106) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_536])).

tff(c_804,plain,(
    ! [C_107] :
      ( k2_relset_1(k2_relat_1('#skF_3'),k2_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),k2_relat_1('#skF_3'),C_107)) = k2_struct_0('#skF_1')
      | ~ v2_funct_1(C_107)
      | k2_relset_1(u1_struct_0('#skF_1'),k2_relat_1('#skF_3'),C_107) != k2_relat_1('#skF_3')
      | ~ m1_subset_1(C_107,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),k2_relat_1('#skF_3'))))
      | ~ v1_funct_2(C_107,u1_struct_0('#skF_1'),k2_relat_1('#skF_3'))
      | ~ v1_funct_1(C_107)
      | ~ l1_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_789])).

tff(c_827,plain,(
    ! [C_109] :
      ( k2_relset_1(k2_relat_1('#skF_3'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),C_109)) = k2_struct_0('#skF_1')
      | ~ v2_funct_1(C_109)
      | k2_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),C_109) != k2_relat_1('#skF_3')
      | ~ m1_subset_1(C_109,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))))
      | ~ v1_funct_2(C_109,k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
      | ~ v1_funct_1(C_109) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_72,c_72,c_72,c_72,c_804])).

tff(c_836,plain,
    ( k2_relset_1(k2_relat_1('#skF_3'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) = k2_struct_0('#skF_1')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_331,c_827])).

tff(c_840,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_151,c_150,c_148,c_46,c_462,c_836])).

tff(c_14,plain,(
    ! [A_10] :
      ( k2_relat_1(k2_funct_1(A_10)) = k1_relat_1(A_10)
      | ~ v2_funct_1(A_10)
      | ~ v1_funct_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_851,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_840,c_14])).

tff(c_862,plain,(
    k2_struct_0('#skF_1') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_54,c_46,c_851])).

tff(c_200,plain,(
    ! [A_53,B_54,D_55] :
      ( r2_funct_2(A_53,B_54,D_55,D_55)
      | ~ m1_subset_1(D_55,k1_zfmisc_1(k2_zfmisc_1(A_53,B_54)))
      | ~ v1_funct_2(D_55,A_53,B_54)
      | ~ v1_funct_1(D_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_202,plain,
    ( r2_funct_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3','#skF_3')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_150,c_200])).

tff(c_205,plain,(
    r2_funct_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_151,c_202])).

tff(c_871,plain,(
    r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_862,c_205])).

tff(c_22,plain,(
    ! [A_12] :
      ( k2_funct_1(k2_funct_1(A_12)) = A_12
      | ~ v2_funct_1(A_12)
      | ~ v1_funct_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_874,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_862,c_151])).

tff(c_873,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_862,c_148])).

tff(c_228,plain,(
    ! [C_60,A_61,B_62] :
      ( v1_funct_1(k2_funct_1(C_60))
      | k2_relset_1(A_61,B_62,C_60) != B_62
      | ~ v2_funct_1(C_60)
      | ~ m1_subset_1(C_60,k1_zfmisc_1(k2_zfmisc_1(A_61,B_62)))
      | ~ v1_funct_2(C_60,A_61,B_62)
      | ~ v1_funct_1(C_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_231,plain,
    ( v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_150,c_228])).

tff(c_234,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_151,c_46,c_148,c_231])).

tff(c_243,plain,(
    ! [C_65,B_66,A_67] :
      ( v1_funct_2(k2_funct_1(C_65),B_66,A_67)
      | k2_relset_1(A_67,B_66,C_65) != B_66
      | ~ v2_funct_1(C_65)
      | ~ m1_subset_1(C_65,k1_zfmisc_1(k2_zfmisc_1(A_67,B_66)))
      | ~ v1_funct_2(C_65,A_67,B_66)
      | ~ v1_funct_1(C_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_246,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k2_struct_0('#skF_1'))
    | k2_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_150,c_243])).

tff(c_249,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_151,c_46,c_148,c_246])).

tff(c_870,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_862,c_249])).

tff(c_841,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) = k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_840,c_462])).

tff(c_1070,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_862,c_862,c_841])).

tff(c_2,plain,(
    ! [B_3,A_1] :
      ( v1_relat_1(B_3)
      | ~ m1_subset_1(B_3,k1_zfmisc_1(A_1))
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_397,plain,(
    ! [C_75,B_76,A_77] :
      ( v1_relat_1(k2_funct_1(C_75))
      | ~ v1_relat_1(k2_zfmisc_1(B_76,A_77))
      | k2_relset_1(A_77,B_76,C_75) != B_76
      | ~ v2_funct_1(C_75)
      | ~ m1_subset_1(C_75,k1_zfmisc_1(k2_zfmisc_1(A_77,B_76)))
      | ~ v1_funct_2(C_75,A_77,B_76)
      | ~ v1_funct_1(C_75) ) ),
    inference(resolution,[status(thm)],[c_380,c_2])).

tff(c_441,plain,(
    ! [C_80,A_81,B_82] :
      ( v1_relat_1(k2_funct_1(C_80))
      | k2_relset_1(A_81,B_82,C_80) != B_82
      | ~ v2_funct_1(C_80)
      | ~ m1_subset_1(C_80,k1_zfmisc_1(k2_zfmisc_1(A_81,B_82)))
      | ~ v1_funct_2(C_80,A_81,B_82)
      | ~ v1_funct_1(C_80) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_397])).

tff(c_447,plain,
    ( v1_relat_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_150,c_441])).

tff(c_451,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_151,c_46,c_148,c_447])).

tff(c_866,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_862,c_840])).

tff(c_8,plain,(
    ! [A_6] : v2_funct_1(k6_relat_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_18,plain,(
    ! [A_11] :
      ( k5_relat_1(k2_funct_1(A_11),A_11) = k6_relat_1(k2_relat_1(A_11))
      | ~ v2_funct_1(A_11)
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_217,plain,(
    ! [B_58,A_59] :
      ( v2_funct_1(B_58)
      | k2_relat_1(B_58) != k1_relat_1(A_59)
      | ~ v2_funct_1(k5_relat_1(B_58,A_59))
      | ~ v1_funct_1(B_58)
      | ~ v1_relat_1(B_58)
      | ~ v1_funct_1(A_59)
      | ~ v1_relat_1(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_220,plain,(
    ! [A_11] :
      ( v2_funct_1(k2_funct_1(A_11))
      | k2_relat_1(k2_funct_1(A_11)) != k1_relat_1(A_11)
      | ~ v2_funct_1(k6_relat_1(k2_relat_1(A_11)))
      | ~ v1_funct_1(k2_funct_1(A_11))
      | ~ v1_relat_1(k2_funct_1(A_11))
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11)
      | ~ v2_funct_1(A_11)
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_217])).

tff(c_225,plain,(
    ! [A_11] :
      ( v2_funct_1(k2_funct_1(A_11))
      | k2_relat_1(k2_funct_1(A_11)) != k1_relat_1(A_11)
      | ~ v1_funct_1(k2_funct_1(A_11))
      | ~ v1_relat_1(k2_funct_1(A_11))
      | ~ v2_funct_1(A_11)
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_220])).

tff(c_188,plain,(
    ! [A_52] :
      ( k5_relat_1(k2_funct_1(A_52),A_52) = k6_relat_1(k2_relat_1(A_52))
      | ~ v2_funct_1(A_52)
      | ~ v1_funct_1(A_52)
      | ~ v1_relat_1(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_197,plain,(
    ! [A_12] :
      ( k6_relat_1(k2_relat_1(k2_funct_1(A_12))) = k5_relat_1(A_12,k2_funct_1(A_12))
      | ~ v2_funct_1(k2_funct_1(A_12))
      | ~ v1_funct_1(k2_funct_1(A_12))
      | ~ v1_relat_1(k2_funct_1(A_12))
      | ~ v2_funct_1(A_12)
      | ~ v1_funct_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_188])).

tff(c_848,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_relat_1(k2_struct_0('#skF_1'))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_840,c_197])).

tff(c_860,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_relat_1(k2_struct_0('#skF_1'))
    | ~ v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_54,c_46,c_451,c_234,c_848])).

tff(c_1077,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_relat_1(k1_relat_1('#skF_3'))
    | ~ v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_862,c_860])).

tff(c_1078,plain,(
    ~ v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1077])).

tff(c_1084,plain,
    ( k2_relat_1(k2_funct_1('#skF_3')) != k1_relat_1('#skF_3')
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_225,c_1078])).

tff(c_1091,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_54,c_46,c_451,c_234,c_866,c_1084])).

tff(c_1093,plain,(
    v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1077])).

tff(c_872,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_862,c_150])).

tff(c_38,plain,(
    ! [A_24,B_25,C_26] :
      ( k2_tops_2(A_24,B_25,C_26) = k2_funct_1(C_26)
      | ~ v2_funct_1(C_26)
      | k2_relset_1(A_24,B_25,C_26) != B_25
      | ~ m1_subset_1(C_26,k1_zfmisc_1(k2_zfmisc_1(A_24,B_25)))
      | ~ v1_funct_2(C_26,A_24,B_25)
      | ~ v1_funct_1(C_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_1094,plain,(
    ! [B_118,A_119,C_120] :
      ( k2_tops_2(B_118,A_119,k2_funct_1(C_120)) = k2_funct_1(k2_funct_1(C_120))
      | ~ v2_funct_1(k2_funct_1(C_120))
      | k2_relset_1(B_118,A_119,k2_funct_1(C_120)) != A_119
      | ~ v1_funct_2(k2_funct_1(C_120),B_118,A_119)
      | ~ v1_funct_1(k2_funct_1(C_120))
      | k2_relset_1(A_119,B_118,C_120) != B_118
      | ~ v2_funct_1(C_120)
      | ~ m1_subset_1(C_120,k1_zfmisc_1(k2_zfmisc_1(A_119,B_118)))
      | ~ v1_funct_2(C_120,A_119,B_118)
      | ~ v1_funct_1(C_120) ) ),
    inference(resolution,[status(thm)],[c_380,c_38])).

tff(c_1097,plain,
    ( k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) != k1_relat_1('#skF_3')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_872,c_1094])).

tff(c_1103,plain,(
    k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_874,c_46,c_873,c_234,c_870,c_1070,c_1093,c_1097])).

tff(c_44,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),k2_tops_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_125,plain,(
    ~ r2_funct_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_72,c_72,c_71,c_71,c_71,c_44])).

tff(c_149,plain,(
    ~ r2_funct_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),k2_tops_2(k2_relat_1('#skF_3'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_143,c_143,c_143,c_125])).

tff(c_332,plain,(
    ~ r2_funct_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),k2_tops_2(k2_relat_1('#skF_3'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_331,c_149])).

tff(c_868,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_862,c_862,c_332])).

tff(c_1147,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),k2_funct_1(k2_funct_1('#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1103,c_868])).

tff(c_1150,plain,
    ( ~ r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3','#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_1147])).

tff(c_1153,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_54,c_46,c_871,c_1150])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 18:28:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.42/1.82  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.42/1.83  
% 4.42/1.83  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.42/1.83  %$ r2_funct_2 > v1_funct_2 > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k2_tops_2 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k6_relat_1 > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 4.42/1.83  
% 4.42/1.83  %Foreground sorts:
% 4.42/1.83  
% 4.42/1.83  
% 4.42/1.83  %Background operators:
% 4.42/1.83  
% 4.42/1.83  
% 4.42/1.83  %Foreground operators:
% 4.42/1.83  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.42/1.83  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.42/1.83  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.42/1.83  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 4.42/1.83  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 4.42/1.83  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.42/1.83  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 4.42/1.83  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.42/1.83  tff(k2_tops_2, type, k2_tops_2: ($i * $i * $i) > $i).
% 4.42/1.83  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.42/1.83  tff('#skF_2', type, '#skF_2': $i).
% 4.42/1.83  tff('#skF_3', type, '#skF_3': $i).
% 4.42/1.83  tff('#skF_1', type, '#skF_1': $i).
% 4.42/1.83  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.42/1.83  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.42/1.83  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 4.42/1.83  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.42/1.83  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.42/1.83  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.42/1.83  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 4.42/1.83  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.42/1.83  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.42/1.83  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 4.42/1.83  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.42/1.83  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 4.42/1.83  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.42/1.83  
% 4.70/1.86  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 4.70/1.86  tff(f_180, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: ((~v2_struct_0(B) & l1_struct_0(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B)) & v2_funct_1(C)) => r2_funct_2(u1_struct_0(A), u1_struct_0(B), k2_tops_2(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)), C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_tops_2)).
% 4.70/1.86  tff(f_123, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 4.70/1.86  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 4.70/1.86  tff(f_87, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 4.70/1.86  tff(f_119, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_funct_2)).
% 4.70/1.86  tff(f_135, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => (k2_tops_2(A, B, C) = k2_funct_1(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tops_2)).
% 4.70/1.86  tff(f_158, axiom, (![A]: (l1_struct_0(A) => (![B]: ((~v2_struct_0(B) & l1_struct_0(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B)) & v2_funct_1(C)) => ((k1_relset_1(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)) = k2_struct_0(B)) & (k2_relset_1(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)) = k2_struct_0(A)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_tops_2)).
% 4.70/1.86  tff(f_65, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 4.70/1.86  tff(f_103, axiom, (![A, B, C, D]: ((((((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(D)) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_funct_2(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_funct_2)).
% 4.70/1.86  tff(f_83, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(k2_funct_1(A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_1)).
% 4.70/1.86  tff(f_38, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_funct_1)).
% 4.70/1.86  tff(f_75, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_funct_1)).
% 4.70/1.86  tff(f_55, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v2_funct_1(k5_relat_1(B, A)) & (k2_relat_1(B) = k1_relat_1(A))) => (v2_funct_1(B) & v2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_funct_1)).
% 4.70/1.86  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.70/1.86  tff(c_60, plain, (l1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_180])).
% 4.70/1.86  tff(c_64, plain, (![A_42]: (u1_struct_0(A_42)=k2_struct_0(A_42) | ~l1_struct_0(A_42))), inference(cnfTransformation, [status(thm)], [f_123])).
% 4.70/1.86  tff(c_72, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_60, c_64])).
% 4.70/1.86  tff(c_56, plain, (l1_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_180])).
% 4.70/1.86  tff(c_71, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_56, c_64])).
% 4.70/1.86  tff(c_50, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_180])).
% 4.70/1.86  tff(c_88, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_71, c_50])).
% 4.70/1.86  tff(c_89, plain, (![B_43, A_44]: (v1_relat_1(B_43) | ~m1_subset_1(B_43, k1_zfmisc_1(A_44)) | ~v1_relat_1(A_44))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.70/1.86  tff(c_92, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_88, c_89])).
% 4.70/1.86  tff(c_95, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_92])).
% 4.70/1.86  tff(c_54, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_180])).
% 4.70/1.86  tff(c_46, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_180])).
% 4.70/1.86  tff(c_138, plain, (![A_48, B_49, C_50]: (k2_relset_1(A_48, B_49, C_50)=k2_relat_1(C_50) | ~m1_subset_1(C_50, k1_zfmisc_1(k2_zfmisc_1(A_48, B_49))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.70/1.86  tff(c_142, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_88, c_138])).
% 4.70/1.86  tff(c_48, plain, (k2_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_180])).
% 4.70/1.86  tff(c_83, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_71, c_48])).
% 4.70/1.86  tff(c_143, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_142, c_83])).
% 4.70/1.86  tff(c_52, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_180])).
% 4.70/1.86  tff(c_73, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_71, c_52])).
% 4.70/1.86  tff(c_82, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_73])).
% 4.70/1.86  tff(c_151, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_143, c_82])).
% 4.70/1.86  tff(c_150, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_143, c_88])).
% 4.70/1.86  tff(c_148, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_143, c_142])).
% 4.70/1.86  tff(c_380, plain, (![C_75, B_76, A_77]: (m1_subset_1(k2_funct_1(C_75), k1_zfmisc_1(k2_zfmisc_1(B_76, A_77))) | k2_relset_1(A_77, B_76, C_75)!=B_76 | ~v2_funct_1(C_75) | ~m1_subset_1(C_75, k1_zfmisc_1(k2_zfmisc_1(A_77, B_76))) | ~v1_funct_2(C_75, A_77, B_76) | ~v1_funct_1(C_75))), inference(cnfTransformation, [status(thm)], [f_119])).
% 4.70/1.86  tff(c_24, plain, (![A_13, B_14, C_15]: (k2_relset_1(A_13, B_14, C_15)=k2_relat_1(C_15) | ~m1_subset_1(C_15, k1_zfmisc_1(k2_zfmisc_1(A_13, B_14))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.70/1.86  tff(c_452, plain, (![B_83, A_84, C_85]: (k2_relset_1(B_83, A_84, k2_funct_1(C_85))=k2_relat_1(k2_funct_1(C_85)) | k2_relset_1(A_84, B_83, C_85)!=B_83 | ~v2_funct_1(C_85) | ~m1_subset_1(C_85, k1_zfmisc_1(k2_zfmisc_1(A_84, B_83))) | ~v1_funct_2(C_85, A_84, B_83) | ~v1_funct_1(C_85))), inference(resolution, [status(thm)], [c_380, c_24])).
% 4.70/1.86  tff(c_458, plain, (k2_relset_1(k2_relat_1('#skF_3'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3')) | k2_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_150, c_452])).
% 4.70/1.86  tff(c_462, plain, (k2_relset_1(k2_relat_1('#skF_3'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_151, c_46, c_148, c_458])).
% 4.70/1.86  tff(c_325, plain, (![A_71, B_72, C_73]: (k2_tops_2(A_71, B_72, C_73)=k2_funct_1(C_73) | ~v2_funct_1(C_73) | k2_relset_1(A_71, B_72, C_73)!=B_72 | ~m1_subset_1(C_73, k1_zfmisc_1(k2_zfmisc_1(A_71, B_72))) | ~v1_funct_2(C_73, A_71, B_72) | ~v1_funct_1(C_73))), inference(cnfTransformation, [status(thm)], [f_135])).
% 4.70/1.86  tff(c_328, plain, (k2_tops_2(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | k2_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_150, c_325])).
% 4.70/1.86  tff(c_331, plain, (k2_tops_2(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_151, c_148, c_46, c_328])).
% 4.70/1.86  tff(c_58, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_180])).
% 4.70/1.86  tff(c_152, plain, (u1_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_143, c_71])).
% 4.70/1.86  tff(c_502, plain, (![B_91, A_92, C_93]: (k2_relset_1(u1_struct_0(B_91), u1_struct_0(A_92), k2_tops_2(u1_struct_0(A_92), u1_struct_0(B_91), C_93))=k2_struct_0(A_92) | ~v2_funct_1(C_93) | k2_relset_1(u1_struct_0(A_92), u1_struct_0(B_91), C_93)!=k2_struct_0(B_91) | ~m1_subset_1(C_93, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_92), u1_struct_0(B_91)))) | ~v1_funct_2(C_93, u1_struct_0(A_92), u1_struct_0(B_91)) | ~v1_funct_1(C_93) | ~l1_struct_0(B_91) | v2_struct_0(B_91) | ~l1_struct_0(A_92))), inference(cnfTransformation, [status(thm)], [f_158])).
% 4.70/1.86  tff(c_511, plain, (![A_92, C_93]: (k2_relset_1(k2_relat_1('#skF_3'), u1_struct_0(A_92), k2_tops_2(u1_struct_0(A_92), u1_struct_0('#skF_2'), C_93))=k2_struct_0(A_92) | ~v2_funct_1(C_93) | k2_relset_1(u1_struct_0(A_92), u1_struct_0('#skF_2'), C_93)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_93, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_92), u1_struct_0('#skF_2')))) | ~v1_funct_2(C_93, u1_struct_0(A_92), u1_struct_0('#skF_2')) | ~v1_funct_1(C_93) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2') | ~l1_struct_0(A_92))), inference(superposition, [status(thm), theory('equality')], [c_152, c_502])).
% 4.70/1.86  tff(c_536, plain, (![A_92, C_93]: (k2_relset_1(k2_relat_1('#skF_3'), u1_struct_0(A_92), k2_tops_2(u1_struct_0(A_92), k2_relat_1('#skF_3'), C_93))=k2_struct_0(A_92) | ~v2_funct_1(C_93) | k2_relset_1(u1_struct_0(A_92), k2_relat_1('#skF_3'), C_93)!=k2_relat_1('#skF_3') | ~m1_subset_1(C_93, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_92), k2_relat_1('#skF_3')))) | ~v1_funct_2(C_93, u1_struct_0(A_92), k2_relat_1('#skF_3')) | ~v1_funct_1(C_93) | v2_struct_0('#skF_2') | ~l1_struct_0(A_92))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_152, c_152, c_152, c_143, c_152, c_511])).
% 4.70/1.86  tff(c_789, plain, (![A_106, C_107]: (k2_relset_1(k2_relat_1('#skF_3'), u1_struct_0(A_106), k2_tops_2(u1_struct_0(A_106), k2_relat_1('#skF_3'), C_107))=k2_struct_0(A_106) | ~v2_funct_1(C_107) | k2_relset_1(u1_struct_0(A_106), k2_relat_1('#skF_3'), C_107)!=k2_relat_1('#skF_3') | ~m1_subset_1(C_107, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_106), k2_relat_1('#skF_3')))) | ~v1_funct_2(C_107, u1_struct_0(A_106), k2_relat_1('#skF_3')) | ~v1_funct_1(C_107) | ~l1_struct_0(A_106))), inference(negUnitSimplification, [status(thm)], [c_58, c_536])).
% 4.70/1.86  tff(c_804, plain, (![C_107]: (k2_relset_1(k2_relat_1('#skF_3'), k2_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), k2_relat_1('#skF_3'), C_107))=k2_struct_0('#skF_1') | ~v2_funct_1(C_107) | k2_relset_1(u1_struct_0('#skF_1'), k2_relat_1('#skF_3'), C_107)!=k2_relat_1('#skF_3') | ~m1_subset_1(C_107, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), k2_relat_1('#skF_3')))) | ~v1_funct_2(C_107, u1_struct_0('#skF_1'), k2_relat_1('#skF_3')) | ~v1_funct_1(C_107) | ~l1_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_72, c_789])).
% 4.70/1.86  tff(c_827, plain, (![C_109]: (k2_relset_1(k2_relat_1('#skF_3'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), C_109))=k2_struct_0('#skF_1') | ~v2_funct_1(C_109) | k2_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), C_109)!=k2_relat_1('#skF_3') | ~m1_subset_1(C_109, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3')))) | ~v1_funct_2(C_109, k2_struct_0('#skF_1'), k2_relat_1('#skF_3')) | ~v1_funct_1(C_109))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_72, c_72, c_72, c_72, c_804])).
% 4.70/1.86  tff(c_836, plain, (k2_relset_1(k2_relat_1('#skF_3'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))=k2_struct_0('#skF_1') | ~v2_funct_1('#skF_3') | k2_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3')))) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_331, c_827])).
% 4.70/1.86  tff(c_840, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_151, c_150, c_148, c_46, c_462, c_836])).
% 4.70/1.86  tff(c_14, plain, (![A_10]: (k2_relat_1(k2_funct_1(A_10))=k1_relat_1(A_10) | ~v2_funct_1(A_10) | ~v1_funct_1(A_10) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.70/1.86  tff(c_851, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_840, c_14])).
% 4.70/1.86  tff(c_862, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_95, c_54, c_46, c_851])).
% 4.70/1.86  tff(c_200, plain, (![A_53, B_54, D_55]: (r2_funct_2(A_53, B_54, D_55, D_55) | ~m1_subset_1(D_55, k1_zfmisc_1(k2_zfmisc_1(A_53, B_54))) | ~v1_funct_2(D_55, A_53, B_54) | ~v1_funct_1(D_55))), inference(cnfTransformation, [status(thm)], [f_103])).
% 4.70/1.86  tff(c_202, plain, (r2_funct_2(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3', '#skF_3') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_150, c_200])).
% 4.70/1.86  tff(c_205, plain, (r2_funct_2(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_151, c_202])).
% 4.70/1.86  tff(c_871, plain, (r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_862, c_205])).
% 4.70/1.86  tff(c_22, plain, (![A_12]: (k2_funct_1(k2_funct_1(A_12))=A_12 | ~v2_funct_1(A_12) | ~v1_funct_1(A_12) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.70/1.86  tff(c_874, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_862, c_151])).
% 4.70/1.86  tff(c_873, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_862, c_148])).
% 4.70/1.86  tff(c_228, plain, (![C_60, A_61, B_62]: (v1_funct_1(k2_funct_1(C_60)) | k2_relset_1(A_61, B_62, C_60)!=B_62 | ~v2_funct_1(C_60) | ~m1_subset_1(C_60, k1_zfmisc_1(k2_zfmisc_1(A_61, B_62))) | ~v1_funct_2(C_60, A_61, B_62) | ~v1_funct_1(C_60))), inference(cnfTransformation, [status(thm)], [f_119])).
% 4.70/1.86  tff(c_231, plain, (v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_150, c_228])).
% 4.70/1.86  tff(c_234, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_151, c_46, c_148, c_231])).
% 4.70/1.86  tff(c_243, plain, (![C_65, B_66, A_67]: (v1_funct_2(k2_funct_1(C_65), B_66, A_67) | k2_relset_1(A_67, B_66, C_65)!=B_66 | ~v2_funct_1(C_65) | ~m1_subset_1(C_65, k1_zfmisc_1(k2_zfmisc_1(A_67, B_66))) | ~v1_funct_2(C_65, A_67, B_66) | ~v1_funct_1(C_65))), inference(cnfTransformation, [status(thm)], [f_119])).
% 4.70/1.86  tff(c_246, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k2_struct_0('#skF_1')) | k2_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_150, c_243])).
% 4.70/1.86  tff(c_249, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_151, c_46, c_148, c_246])).
% 4.70/1.86  tff(c_870, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_862, c_249])).
% 4.70/1.86  tff(c_841, plain, (k2_relset_1(k2_relat_1('#skF_3'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_840, c_462])).
% 4.70/1.86  tff(c_1070, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_862, c_862, c_841])).
% 4.70/1.86  tff(c_2, plain, (![B_3, A_1]: (v1_relat_1(B_3) | ~m1_subset_1(B_3, k1_zfmisc_1(A_1)) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.70/1.86  tff(c_397, plain, (![C_75, B_76, A_77]: (v1_relat_1(k2_funct_1(C_75)) | ~v1_relat_1(k2_zfmisc_1(B_76, A_77)) | k2_relset_1(A_77, B_76, C_75)!=B_76 | ~v2_funct_1(C_75) | ~m1_subset_1(C_75, k1_zfmisc_1(k2_zfmisc_1(A_77, B_76))) | ~v1_funct_2(C_75, A_77, B_76) | ~v1_funct_1(C_75))), inference(resolution, [status(thm)], [c_380, c_2])).
% 4.70/1.86  tff(c_441, plain, (![C_80, A_81, B_82]: (v1_relat_1(k2_funct_1(C_80)) | k2_relset_1(A_81, B_82, C_80)!=B_82 | ~v2_funct_1(C_80) | ~m1_subset_1(C_80, k1_zfmisc_1(k2_zfmisc_1(A_81, B_82))) | ~v1_funct_2(C_80, A_81, B_82) | ~v1_funct_1(C_80))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_397])).
% 4.70/1.86  tff(c_447, plain, (v1_relat_1(k2_funct_1('#skF_3')) | k2_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_150, c_441])).
% 4.70/1.86  tff(c_451, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_151, c_46, c_148, c_447])).
% 4.70/1.86  tff(c_866, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_862, c_840])).
% 4.70/1.86  tff(c_8, plain, (![A_6]: (v2_funct_1(k6_relat_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.70/1.86  tff(c_18, plain, (![A_11]: (k5_relat_1(k2_funct_1(A_11), A_11)=k6_relat_1(k2_relat_1(A_11)) | ~v2_funct_1(A_11) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.70/1.86  tff(c_217, plain, (![B_58, A_59]: (v2_funct_1(B_58) | k2_relat_1(B_58)!=k1_relat_1(A_59) | ~v2_funct_1(k5_relat_1(B_58, A_59)) | ~v1_funct_1(B_58) | ~v1_relat_1(B_58) | ~v1_funct_1(A_59) | ~v1_relat_1(A_59))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.70/1.86  tff(c_220, plain, (![A_11]: (v2_funct_1(k2_funct_1(A_11)) | k2_relat_1(k2_funct_1(A_11))!=k1_relat_1(A_11) | ~v2_funct_1(k6_relat_1(k2_relat_1(A_11))) | ~v1_funct_1(k2_funct_1(A_11)) | ~v1_relat_1(k2_funct_1(A_11)) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11) | ~v2_funct_1(A_11) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(superposition, [status(thm), theory('equality')], [c_18, c_217])).
% 4.70/1.86  tff(c_225, plain, (![A_11]: (v2_funct_1(k2_funct_1(A_11)) | k2_relat_1(k2_funct_1(A_11))!=k1_relat_1(A_11) | ~v1_funct_1(k2_funct_1(A_11)) | ~v1_relat_1(k2_funct_1(A_11)) | ~v2_funct_1(A_11) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_220])).
% 4.70/1.86  tff(c_188, plain, (![A_52]: (k5_relat_1(k2_funct_1(A_52), A_52)=k6_relat_1(k2_relat_1(A_52)) | ~v2_funct_1(A_52) | ~v1_funct_1(A_52) | ~v1_relat_1(A_52))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.70/1.86  tff(c_197, plain, (![A_12]: (k6_relat_1(k2_relat_1(k2_funct_1(A_12)))=k5_relat_1(A_12, k2_funct_1(A_12)) | ~v2_funct_1(k2_funct_1(A_12)) | ~v1_funct_1(k2_funct_1(A_12)) | ~v1_relat_1(k2_funct_1(A_12)) | ~v2_funct_1(A_12) | ~v1_funct_1(A_12) | ~v1_relat_1(A_12))), inference(superposition, [status(thm), theory('equality')], [c_22, c_188])).
% 4.70/1.86  tff(c_848, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_relat_1(k2_struct_0('#skF_1')) | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_840, c_197])).
% 4.70/1.86  tff(c_860, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_relat_1(k2_struct_0('#skF_1')) | ~v2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_95, c_54, c_46, c_451, c_234, c_848])).
% 4.70/1.86  tff(c_1077, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_relat_1(k1_relat_1('#skF_3')) | ~v2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_862, c_860])).
% 4.70/1.86  tff(c_1078, plain, (~v2_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_1077])).
% 4.70/1.86  tff(c_1084, plain, (k2_relat_1(k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3') | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_225, c_1078])).
% 4.70/1.86  tff(c_1091, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_95, c_54, c_46, c_451, c_234, c_866, c_1084])).
% 4.70/1.86  tff(c_1093, plain, (v2_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_1077])).
% 4.70/1.86  tff(c_872, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_862, c_150])).
% 4.70/1.86  tff(c_38, plain, (![A_24, B_25, C_26]: (k2_tops_2(A_24, B_25, C_26)=k2_funct_1(C_26) | ~v2_funct_1(C_26) | k2_relset_1(A_24, B_25, C_26)!=B_25 | ~m1_subset_1(C_26, k1_zfmisc_1(k2_zfmisc_1(A_24, B_25))) | ~v1_funct_2(C_26, A_24, B_25) | ~v1_funct_1(C_26))), inference(cnfTransformation, [status(thm)], [f_135])).
% 4.70/1.86  tff(c_1094, plain, (![B_118, A_119, C_120]: (k2_tops_2(B_118, A_119, k2_funct_1(C_120))=k2_funct_1(k2_funct_1(C_120)) | ~v2_funct_1(k2_funct_1(C_120)) | k2_relset_1(B_118, A_119, k2_funct_1(C_120))!=A_119 | ~v1_funct_2(k2_funct_1(C_120), B_118, A_119) | ~v1_funct_1(k2_funct_1(C_120)) | k2_relset_1(A_119, B_118, C_120)!=B_118 | ~v2_funct_1(C_120) | ~m1_subset_1(C_120, k1_zfmisc_1(k2_zfmisc_1(A_119, B_118))) | ~v1_funct_2(C_120, A_119, B_118) | ~v1_funct_1(C_120))), inference(resolution, [status(thm)], [c_380, c_38])).
% 4.70/1.86  tff(c_1097, plain, (k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3')) | ~v2_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3') | ~v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_872, c_1094])).
% 4.70/1.86  tff(c_1103, plain, (k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_874, c_46, c_873, c_234, c_870, c_1070, c_1093, c_1097])).
% 4.70/1.86  tff(c_44, plain, (~r2_funct_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), k2_tops_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_180])).
% 4.70/1.86  tff(c_125, plain, (~r2_funct_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_72, c_72, c_71, c_71, c_71, c_44])).
% 4.70/1.86  tff(c_149, plain, (~r2_funct_2(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), k2_tops_2(k2_relat_1('#skF_3'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_143, c_143, c_143, c_125])).
% 4.70/1.86  tff(c_332, plain, (~r2_funct_2(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), k2_tops_2(k2_relat_1('#skF_3'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_331, c_149])).
% 4.70/1.86  tff(c_868, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_862, c_862, c_332])).
% 4.70/1.86  tff(c_1147, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), k2_funct_1(k2_funct_1('#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1103, c_868])).
% 4.70/1.86  tff(c_1150, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3', '#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_22, c_1147])).
% 4.70/1.86  tff(c_1153, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_95, c_54, c_46, c_871, c_1150])).
% 4.70/1.86  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.70/1.86  
% 4.70/1.86  Inference rules
% 4.70/1.86  ----------------------
% 4.70/1.86  #Ref     : 0
% 4.70/1.86  #Sup     : 260
% 4.70/1.86  #Fact    : 0
% 4.70/1.86  #Define  : 0
% 4.70/1.86  #Split   : 1
% 4.70/1.86  #Chain   : 0
% 4.70/1.86  #Close   : 0
% 4.70/1.86  
% 4.70/1.86  Ordering : KBO
% 4.70/1.86  
% 4.70/1.86  Simplification rules
% 4.70/1.86  ----------------------
% 4.70/1.86  #Subsume      : 41
% 4.70/1.86  #Demod        : 433
% 4.70/1.86  #Tautology    : 136
% 4.70/1.86  #SimpNegUnit  : 4
% 4.70/1.86  #BackRed      : 19
% 4.70/1.86  
% 4.70/1.86  #Partial instantiations: 0
% 4.70/1.86  #Strategies tried      : 1
% 4.70/1.86  
% 4.70/1.86  Timing (in seconds)
% 4.70/1.86  ----------------------
% 4.70/1.86  Preprocessing        : 0.38
% 4.70/1.86  Parsing              : 0.20
% 4.70/1.86  CNF conversion       : 0.02
% 4.70/1.86  Main loop            : 0.69
% 4.70/1.86  Inferencing          : 0.25
% 4.70/1.86  Reduction            : 0.26
% 4.70/1.86  Demodulation         : 0.20
% 4.70/1.86  BG Simplification    : 0.04
% 4.70/1.86  Subsumption          : 0.11
% 4.70/1.86  Abstraction          : 0.04
% 4.70/1.86  MUC search           : 0.00
% 4.70/1.86  Cooper               : 0.00
% 4.70/1.86  Total                : 1.12
% 4.70/1.86  Index Insertion      : 0.00
% 4.70/1.86  Index Deletion       : 0.00
% 4.70/1.86  Index Matching       : 0.00
% 4.70/1.86  BG Taut test         : 0.00
%------------------------------------------------------------------------------
