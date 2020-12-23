%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:49 EST 2020

% Result     : Theorem 15.23s
% Output     : CNFRefutation 15.23s
% Verified   : 
% Statistics : Number of formulae       :  198 (6352 expanded)
%              Number of leaves         :   36 (2179 expanded)
%              Depth                    :   21
%              Number of atoms          :  721 (17963 expanded)
%              Number of equality atoms :  125 (3110 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_funct_2 > v5_pre_topc > v3_tops_2 > v1_funct_2 > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_relat_1 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k2_tops_2 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k2_struct_0 > k2_funct_1 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

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

tff(v3_tops_2,type,(
    v3_tops_2: ( $i * $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

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

tff(v5_pre_topc,type,(
    v5_pre_topc: ( $i * $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(r2_funct_2,type,(
    r2_funct_2: ( $i * $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_177,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & l1_pre_topc(B) )
           => ! [C] :
                ( ( v1_funct_1(C)
                  & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                  & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
               => ( v3_tops_2(C,A,B)
                 => v3_tops_2(k2_tops_2(u1_struct_0(A),u1_struct_0(B),C),B,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_tops_2)).

tff(f_65,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_61,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( k2_relset_1(A,B,C) = B
          & v2_funct_1(C) )
       => k2_tops_2(A,B,C) = k2_funct_1(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_2)).

tff(f_101,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( l1_pre_topc(B)
         => ! [C] :
              ( ( v1_funct_1(C)
                & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
             => ( v3_tops_2(C,A,B)
              <=> ( k1_relset_1(u1_struct_0(A),u1_struct_0(B),C) = k2_struct_0(A)
                  & k2_relset_1(u1_struct_0(A),u1_struct_0(B),C) = k2_struct_0(B)
                  & v2_funct_1(C)
                  & v5_pre_topc(C,A,B)
                  & v5_pre_topc(k2_tops_2(u1_struct_0(A),u1_struct_0(B),C),B,A) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tops_2)).

tff(f_113,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( v1_funct_1(k2_tops_2(A,B,C))
        & v1_funct_2(k2_tops_2(A,B,C),B,A)
        & m1_subset_1(k2_tops_2(A,B,C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_2)).

tff(f_136,axiom,(
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

tff(f_41,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_37,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A)
        & v2_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A))
        & v2_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_funct_1)).

tff(f_157,axiom,(
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
               => r2_funct_2(u1_struct_0(A),u1_struct_0(B),k2_tops_2(u1_struct_0(B),u1_struct_0(A),k2_tops_2(u1_struct_0(A),u1_struct_0(B),C)),C) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_tops_2)).

tff(f_57,axiom,(
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

tff(c_52,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_58,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_16,plain,(
    ! [A_10] :
      ( l1_struct_0(A_10)
      | ~ l1_pre_topc(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_60,plain,(
    ! [A_43] :
      ( u1_struct_0(A_43) = k2_struct_0(A_43)
      | ~ l1_struct_0(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_65,plain,(
    ! [A_44] :
      ( u1_struct_0(A_44) = k2_struct_0(A_44)
      | ~ l1_pre_topc(A_44) ) ),
    inference(resolution,[status(thm)],[c_16,c_60])).

tff(c_73,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_58,c_65])).

tff(c_54,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_72,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_65])).

tff(c_50,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_75,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_50])).

tff(c_84,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_75])).

tff(c_48,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_74,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_48])).

tff(c_86,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_74])).

tff(c_140,plain,(
    ! [A_66,B_67,C_68] :
      ( k2_tops_2(A_66,B_67,C_68) = k2_funct_1(C_68)
      | ~ v2_funct_1(C_68)
      | k2_relset_1(A_66,B_67,C_68) != B_67
      | ~ m1_subset_1(C_68,k1_zfmisc_1(k2_zfmisc_1(A_66,B_67)))
      | ~ v1_funct_2(C_68,A_66,B_67)
      | ~ v1_funct_1(C_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_146,plain,
    ( k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_86,c_140])).

tff(c_150,plain,
    ( k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_84,c_146])).

tff(c_151,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_150])).

tff(c_46,plain,(
    v3_tops_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_441,plain,(
    ! [A_108,B_109,C_110] :
      ( k2_relset_1(u1_struct_0(A_108),u1_struct_0(B_109),C_110) = k2_struct_0(B_109)
      | ~ v3_tops_2(C_110,A_108,B_109)
      | ~ m1_subset_1(C_110,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_108),u1_struct_0(B_109))))
      | ~ v1_funct_2(C_110,u1_struct_0(A_108),u1_struct_0(B_109))
      | ~ v1_funct_1(C_110)
      | ~ l1_pre_topc(B_109)
      | ~ l1_pre_topc(A_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_457,plain,(
    ! [A_108,C_110] :
      ( k2_relset_1(u1_struct_0(A_108),u1_struct_0('#skF_2'),C_110) = k2_struct_0('#skF_2')
      | ~ v3_tops_2(C_110,A_108,'#skF_2')
      | ~ m1_subset_1(C_110,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_108),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_110,u1_struct_0(A_108),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_110)
      | ~ l1_pre_topc('#skF_2')
      | ~ l1_pre_topc(A_108) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_441])).

tff(c_511,plain,(
    ! [A_116,C_117] :
      ( k2_relset_1(u1_struct_0(A_116),k2_struct_0('#skF_2'),C_117) = k2_struct_0('#skF_2')
      | ~ v3_tops_2(C_117,A_116,'#skF_2')
      | ~ m1_subset_1(C_117,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_116),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_117,u1_struct_0(A_116),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_117)
      | ~ l1_pre_topc(A_116) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_72,c_72,c_457])).

tff(c_518,plain,(
    ! [C_117] :
      ( k2_relset_1(u1_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_117) = k2_struct_0('#skF_2')
      | ~ v3_tops_2(C_117,'#skF_1','#skF_2')
      | ~ m1_subset_1(C_117,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_117,u1_struct_0('#skF_1'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_117)
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_73,c_511])).

tff(c_527,plain,(
    ! [C_118] :
      ( k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_118) = k2_struct_0('#skF_2')
      | ~ v3_tops_2(C_118,'#skF_1','#skF_2')
      | ~ m1_subset_1(C_118,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_118,k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_118) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_73,c_73,c_518])).

tff(c_534,plain,
    ( k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2')
    | ~ v3_tops_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_86,c_527])).

tff(c_538,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_84,c_46,c_534])).

tff(c_540,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_151,c_538])).

tff(c_541,plain,
    ( ~ v2_funct_1('#skF_3')
    | k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_150])).

tff(c_547,plain,(
    ~ v2_funct_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_541])).

tff(c_548,plain,(
    ! [C_119,A_120,B_121] :
      ( v2_funct_1(C_119)
      | ~ v3_tops_2(C_119,A_120,B_121)
      | ~ m1_subset_1(C_119,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_120),u1_struct_0(B_121))))
      | ~ v1_funct_2(C_119,u1_struct_0(A_120),u1_struct_0(B_121))
      | ~ v1_funct_1(C_119)
      | ~ l1_pre_topc(B_121)
      | ~ l1_pre_topc(A_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_555,plain,(
    ! [C_119,B_121] :
      ( v2_funct_1(C_119)
      | ~ v3_tops_2(C_119,'#skF_1',B_121)
      | ~ m1_subset_1(C_119,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),u1_struct_0(B_121))))
      | ~ v1_funct_2(C_119,u1_struct_0('#skF_1'),u1_struct_0(B_121))
      | ~ v1_funct_1(C_119)
      | ~ l1_pre_topc(B_121)
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_73,c_548])).

tff(c_574,plain,(
    ! [C_122,B_123] :
      ( v2_funct_1(C_122)
      | ~ v3_tops_2(C_122,'#skF_1',B_123)
      | ~ m1_subset_1(C_122,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),u1_struct_0(B_123))))
      | ~ v1_funct_2(C_122,k2_struct_0('#skF_1'),u1_struct_0(B_123))
      | ~ v1_funct_1(C_122)
      | ~ l1_pre_topc(B_123) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_73,c_555])).

tff(c_584,plain,(
    ! [C_122] :
      ( v2_funct_1(C_122)
      | ~ v3_tops_2(C_122,'#skF_1','#skF_2')
      | ~ m1_subset_1(C_122,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_122,k2_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_122)
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_574])).

tff(c_596,plain,(
    ! [C_125] :
      ( v2_funct_1(C_125)
      | ~ v3_tops_2(C_125,'#skF_1','#skF_2')
      | ~ m1_subset_1(C_125,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_125,k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_125) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_72,c_584])).

tff(c_603,plain,
    ( v2_funct_1('#skF_3')
    | ~ v3_tops_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_86,c_596])).

tff(c_607,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_84,c_46,c_603])).

tff(c_609,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_547,c_607])).

tff(c_610,plain,(
    k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_541])).

tff(c_44,plain,(
    ~ v3_tops_2(k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3'),'#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_94,plain,(
    ~ v3_tops_2(k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3'),'#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_72,c_44])).

tff(c_615,plain,(
    ~ v3_tops_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_610,c_94])).

tff(c_95,plain,(
    ! [A_51,B_52,C_53] :
      ( v1_funct_1(k2_tops_2(A_51,B_52,C_53))
      | ~ m1_subset_1(C_53,k1_zfmisc_1(k2_zfmisc_1(A_51,B_52)))
      | ~ v1_funct_2(C_53,A_51,B_52)
      | ~ v1_funct_1(C_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_98,plain,
    ( v1_funct_1(k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3'))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_86,c_95])).

tff(c_101,plain,(
    v1_funct_1(k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_84,c_98])).

tff(c_614,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_610,c_101])).

tff(c_108,plain,(
    ! [A_57,B_58,C_59] :
      ( v1_funct_2(k2_tops_2(A_57,B_58,C_59),B_58,A_57)
      | ~ m1_subset_1(C_59,k1_zfmisc_1(k2_zfmisc_1(A_57,B_58)))
      | ~ v1_funct_2(C_59,A_57,B_58)
      | ~ v1_funct_1(C_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_110,plain,
    ( v1_funct_2(k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3'),k2_struct_0('#skF_2'),k2_struct_0('#skF_1'))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_86,c_108])).

tff(c_113,plain,(
    v1_funct_2(k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3'),k2_struct_0('#skF_2'),k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_84,c_110])).

tff(c_613,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),k2_struct_0('#skF_2'),k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_610,c_113])).

tff(c_542,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_150])).

tff(c_611,plain,(
    v2_funct_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_541])).

tff(c_56,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_14626,plain,(
    ! [B_918,A_919,C_920] :
      ( k2_relset_1(u1_struct_0(B_918),u1_struct_0(A_919),k2_tops_2(u1_struct_0(A_919),u1_struct_0(B_918),C_920)) = k2_struct_0(A_919)
      | ~ v2_funct_1(C_920)
      | k2_relset_1(u1_struct_0(A_919),u1_struct_0(B_918),C_920) != k2_struct_0(B_918)
      | ~ m1_subset_1(C_920,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_919),u1_struct_0(B_918))))
      | ~ v1_funct_2(C_920,u1_struct_0(A_919),u1_struct_0(B_918))
      | ~ v1_funct_1(C_920)
      | ~ l1_struct_0(B_918)
      | v2_struct_0(B_918)
      | ~ l1_struct_0(A_919) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_14656,plain,(
    ! [A_919,C_920] :
      ( k2_relset_1(u1_struct_0('#skF_2'),u1_struct_0(A_919),k2_tops_2(u1_struct_0(A_919),k2_struct_0('#skF_2'),C_920)) = k2_struct_0(A_919)
      | ~ v2_funct_1(C_920)
      | k2_relset_1(u1_struct_0(A_919),u1_struct_0('#skF_2'),C_920) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_920,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_919),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_920,u1_struct_0(A_919),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_920)
      | ~ l1_struct_0('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_struct_0(A_919) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_14626])).

tff(c_14667,plain,(
    ! [A_919,C_920] :
      ( k2_relset_1(k2_struct_0('#skF_2'),u1_struct_0(A_919),k2_tops_2(u1_struct_0(A_919),k2_struct_0('#skF_2'),C_920)) = k2_struct_0(A_919)
      | ~ v2_funct_1(C_920)
      | k2_relset_1(u1_struct_0(A_919),k2_struct_0('#skF_2'),C_920) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_920,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_919),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_920,u1_struct_0(A_919),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_920)
      | ~ l1_struct_0('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_struct_0(A_919) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_72,c_72,c_72,c_14656])).

tff(c_14668,plain,(
    ! [A_919,C_920] :
      ( k2_relset_1(k2_struct_0('#skF_2'),u1_struct_0(A_919),k2_tops_2(u1_struct_0(A_919),k2_struct_0('#skF_2'),C_920)) = k2_struct_0(A_919)
      | ~ v2_funct_1(C_920)
      | k2_relset_1(u1_struct_0(A_919),k2_struct_0('#skF_2'),C_920) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_920,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_919),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_920,u1_struct_0(A_919),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_920)
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0(A_919) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_14667])).

tff(c_14697,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_14668])).

tff(c_14700,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_16,c_14697])).

tff(c_14704,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_14700])).

tff(c_14706,plain,(
    l1_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_14668])).

tff(c_14764,plain,(
    ! [B_929,A_930,C_931] :
      ( k1_relset_1(u1_struct_0(B_929),u1_struct_0(A_930),k2_tops_2(u1_struct_0(A_930),u1_struct_0(B_929),C_931)) = k2_struct_0(B_929)
      | ~ v2_funct_1(C_931)
      | k2_relset_1(u1_struct_0(A_930),u1_struct_0(B_929),C_931) != k2_struct_0(B_929)
      | ~ m1_subset_1(C_931,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_930),u1_struct_0(B_929))))
      | ~ v1_funct_2(C_931,u1_struct_0(A_930),u1_struct_0(B_929))
      | ~ v1_funct_1(C_931)
      | ~ l1_struct_0(B_929)
      | v2_struct_0(B_929)
      | ~ l1_struct_0(A_930) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_14794,plain,(
    ! [A_930,C_931] :
      ( k1_relset_1(u1_struct_0('#skF_2'),u1_struct_0(A_930),k2_tops_2(u1_struct_0(A_930),k2_struct_0('#skF_2'),C_931)) = k2_struct_0('#skF_2')
      | ~ v2_funct_1(C_931)
      | k2_relset_1(u1_struct_0(A_930),u1_struct_0('#skF_2'),C_931) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_931,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_930),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_931,u1_struct_0(A_930),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_931)
      | ~ l1_struct_0('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_struct_0(A_930) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_14764])).

tff(c_14809,plain,(
    ! [A_930,C_931] :
      ( k1_relset_1(k2_struct_0('#skF_2'),u1_struct_0(A_930),k2_tops_2(u1_struct_0(A_930),k2_struct_0('#skF_2'),C_931)) = k2_struct_0('#skF_2')
      | ~ v2_funct_1(C_931)
      | k2_relset_1(u1_struct_0(A_930),k2_struct_0('#skF_2'),C_931) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_931,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_930),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_931,u1_struct_0(A_930),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_931)
      | v2_struct_0('#skF_2')
      | ~ l1_struct_0(A_930) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14706,c_72,c_72,c_72,c_72,c_14794])).

tff(c_14825,plain,(
    ! [A_933,C_934] :
      ( k1_relset_1(k2_struct_0('#skF_2'),u1_struct_0(A_933),k2_tops_2(u1_struct_0(A_933),k2_struct_0('#skF_2'),C_934)) = k2_struct_0('#skF_2')
      | ~ v2_funct_1(C_934)
      | k2_relset_1(u1_struct_0(A_933),k2_struct_0('#skF_2'),C_934) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_934,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_933),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_934,u1_struct_0(A_933),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_934)
      | ~ l1_struct_0(A_933) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_14809])).

tff(c_14837,plain,(
    ! [C_934] :
      ( k1_relset_1(k2_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_934)) = k2_struct_0('#skF_2')
      | ~ v2_funct_1(C_934)
      | k2_relset_1(u1_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_934) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_934,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_934,u1_struct_0('#skF_1'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_934)
      | ~ l1_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_73,c_14825])).

tff(c_14847,plain,(
    ! [C_934] :
      ( k1_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_934)) = k2_struct_0('#skF_2')
      | ~ v2_funct_1(C_934)
      | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_934) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_934,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_934,k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_934)
      | ~ l1_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_73,c_73,c_73,c_14837])).

tff(c_23908,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_14847])).

tff(c_23911,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_16,c_23908])).

tff(c_23915,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_23911])).

tff(c_23917,plain,(
    l1_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_14847])).

tff(c_14834,plain,(
    ! [C_934] :
      ( k1_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_934)) = k2_struct_0('#skF_2')
      | ~ v2_funct_1(C_934)
      | k2_relset_1(u1_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_934) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_934,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_934,u1_struct_0('#skF_1'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_934)
      | ~ l1_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_73,c_14825])).

tff(c_14846,plain,(
    ! [C_934] :
      ( k1_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_934)) = k2_struct_0('#skF_2')
      | ~ v2_funct_1(C_934)
      | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_934) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_934,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_934,k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_934)
      | ~ l1_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_73,c_73,c_73,c_14834])).

tff(c_23925,plain,(
    ! [C_1353] :
      ( k1_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_1353)) = k2_struct_0('#skF_2')
      | ~ v2_funct_1(C_1353)
      | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_1353) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_1353,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_1353,k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_1353) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_23917,c_14846])).

tff(c_23940,plain,
    ( k1_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) = k2_struct_0('#skF_2')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_610,c_23925])).

tff(c_23948,plain,(
    k1_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_84,c_86,c_542,c_611,c_23940])).

tff(c_32,plain,(
    ! [A_21,B_22,C_23] :
      ( m1_subset_1(k2_tops_2(A_21,B_22,C_23),k1_zfmisc_1(k2_zfmisc_1(B_22,A_21)))
      | ~ m1_subset_1(C_23,k1_zfmisc_1(k2_zfmisc_1(A_21,B_22)))
      | ~ v1_funct_2(C_23,A_21,B_22)
      | ~ v1_funct_1(C_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_619,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'))))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_610,c_32])).

tff(c_623,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_84,c_86,c_619])).

tff(c_18,plain,(
    ! [A_11,B_12,C_13] :
      ( k2_tops_2(A_11,B_12,C_13) = k2_funct_1(C_13)
      | ~ v2_funct_1(C_13)
      | k2_relset_1(A_11,B_12,C_13) != B_12
      | ~ m1_subset_1(C_13,k1_zfmisc_1(k2_zfmisc_1(A_11,B_12)))
      | ~ v1_funct_2(C_13,A_11,B_12)
      | ~ v1_funct_1(C_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_653,plain,
    ( k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) != k2_struct_0('#skF_1')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),k2_struct_0('#skF_2'),k2_struct_0('#skF_1'))
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_623,c_18])).

tff(c_669,plain,
    ( k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) != k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_614,c_613,c_653])).

tff(c_744,plain,(
    k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) != k2_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_669])).

tff(c_1227,plain,(
    ! [B_196,A_197,C_198] :
      ( k2_relset_1(u1_struct_0(B_196),u1_struct_0(A_197),k2_tops_2(u1_struct_0(A_197),u1_struct_0(B_196),C_198)) = k2_struct_0(A_197)
      | ~ v2_funct_1(C_198)
      | k2_relset_1(u1_struct_0(A_197),u1_struct_0(B_196),C_198) != k2_struct_0(B_196)
      | ~ m1_subset_1(C_198,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_197),u1_struct_0(B_196))))
      | ~ v1_funct_2(C_198,u1_struct_0(A_197),u1_struct_0(B_196))
      | ~ v1_funct_1(C_198)
      | ~ l1_struct_0(B_196)
      | v2_struct_0(B_196)
      | ~ l1_struct_0(A_197) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_1257,plain,(
    ! [A_197,C_198] :
      ( k2_relset_1(u1_struct_0('#skF_2'),u1_struct_0(A_197),k2_tops_2(u1_struct_0(A_197),k2_struct_0('#skF_2'),C_198)) = k2_struct_0(A_197)
      | ~ v2_funct_1(C_198)
      | k2_relset_1(u1_struct_0(A_197),u1_struct_0('#skF_2'),C_198) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_198,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_197),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_198,u1_struct_0(A_197),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_198)
      | ~ l1_struct_0('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_struct_0(A_197) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_1227])).

tff(c_1268,plain,(
    ! [A_197,C_198] :
      ( k2_relset_1(k2_struct_0('#skF_2'),u1_struct_0(A_197),k2_tops_2(u1_struct_0(A_197),k2_struct_0('#skF_2'),C_198)) = k2_struct_0(A_197)
      | ~ v2_funct_1(C_198)
      | k2_relset_1(u1_struct_0(A_197),k2_struct_0('#skF_2'),C_198) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_198,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_197),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_198,u1_struct_0(A_197),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_198)
      | ~ l1_struct_0('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_struct_0(A_197) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_72,c_72,c_72,c_1257])).

tff(c_1269,plain,(
    ! [A_197,C_198] :
      ( k2_relset_1(k2_struct_0('#skF_2'),u1_struct_0(A_197),k2_tops_2(u1_struct_0(A_197),k2_struct_0('#skF_2'),C_198)) = k2_struct_0(A_197)
      | ~ v2_funct_1(C_198)
      | k2_relset_1(u1_struct_0(A_197),k2_struct_0('#skF_2'),C_198) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_198,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_197),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_198,u1_struct_0(A_197),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_198)
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0(A_197) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_1268])).

tff(c_1289,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_1269])).

tff(c_1292,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_16,c_1289])).

tff(c_1296,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_1292])).

tff(c_1298,plain,(
    l1_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_1269])).

tff(c_1335,plain,(
    ! [B_206,A_207,C_208] :
      ( k1_relset_1(u1_struct_0(B_206),u1_struct_0(A_207),k2_tops_2(u1_struct_0(A_207),u1_struct_0(B_206),C_208)) = k2_struct_0(B_206)
      | ~ v2_funct_1(C_208)
      | k2_relset_1(u1_struct_0(A_207),u1_struct_0(B_206),C_208) != k2_struct_0(B_206)
      | ~ m1_subset_1(C_208,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_207),u1_struct_0(B_206))))
      | ~ v1_funct_2(C_208,u1_struct_0(A_207),u1_struct_0(B_206))
      | ~ v1_funct_1(C_208)
      | ~ l1_struct_0(B_206)
      | v2_struct_0(B_206)
      | ~ l1_struct_0(A_207) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_1356,plain,(
    ! [A_207,C_208] :
      ( k1_relset_1(k2_struct_0('#skF_2'),u1_struct_0(A_207),k2_tops_2(u1_struct_0(A_207),u1_struct_0('#skF_2'),C_208)) = k2_struct_0('#skF_2')
      | ~ v2_funct_1(C_208)
      | k2_relset_1(u1_struct_0(A_207),u1_struct_0('#skF_2'),C_208) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_208,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_207),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_208,u1_struct_0(A_207),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_208)
      | ~ l1_struct_0('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_struct_0(A_207) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_1335])).

tff(c_1373,plain,(
    ! [A_207,C_208] :
      ( k1_relset_1(k2_struct_0('#skF_2'),u1_struct_0(A_207),k2_tops_2(u1_struct_0(A_207),k2_struct_0('#skF_2'),C_208)) = k2_struct_0('#skF_2')
      | ~ v2_funct_1(C_208)
      | k2_relset_1(u1_struct_0(A_207),k2_struct_0('#skF_2'),C_208) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_208,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_207),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_208,u1_struct_0(A_207),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_208)
      | v2_struct_0('#skF_2')
      | ~ l1_struct_0(A_207) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1298,c_72,c_72,c_72,c_72,c_1356])).

tff(c_1409,plain,(
    ! [A_214,C_215] :
      ( k1_relset_1(k2_struct_0('#skF_2'),u1_struct_0(A_214),k2_tops_2(u1_struct_0(A_214),k2_struct_0('#skF_2'),C_215)) = k2_struct_0('#skF_2')
      | ~ v2_funct_1(C_215)
      | k2_relset_1(u1_struct_0(A_214),k2_struct_0('#skF_2'),C_215) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_215,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_214),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_215,u1_struct_0(A_214),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_215)
      | ~ l1_struct_0(A_214) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_1373])).

tff(c_1418,plain,(
    ! [C_215] :
      ( k1_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_215)) = k2_struct_0('#skF_2')
      | ~ v2_funct_1(C_215)
      | k2_relset_1(u1_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_215) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_215,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_215,u1_struct_0('#skF_1'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_215)
      | ~ l1_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_73,c_1409])).

tff(c_1430,plain,(
    ! [C_215] :
      ( k1_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_215)) = k2_struct_0('#skF_2')
      | ~ v2_funct_1(C_215)
      | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_215) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_215,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_215,k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_215)
      | ~ l1_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_73,c_73,c_73,c_1418])).

tff(c_1579,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_1430])).

tff(c_1582,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_16,c_1579])).

tff(c_1586,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_1582])).

tff(c_1588,plain,(
    l1_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_1430])).

tff(c_1541,plain,(
    ! [A_229,C_230] :
      ( k2_relset_1(k2_struct_0('#skF_2'),u1_struct_0(A_229),k2_tops_2(u1_struct_0(A_229),k2_struct_0('#skF_2'),C_230)) = k2_struct_0(A_229)
      | ~ v2_funct_1(C_230)
      | k2_relset_1(u1_struct_0(A_229),k2_struct_0('#skF_2'),C_230) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_230,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_229),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_230,u1_struct_0(A_229),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_230)
      | ~ l1_struct_0(A_229) ) ),
    inference(splitRight,[status(thm)],[c_1269])).

tff(c_1553,plain,(
    ! [C_230] :
      ( k2_relset_1(k2_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_230)) = k2_struct_0('#skF_1')
      | ~ v2_funct_1(C_230)
      | k2_relset_1(u1_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_230) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_230,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_230,u1_struct_0('#skF_1'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_230)
      | ~ l1_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_73,c_1541])).

tff(c_1563,plain,(
    ! [C_230] :
      ( k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_230)) = k2_struct_0('#skF_1')
      | ~ v2_funct_1(C_230)
      | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_230) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_230,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_230,k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_230)
      | ~ l1_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_73,c_73,c_73,c_1553])).

tff(c_1667,plain,(
    ! [C_238] :
      ( k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_238)) = k2_struct_0('#skF_1')
      | ~ v2_funct_1(C_238)
      | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_238) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_238,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_238,k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_238) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1588,c_1563])).

tff(c_1676,plain,
    ( k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) = k2_struct_0('#skF_1')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_610,c_1667])).

tff(c_1680,plain,(
    k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) = k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_84,c_86,c_542,c_611,c_1676])).

tff(c_1682,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_744,c_1680])).

tff(c_1684,plain,(
    k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) = k2_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_669])).

tff(c_8,plain,(
    ! [C_4,A_2,B_3] :
      ( v1_relat_1(C_4)
      | ~ m1_subset_1(C_4,k1_zfmisc_1(k2_zfmisc_1(A_2,B_3))) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_90,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_86,c_8])).

tff(c_2,plain,(
    ! [A_1] :
      ( v2_funct_1(k2_funct_1(A_1))
      | ~ v2_funct_1(A_1)
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1683,plain,
    ( ~ v2_funct_1(k2_funct_1('#skF_3'))
    | k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_669])).

tff(c_1689,plain,(
    ~ v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1683])).

tff(c_1692,plain,
    ( ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2,c_1689])).

tff(c_1696,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_52,c_611,c_1692])).

tff(c_1698,plain,(
    v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1683])).

tff(c_14535,plain,(
    ! [A_914,B_915,C_916] :
      ( v5_pre_topc(k2_tops_2(u1_struct_0(A_914),u1_struct_0(B_915),C_916),B_915,A_914)
      | ~ v3_tops_2(C_916,A_914,B_915)
      | ~ m1_subset_1(C_916,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_914),u1_struct_0(B_915))))
      | ~ v1_funct_2(C_916,u1_struct_0(A_914),u1_struct_0(B_915))
      | ~ v1_funct_1(C_916)
      | ~ l1_pre_topc(B_915)
      | ~ l1_pre_topc(A_914) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_14546,plain,(
    ! [A_914,C_916] :
      ( v5_pre_topc(k2_tops_2(u1_struct_0(A_914),u1_struct_0('#skF_2'),C_916),'#skF_2',A_914)
      | ~ v3_tops_2(C_916,A_914,'#skF_2')
      | ~ m1_subset_1(C_916,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_914),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_916,u1_struct_0(A_914),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_916)
      | ~ l1_pre_topc('#skF_2')
      | ~ l1_pre_topc(A_914) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_14535])).

tff(c_20842,plain,(
    ! [A_1223,C_1224] :
      ( v5_pre_topc(k2_tops_2(u1_struct_0(A_1223),k2_struct_0('#skF_2'),C_1224),'#skF_2',A_1223)
      | ~ v3_tops_2(C_1224,A_1223,'#skF_2')
      | ~ m1_subset_1(C_1224,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1223),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_1224,u1_struct_0(A_1223),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_1224)
      | ~ l1_pre_topc(A_1223) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_72,c_72,c_14546])).

tff(c_20847,plain,(
    ! [C_1224] :
      ( v5_pre_topc(k2_tops_2(u1_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_1224),'#skF_2','#skF_1')
      | ~ v3_tops_2(C_1224,'#skF_1','#skF_2')
      | ~ m1_subset_1(C_1224,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_1224,u1_struct_0('#skF_1'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_1224)
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_73,c_20842])).

tff(c_20900,plain,(
    ! [C_1228] :
      ( v5_pre_topc(k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_1228),'#skF_2','#skF_1')
      | ~ v3_tops_2(C_1228,'#skF_1','#skF_2')
      | ~ m1_subset_1(C_1228,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_1228,k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_1228) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_73,c_73,c_20847])).

tff(c_20913,plain,
    ( v5_pre_topc(k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3'),'#skF_2','#skF_1')
    | ~ v3_tops_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_86,c_20900])).

tff(c_20923,plain,(
    v5_pre_topc(k2_funct_1('#skF_3'),'#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_84,c_46,c_610,c_20913])).

tff(c_718,plain,(
    ! [C_133,A_134,B_135] :
      ( v5_pre_topc(C_133,A_134,B_135)
      | ~ v3_tops_2(C_133,A_134,B_135)
      | ~ m1_subset_1(C_133,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_134),u1_struct_0(B_135))))
      | ~ v1_funct_2(C_133,u1_struct_0(A_134),u1_struct_0(B_135))
      | ~ v1_funct_1(C_133)
      | ~ l1_pre_topc(B_135)
      | ~ l1_pre_topc(A_134) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_725,plain,(
    ! [C_133,B_135] :
      ( v5_pre_topc(C_133,'#skF_1',B_135)
      | ~ v3_tops_2(C_133,'#skF_1',B_135)
      | ~ m1_subset_1(C_133,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),u1_struct_0(B_135))))
      | ~ v1_funct_2(C_133,u1_struct_0('#skF_1'),u1_struct_0(B_135))
      | ~ v1_funct_1(C_133)
      | ~ l1_pre_topc(B_135)
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_73,c_718])).

tff(c_14158,plain,(
    ! [C_874,B_875] :
      ( v5_pre_topc(C_874,'#skF_1',B_875)
      | ~ v3_tops_2(C_874,'#skF_1',B_875)
      | ~ m1_subset_1(C_874,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),u1_struct_0(B_875))))
      | ~ v1_funct_2(C_874,k2_struct_0('#skF_1'),u1_struct_0(B_875))
      | ~ v1_funct_1(C_874)
      | ~ l1_pre_topc(B_875) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_73,c_725])).

tff(c_14168,plain,(
    ! [C_874] :
      ( v5_pre_topc(C_874,'#skF_1','#skF_2')
      | ~ v3_tops_2(C_874,'#skF_1','#skF_2')
      | ~ m1_subset_1(C_874,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_874,k2_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_874)
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_14158])).

tff(c_14180,plain,(
    ! [C_877] :
      ( v5_pre_topc(C_877,'#skF_1','#skF_2')
      | ~ v3_tops_2(C_877,'#skF_1','#skF_2')
      | ~ m1_subset_1(C_877,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_877,k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_877) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_72,c_14168])).

tff(c_14190,plain,
    ( v5_pre_topc('#skF_3','#skF_1','#skF_2')
    | ~ v3_tops_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_86,c_14180])).

tff(c_14197,plain,(
    v5_pre_topc('#skF_3','#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_84,c_46,c_14190])).

tff(c_1697,plain,(
    k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1683])).

tff(c_36,plain,(
    ! [A_21,B_22,C_23] :
      ( v1_funct_1(k2_tops_2(A_21,B_22,C_23))
      | ~ m1_subset_1(C_23,k1_zfmisc_1(k2_zfmisc_1(A_21,B_22)))
      | ~ v1_funct_2(C_23,A_21,B_22)
      | ~ v1_funct_1(C_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_663,plain,
    ( v1_funct_1(k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')))
    | ~ v1_funct_2(k2_funct_1('#skF_3'),k2_struct_0('#skF_2'),k2_struct_0('#skF_1'))
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_623,c_36])).

tff(c_681,plain,(
    v1_funct_1(k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_614,c_613,c_663])).

tff(c_1713,plain,(
    v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1697,c_681])).

tff(c_34,plain,(
    ! [A_21,B_22,C_23] :
      ( v1_funct_2(k2_tops_2(A_21,B_22,C_23),B_22,A_21)
      | ~ m1_subset_1(C_23,k1_zfmisc_1(k2_zfmisc_1(A_21,B_22)))
      | ~ v1_funct_2(C_23,A_21,B_22)
      | ~ v1_funct_1(C_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_658,plain,
    ( v1_funct_2(k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')),k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_2(k2_funct_1('#skF_3'),k2_struct_0('#skF_2'),k2_struct_0('#skF_1'))
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_623,c_34])).

tff(c_675,plain,(
    v1_funct_2(k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')),k2_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_614,c_613,c_658])).

tff(c_1712,plain,(
    v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')),k2_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1697,c_675])).

tff(c_1718,plain,
    ( m1_subset_1(k2_funct_1(k2_funct_1('#skF_3')),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
    | ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'))))
    | ~ v1_funct_2(k2_funct_1('#skF_3'),k2_struct_0('#skF_2'),k2_struct_0('#skF_1'))
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1697,c_32])).

tff(c_1722,plain,(
    m1_subset_1(k2_funct_1(k2_funct_1('#skF_3')),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_614,c_613,c_623,c_1718])).

tff(c_14924,plain,(
    ! [A_943,B_944,C_945] :
      ( r2_funct_2(u1_struct_0(A_943),u1_struct_0(B_944),k2_tops_2(u1_struct_0(B_944),u1_struct_0(A_943),k2_tops_2(u1_struct_0(A_943),u1_struct_0(B_944),C_945)),C_945)
      | ~ v2_funct_1(C_945)
      | k2_relset_1(u1_struct_0(A_943),u1_struct_0(B_944),C_945) != k2_struct_0(B_944)
      | ~ m1_subset_1(C_945,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_943),u1_struct_0(B_944))))
      | ~ v1_funct_2(C_945,u1_struct_0(A_943),u1_struct_0(B_944))
      | ~ v1_funct_1(C_945)
      | ~ l1_struct_0(B_944)
      | v2_struct_0(B_944)
      | ~ l1_struct_0(A_943) ) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_14953,plain,(
    ! [A_943,C_945] :
      ( r2_funct_2(u1_struct_0(A_943),u1_struct_0('#skF_2'),k2_tops_2(k2_struct_0('#skF_2'),u1_struct_0(A_943),k2_tops_2(u1_struct_0(A_943),u1_struct_0('#skF_2'),C_945)),C_945)
      | ~ v2_funct_1(C_945)
      | k2_relset_1(u1_struct_0(A_943),u1_struct_0('#skF_2'),C_945) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_945,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_943),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_945,u1_struct_0(A_943),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_945)
      | ~ l1_struct_0('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_struct_0(A_943) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_14924])).

tff(c_14976,plain,(
    ! [A_943,C_945] :
      ( r2_funct_2(u1_struct_0(A_943),k2_struct_0('#skF_2'),k2_tops_2(k2_struct_0('#skF_2'),u1_struct_0(A_943),k2_tops_2(u1_struct_0(A_943),k2_struct_0('#skF_2'),C_945)),C_945)
      | ~ v2_funct_1(C_945)
      | k2_relset_1(u1_struct_0(A_943),k2_struct_0('#skF_2'),C_945) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_945,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_943),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_945,u1_struct_0(A_943),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_945)
      | v2_struct_0('#skF_2')
      | ~ l1_struct_0(A_943) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14706,c_72,c_72,c_72,c_72,c_72,c_14953])).

tff(c_20768,plain,(
    ! [A_1217,C_1218] :
      ( r2_funct_2(u1_struct_0(A_1217),k2_struct_0('#skF_2'),k2_tops_2(k2_struct_0('#skF_2'),u1_struct_0(A_1217),k2_tops_2(u1_struct_0(A_1217),k2_struct_0('#skF_2'),C_1218)),C_1218)
      | ~ v2_funct_1(C_1218)
      | k2_relset_1(u1_struct_0(A_1217),k2_struct_0('#skF_2'),C_1218) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_1218,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1217),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_1218,u1_struct_0(A_1217),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_1218)
      | ~ l1_struct_0(A_1217) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_14976])).

tff(c_20773,plain,(
    ! [C_1218] :
      ( r2_funct_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),k2_tops_2(k2_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_1218)),C_1218)
      | ~ v2_funct_1(C_1218)
      | k2_relset_1(u1_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_1218) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_1218,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_1218,u1_struct_0('#skF_1'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_1218)
      | ~ l1_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_73,c_20768])).

tff(c_20790,plain,(
    ! [C_1218] :
      ( r2_funct_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_1218)),C_1218)
      | ~ v2_funct_1(C_1218)
      | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_1218) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_1218,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_1218,k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_1218)
      | ~ l1_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_73,c_73,c_73,c_73,c_20773])).

tff(c_25322,plain,(
    ! [C_1405] :
      ( r2_funct_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_1405)),C_1405)
      | ~ v2_funct_1(C_1405)
      | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_1405) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_1405,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_1405,k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_1405) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_23917,c_20790])).

tff(c_25336,plain,
    ( r2_funct_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')),'#skF_3')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_610,c_25322])).

tff(c_25345,plain,(
    r2_funct_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),k2_funct_1(k2_funct_1('#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_84,c_86,c_542,c_611,c_1697,c_25336])).

tff(c_12,plain,(
    ! [D_8,C_7,A_5,B_6] :
      ( D_8 = C_7
      | ~ r2_funct_2(A_5,B_6,C_7,D_8)
      | ~ m1_subset_1(D_8,k1_zfmisc_1(k2_zfmisc_1(A_5,B_6)))
      | ~ v1_funct_2(D_8,A_5,B_6)
      | ~ v1_funct_1(D_8)
      | ~ m1_subset_1(C_7,k1_zfmisc_1(k2_zfmisc_1(A_5,B_6)))
      | ~ v1_funct_2(C_7,A_5,B_6)
      | ~ v1_funct_1(C_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_25347,plain,
    ( k2_funct_1(k2_funct_1('#skF_3')) = '#skF_3'
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1(k2_funct_1(k2_funct_1('#skF_3')),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
    | ~ v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')),k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_25345,c_12])).

tff(c_25350,plain,(
    k2_funct_1(k2_funct_1('#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1713,c_1712,c_1722,c_52,c_84,c_86,c_25347])).

tff(c_25434,plain,(
    k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_25350,c_1697])).

tff(c_15402,plain,(
    ! [C_988,A_989,B_990] :
      ( v3_tops_2(C_988,A_989,B_990)
      | ~ v5_pre_topc(k2_tops_2(u1_struct_0(A_989),u1_struct_0(B_990),C_988),B_990,A_989)
      | ~ v5_pre_topc(C_988,A_989,B_990)
      | ~ v2_funct_1(C_988)
      | k2_relset_1(u1_struct_0(A_989),u1_struct_0(B_990),C_988) != k2_struct_0(B_990)
      | k1_relset_1(u1_struct_0(A_989),u1_struct_0(B_990),C_988) != k2_struct_0(A_989)
      | ~ m1_subset_1(C_988,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_989),u1_struct_0(B_990))))
      | ~ v1_funct_2(C_988,u1_struct_0(A_989),u1_struct_0(B_990))
      | ~ v1_funct_1(C_988)
      | ~ l1_pre_topc(B_990)
      | ~ l1_pre_topc(A_989) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_15406,plain,(
    ! [C_988,A_989] :
      ( v3_tops_2(C_988,A_989,'#skF_1')
      | ~ v5_pre_topc(k2_tops_2(u1_struct_0(A_989),k2_struct_0('#skF_1'),C_988),'#skF_1',A_989)
      | ~ v5_pre_topc(C_988,A_989,'#skF_1')
      | ~ v2_funct_1(C_988)
      | k2_relset_1(u1_struct_0(A_989),u1_struct_0('#skF_1'),C_988) != k2_struct_0('#skF_1')
      | k1_relset_1(u1_struct_0(A_989),u1_struct_0('#skF_1'),C_988) != k2_struct_0(A_989)
      | ~ m1_subset_1(C_988,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_989),u1_struct_0('#skF_1'))))
      | ~ v1_funct_2(C_988,u1_struct_0(A_989),u1_struct_0('#skF_1'))
      | ~ v1_funct_1(C_988)
      | ~ l1_pre_topc('#skF_1')
      | ~ l1_pre_topc(A_989) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_73,c_15402])).

tff(c_25972,plain,(
    ! [C_1433,A_1434] :
      ( v3_tops_2(C_1433,A_1434,'#skF_1')
      | ~ v5_pre_topc(k2_tops_2(u1_struct_0(A_1434),k2_struct_0('#skF_1'),C_1433),'#skF_1',A_1434)
      | ~ v5_pre_topc(C_1433,A_1434,'#skF_1')
      | ~ v2_funct_1(C_1433)
      | k2_relset_1(u1_struct_0(A_1434),k2_struct_0('#skF_1'),C_1433) != k2_struct_0('#skF_1')
      | k1_relset_1(u1_struct_0(A_1434),k2_struct_0('#skF_1'),C_1433) != k2_struct_0(A_1434)
      | ~ m1_subset_1(C_1433,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1434),k2_struct_0('#skF_1'))))
      | ~ v1_funct_2(C_1433,u1_struct_0(A_1434),k2_struct_0('#skF_1'))
      | ~ v1_funct_1(C_1433)
      | ~ l1_pre_topc(A_1434) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_73,c_73,c_73,c_73,c_15406])).

tff(c_25976,plain,(
    ! [C_1433] :
      ( v3_tops_2(C_1433,'#skF_2','#skF_1')
      | ~ v5_pre_topc(k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),C_1433),'#skF_1','#skF_2')
      | ~ v5_pre_topc(C_1433,'#skF_2','#skF_1')
      | ~ v2_funct_1(C_1433)
      | k2_relset_1(u1_struct_0('#skF_2'),k2_struct_0('#skF_1'),C_1433) != k2_struct_0('#skF_1')
      | k1_relset_1(u1_struct_0('#skF_2'),k2_struct_0('#skF_1'),C_1433) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_1433,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),k2_struct_0('#skF_1'))))
      | ~ v1_funct_2(C_1433,u1_struct_0('#skF_2'),k2_struct_0('#skF_1'))
      | ~ v1_funct_1(C_1433)
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_25972])).

tff(c_25987,plain,(
    ! [C_1436] :
      ( v3_tops_2(C_1436,'#skF_2','#skF_1')
      | ~ v5_pre_topc(k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),C_1436),'#skF_1','#skF_2')
      | ~ v5_pre_topc(C_1436,'#skF_2','#skF_1')
      | ~ v2_funct_1(C_1436)
      | k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),C_1436) != k2_struct_0('#skF_1')
      | k1_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),C_1436) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_1436,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'))))
      | ~ v1_funct_2(C_1436,k2_struct_0('#skF_2'),k2_struct_0('#skF_1'))
      | ~ v1_funct_1(C_1436) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_72,c_72,c_72,c_72,c_25976])).

tff(c_25990,plain,
    ( v3_tops_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ v5_pre_topc(k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')),'#skF_1','#skF_2')
    | ~ v5_pre_topc(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) != k2_struct_0('#skF_1')
    | k1_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) != k2_struct_0('#skF_2')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),k2_struct_0('#skF_2'),k2_struct_0('#skF_1'))
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_623,c_25987])).

tff(c_25997,plain,(
    v3_tops_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_614,c_613,c_23948,c_1684,c_1698,c_20923,c_14197,c_25434,c_25990])).

tff(c_25999,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_615,c_25997])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:27:38 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 15.23/8.27  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 15.23/8.29  
% 15.23/8.29  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 15.23/8.29  %$ r2_funct_2 > v5_pre_topc > v3_tops_2 > v1_funct_2 > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_relat_1 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k2_tops_2 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k2_struct_0 > k2_funct_1 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 15.23/8.29  
% 15.23/8.29  %Foreground sorts:
% 15.23/8.29  
% 15.23/8.29  
% 15.23/8.29  %Background operators:
% 15.23/8.29  
% 15.23/8.29  
% 15.23/8.29  %Foreground operators:
% 15.23/8.29  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 15.23/8.29  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 15.23/8.29  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 15.23/8.29  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 15.23/8.29  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 15.23/8.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 15.23/8.29  tff(v3_tops_2, type, v3_tops_2: ($i * $i * $i) > $o).
% 15.23/8.29  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 15.23/8.29  tff(k2_tops_2, type, k2_tops_2: ($i * $i * $i) > $i).
% 15.23/8.29  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 15.23/8.29  tff('#skF_2', type, '#skF_2': $i).
% 15.23/8.29  tff('#skF_3', type, '#skF_3': $i).
% 15.23/8.29  tff('#skF_1', type, '#skF_1': $i).
% 15.23/8.29  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 15.23/8.29  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 15.23/8.29  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 15.23/8.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 15.23/8.29  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 15.23/8.29  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 15.23/8.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 15.23/8.29  tff(v5_pre_topc, type, v5_pre_topc: ($i * $i * $i) > $o).
% 15.23/8.29  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 15.23/8.29  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 15.23/8.29  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 15.23/8.29  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 15.23/8.29  
% 15.23/8.32  tff(f_177, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: ((~v2_struct_0(B) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (v3_tops_2(C, A, B) => v3_tops_2(k2_tops_2(u1_struct_0(A), u1_struct_0(B), C), B, A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_tops_2)).
% 15.23/8.32  tff(f_65, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 15.23/8.32  tff(f_61, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 15.23/8.32  tff(f_77, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => (k2_tops_2(A, B, C) = k2_funct_1(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tops_2)).
% 15.23/8.32  tff(f_101, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (v3_tops_2(C, A, B) <=> (((((k1_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(A)) & (k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B))) & v2_funct_1(C)) & v5_pre_topc(C, A, B)) & v5_pre_topc(k2_tops_2(u1_struct_0(A), u1_struct_0(B), C), B, A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_tops_2)).
% 15.23/8.32  tff(f_113, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v1_funct_1(k2_tops_2(A, B, C)) & v1_funct_2(k2_tops_2(A, B, C), B, A)) & m1_subset_1(k2_tops_2(A, B, C), k1_zfmisc_1(k2_zfmisc_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tops_2)).
% 15.23/8.32  tff(f_136, axiom, (![A]: (l1_struct_0(A) => (![B]: ((~v2_struct_0(B) & l1_struct_0(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B)) & v2_funct_1(C)) => ((k1_relset_1(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)) = k2_struct_0(B)) & (k2_relset_1(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)) = k2_struct_0(A)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_tops_2)).
% 15.23/8.32  tff(f_41, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 15.23/8.32  tff(f_37, axiom, (![A]: (((v1_relat_1(A) & v1_funct_1(A)) & v2_funct_1(A)) => ((v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))) & v2_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_funct_1)).
% 15.23/8.32  tff(f_157, axiom, (![A]: (l1_struct_0(A) => (![B]: ((~v2_struct_0(B) & l1_struct_0(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B)) & v2_funct_1(C)) => r2_funct_2(u1_struct_0(A), u1_struct_0(B), k2_tops_2(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)), C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_tops_2)).
% 15.23/8.32  tff(f_57, axiom, (![A, B, C, D]: ((((((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(D)) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_funct_2(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_funct_2)).
% 15.23/8.32  tff(c_52, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_177])).
% 15.23/8.32  tff(c_58, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_177])).
% 15.23/8.32  tff(c_16, plain, (![A_10]: (l1_struct_0(A_10) | ~l1_pre_topc(A_10))), inference(cnfTransformation, [status(thm)], [f_65])).
% 15.23/8.32  tff(c_60, plain, (![A_43]: (u1_struct_0(A_43)=k2_struct_0(A_43) | ~l1_struct_0(A_43))), inference(cnfTransformation, [status(thm)], [f_61])).
% 15.23/8.32  tff(c_65, plain, (![A_44]: (u1_struct_0(A_44)=k2_struct_0(A_44) | ~l1_pre_topc(A_44))), inference(resolution, [status(thm)], [c_16, c_60])).
% 15.23/8.32  tff(c_73, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_58, c_65])).
% 15.23/8.32  tff(c_54, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_177])).
% 15.23/8.32  tff(c_72, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_54, c_65])).
% 15.23/8.32  tff(c_50, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_177])).
% 15.23/8.32  tff(c_75, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_50])).
% 15.23/8.32  tff(c_84, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_73, c_75])).
% 15.23/8.32  tff(c_48, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_177])).
% 15.23/8.32  tff(c_74, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_48])).
% 15.23/8.32  tff(c_86, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_73, c_74])).
% 15.23/8.32  tff(c_140, plain, (![A_66, B_67, C_68]: (k2_tops_2(A_66, B_67, C_68)=k2_funct_1(C_68) | ~v2_funct_1(C_68) | k2_relset_1(A_66, B_67, C_68)!=B_67 | ~m1_subset_1(C_68, k1_zfmisc_1(k2_zfmisc_1(A_66, B_67))) | ~v1_funct_2(C_68, A_66, B_67) | ~v1_funct_1(C_68))), inference(cnfTransformation, [status(thm)], [f_77])).
% 15.23/8.32  tff(c_146, plain, (k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_86, c_140])).
% 15.23/8.32  tff(c_150, plain, (k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_84, c_146])).
% 15.23/8.32  tff(c_151, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_150])).
% 15.23/8.32  tff(c_46, plain, (v3_tops_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_177])).
% 15.23/8.32  tff(c_441, plain, (![A_108, B_109, C_110]: (k2_relset_1(u1_struct_0(A_108), u1_struct_0(B_109), C_110)=k2_struct_0(B_109) | ~v3_tops_2(C_110, A_108, B_109) | ~m1_subset_1(C_110, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_108), u1_struct_0(B_109)))) | ~v1_funct_2(C_110, u1_struct_0(A_108), u1_struct_0(B_109)) | ~v1_funct_1(C_110) | ~l1_pre_topc(B_109) | ~l1_pre_topc(A_108))), inference(cnfTransformation, [status(thm)], [f_101])).
% 15.23/8.32  tff(c_457, plain, (![A_108, C_110]: (k2_relset_1(u1_struct_0(A_108), u1_struct_0('#skF_2'), C_110)=k2_struct_0('#skF_2') | ~v3_tops_2(C_110, A_108, '#skF_2') | ~m1_subset_1(C_110, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_108), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_110, u1_struct_0(A_108), u1_struct_0('#skF_2')) | ~v1_funct_1(C_110) | ~l1_pre_topc('#skF_2') | ~l1_pre_topc(A_108))), inference(superposition, [status(thm), theory('equality')], [c_72, c_441])).
% 15.23/8.32  tff(c_511, plain, (![A_116, C_117]: (k2_relset_1(u1_struct_0(A_116), k2_struct_0('#skF_2'), C_117)=k2_struct_0('#skF_2') | ~v3_tops_2(C_117, A_116, '#skF_2') | ~m1_subset_1(C_117, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_116), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_117, u1_struct_0(A_116), k2_struct_0('#skF_2')) | ~v1_funct_1(C_117) | ~l1_pre_topc(A_116))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_72, c_72, c_457])).
% 15.23/8.32  tff(c_518, plain, (![C_117]: (k2_relset_1(u1_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_117)=k2_struct_0('#skF_2') | ~v3_tops_2(C_117, '#skF_1', '#skF_2') | ~m1_subset_1(C_117, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_117, u1_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1(C_117) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_73, c_511])).
% 15.23/8.32  tff(c_527, plain, (![C_118]: (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_118)=k2_struct_0('#skF_2') | ~v3_tops_2(C_118, '#skF_1', '#skF_2') | ~m1_subset_1(C_118, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_118, k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1(C_118))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_73, c_73, c_518])).
% 15.23/8.32  tff(c_534, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2') | ~v3_tops_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_86, c_527])).
% 15.23/8.32  tff(c_538, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_84, c_46, c_534])).
% 15.23/8.32  tff(c_540, plain, $false, inference(negUnitSimplification, [status(thm)], [c_151, c_538])).
% 15.23/8.32  tff(c_541, plain, (~v2_funct_1('#skF_3') | k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_funct_1('#skF_3')), inference(splitRight, [status(thm)], [c_150])).
% 15.23/8.32  tff(c_547, plain, (~v2_funct_1('#skF_3')), inference(splitLeft, [status(thm)], [c_541])).
% 15.23/8.32  tff(c_548, plain, (![C_119, A_120, B_121]: (v2_funct_1(C_119) | ~v3_tops_2(C_119, A_120, B_121) | ~m1_subset_1(C_119, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_120), u1_struct_0(B_121)))) | ~v1_funct_2(C_119, u1_struct_0(A_120), u1_struct_0(B_121)) | ~v1_funct_1(C_119) | ~l1_pre_topc(B_121) | ~l1_pre_topc(A_120))), inference(cnfTransformation, [status(thm)], [f_101])).
% 15.23/8.33  tff(c_555, plain, (![C_119, B_121]: (v2_funct_1(C_119) | ~v3_tops_2(C_119, '#skF_1', B_121) | ~m1_subset_1(C_119, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), u1_struct_0(B_121)))) | ~v1_funct_2(C_119, u1_struct_0('#skF_1'), u1_struct_0(B_121)) | ~v1_funct_1(C_119) | ~l1_pre_topc(B_121) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_73, c_548])).
% 15.23/8.33  tff(c_574, plain, (![C_122, B_123]: (v2_funct_1(C_122) | ~v3_tops_2(C_122, '#skF_1', B_123) | ~m1_subset_1(C_122, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), u1_struct_0(B_123)))) | ~v1_funct_2(C_122, k2_struct_0('#skF_1'), u1_struct_0(B_123)) | ~v1_funct_1(C_122) | ~l1_pre_topc(B_123))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_73, c_555])).
% 15.23/8.33  tff(c_584, plain, (![C_122]: (v2_funct_1(C_122) | ~v3_tops_2(C_122, '#skF_1', '#skF_2') | ~m1_subset_1(C_122, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_122, k2_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1(C_122) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_72, c_574])).
% 15.23/8.33  tff(c_596, plain, (![C_125]: (v2_funct_1(C_125) | ~v3_tops_2(C_125, '#skF_1', '#skF_2') | ~m1_subset_1(C_125, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_125, k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1(C_125))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_72, c_584])).
% 15.23/8.33  tff(c_603, plain, (v2_funct_1('#skF_3') | ~v3_tops_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_86, c_596])).
% 15.23/8.33  tff(c_607, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_84, c_46, c_603])).
% 15.23/8.33  tff(c_609, plain, $false, inference(negUnitSimplification, [status(thm)], [c_547, c_607])).
% 15.23/8.33  tff(c_610, plain, (k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_funct_1('#skF_3')), inference(splitRight, [status(thm)], [c_541])).
% 15.23/8.33  tff(c_44, plain, (~v3_tops_2(k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'), '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_177])).
% 15.23/8.33  tff(c_94, plain, (~v3_tops_2(k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'), '#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_73, c_72, c_44])).
% 15.23/8.33  tff(c_615, plain, (~v3_tops_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_610, c_94])).
% 15.23/8.33  tff(c_95, plain, (![A_51, B_52, C_53]: (v1_funct_1(k2_tops_2(A_51, B_52, C_53)) | ~m1_subset_1(C_53, k1_zfmisc_1(k2_zfmisc_1(A_51, B_52))) | ~v1_funct_2(C_53, A_51, B_52) | ~v1_funct_1(C_53))), inference(cnfTransformation, [status(thm)], [f_113])).
% 15.23/8.33  tff(c_98, plain, (v1_funct_1(k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_86, c_95])).
% 15.23/8.33  tff(c_101, plain, (v1_funct_1(k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_84, c_98])).
% 15.23/8.33  tff(c_614, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_610, c_101])).
% 15.23/8.33  tff(c_108, plain, (![A_57, B_58, C_59]: (v1_funct_2(k2_tops_2(A_57, B_58, C_59), B_58, A_57) | ~m1_subset_1(C_59, k1_zfmisc_1(k2_zfmisc_1(A_57, B_58))) | ~v1_funct_2(C_59, A_57, B_58) | ~v1_funct_1(C_59))), inference(cnfTransformation, [status(thm)], [f_113])).
% 15.23/8.33  tff(c_110, plain, (v1_funct_2(k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'), k2_struct_0('#skF_2'), k2_struct_0('#skF_1')) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_86, c_108])).
% 15.23/8.33  tff(c_113, plain, (v1_funct_2(k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'), k2_struct_0('#skF_2'), k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_84, c_110])).
% 15.23/8.33  tff(c_613, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_struct_0('#skF_2'), k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_610, c_113])).
% 15.23/8.33  tff(c_542, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_150])).
% 15.23/8.33  tff(c_611, plain, (v2_funct_1('#skF_3')), inference(splitRight, [status(thm)], [c_541])).
% 15.23/8.33  tff(c_56, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_177])).
% 15.23/8.33  tff(c_14626, plain, (![B_918, A_919, C_920]: (k2_relset_1(u1_struct_0(B_918), u1_struct_0(A_919), k2_tops_2(u1_struct_0(A_919), u1_struct_0(B_918), C_920))=k2_struct_0(A_919) | ~v2_funct_1(C_920) | k2_relset_1(u1_struct_0(A_919), u1_struct_0(B_918), C_920)!=k2_struct_0(B_918) | ~m1_subset_1(C_920, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_919), u1_struct_0(B_918)))) | ~v1_funct_2(C_920, u1_struct_0(A_919), u1_struct_0(B_918)) | ~v1_funct_1(C_920) | ~l1_struct_0(B_918) | v2_struct_0(B_918) | ~l1_struct_0(A_919))), inference(cnfTransformation, [status(thm)], [f_136])).
% 15.23/8.33  tff(c_14656, plain, (![A_919, C_920]: (k2_relset_1(u1_struct_0('#skF_2'), u1_struct_0(A_919), k2_tops_2(u1_struct_0(A_919), k2_struct_0('#skF_2'), C_920))=k2_struct_0(A_919) | ~v2_funct_1(C_920) | k2_relset_1(u1_struct_0(A_919), u1_struct_0('#skF_2'), C_920)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_920, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_919), u1_struct_0('#skF_2')))) | ~v1_funct_2(C_920, u1_struct_0(A_919), u1_struct_0('#skF_2')) | ~v1_funct_1(C_920) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2') | ~l1_struct_0(A_919))), inference(superposition, [status(thm), theory('equality')], [c_72, c_14626])).
% 15.23/8.33  tff(c_14667, plain, (![A_919, C_920]: (k2_relset_1(k2_struct_0('#skF_2'), u1_struct_0(A_919), k2_tops_2(u1_struct_0(A_919), k2_struct_0('#skF_2'), C_920))=k2_struct_0(A_919) | ~v2_funct_1(C_920) | k2_relset_1(u1_struct_0(A_919), k2_struct_0('#skF_2'), C_920)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_920, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_919), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_920, u1_struct_0(A_919), k2_struct_0('#skF_2')) | ~v1_funct_1(C_920) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2') | ~l1_struct_0(A_919))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_72, c_72, c_72, c_14656])).
% 15.23/8.33  tff(c_14668, plain, (![A_919, C_920]: (k2_relset_1(k2_struct_0('#skF_2'), u1_struct_0(A_919), k2_tops_2(u1_struct_0(A_919), k2_struct_0('#skF_2'), C_920))=k2_struct_0(A_919) | ~v2_funct_1(C_920) | k2_relset_1(u1_struct_0(A_919), k2_struct_0('#skF_2'), C_920)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_920, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_919), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_920, u1_struct_0(A_919), k2_struct_0('#skF_2')) | ~v1_funct_1(C_920) | ~l1_struct_0('#skF_2') | ~l1_struct_0(A_919))), inference(negUnitSimplification, [status(thm)], [c_56, c_14667])).
% 15.23/8.33  tff(c_14697, plain, (~l1_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_14668])).
% 15.23/8.33  tff(c_14700, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_16, c_14697])).
% 15.23/8.33  tff(c_14704, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_14700])).
% 15.23/8.33  tff(c_14706, plain, (l1_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_14668])).
% 15.23/8.33  tff(c_14764, plain, (![B_929, A_930, C_931]: (k1_relset_1(u1_struct_0(B_929), u1_struct_0(A_930), k2_tops_2(u1_struct_0(A_930), u1_struct_0(B_929), C_931))=k2_struct_0(B_929) | ~v2_funct_1(C_931) | k2_relset_1(u1_struct_0(A_930), u1_struct_0(B_929), C_931)!=k2_struct_0(B_929) | ~m1_subset_1(C_931, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_930), u1_struct_0(B_929)))) | ~v1_funct_2(C_931, u1_struct_0(A_930), u1_struct_0(B_929)) | ~v1_funct_1(C_931) | ~l1_struct_0(B_929) | v2_struct_0(B_929) | ~l1_struct_0(A_930))), inference(cnfTransformation, [status(thm)], [f_136])).
% 15.23/8.33  tff(c_14794, plain, (![A_930, C_931]: (k1_relset_1(u1_struct_0('#skF_2'), u1_struct_0(A_930), k2_tops_2(u1_struct_0(A_930), k2_struct_0('#skF_2'), C_931))=k2_struct_0('#skF_2') | ~v2_funct_1(C_931) | k2_relset_1(u1_struct_0(A_930), u1_struct_0('#skF_2'), C_931)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_931, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_930), u1_struct_0('#skF_2')))) | ~v1_funct_2(C_931, u1_struct_0(A_930), u1_struct_0('#skF_2')) | ~v1_funct_1(C_931) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2') | ~l1_struct_0(A_930))), inference(superposition, [status(thm), theory('equality')], [c_72, c_14764])).
% 15.23/8.33  tff(c_14809, plain, (![A_930, C_931]: (k1_relset_1(k2_struct_0('#skF_2'), u1_struct_0(A_930), k2_tops_2(u1_struct_0(A_930), k2_struct_0('#skF_2'), C_931))=k2_struct_0('#skF_2') | ~v2_funct_1(C_931) | k2_relset_1(u1_struct_0(A_930), k2_struct_0('#skF_2'), C_931)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_931, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_930), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_931, u1_struct_0(A_930), k2_struct_0('#skF_2')) | ~v1_funct_1(C_931) | v2_struct_0('#skF_2') | ~l1_struct_0(A_930))), inference(demodulation, [status(thm), theory('equality')], [c_14706, c_72, c_72, c_72, c_72, c_14794])).
% 15.23/8.33  tff(c_14825, plain, (![A_933, C_934]: (k1_relset_1(k2_struct_0('#skF_2'), u1_struct_0(A_933), k2_tops_2(u1_struct_0(A_933), k2_struct_0('#skF_2'), C_934))=k2_struct_0('#skF_2') | ~v2_funct_1(C_934) | k2_relset_1(u1_struct_0(A_933), k2_struct_0('#skF_2'), C_934)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_934, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_933), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_934, u1_struct_0(A_933), k2_struct_0('#skF_2')) | ~v1_funct_1(C_934) | ~l1_struct_0(A_933))), inference(negUnitSimplification, [status(thm)], [c_56, c_14809])).
% 15.23/8.33  tff(c_14837, plain, (![C_934]: (k1_relset_1(k2_struct_0('#skF_2'), u1_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_934))=k2_struct_0('#skF_2') | ~v2_funct_1(C_934) | k2_relset_1(u1_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_934)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_934, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_934, u1_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1(C_934) | ~l1_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_73, c_14825])).
% 15.23/8.33  tff(c_14847, plain, (![C_934]: (k1_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_934))=k2_struct_0('#skF_2') | ~v2_funct_1(C_934) | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_934)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_934, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_934, k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1(C_934) | ~l1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_73, c_73, c_73, c_73, c_14837])).
% 15.23/8.33  tff(c_23908, plain, (~l1_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_14847])).
% 15.23/8.33  tff(c_23911, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_16, c_23908])).
% 15.23/8.33  tff(c_23915, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_23911])).
% 15.23/8.33  tff(c_23917, plain, (l1_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_14847])).
% 15.23/8.33  tff(c_14834, plain, (![C_934]: (k1_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_934))=k2_struct_0('#skF_2') | ~v2_funct_1(C_934) | k2_relset_1(u1_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_934)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_934, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_934, u1_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1(C_934) | ~l1_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_73, c_14825])).
% 15.23/8.33  tff(c_14846, plain, (![C_934]: (k1_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_934))=k2_struct_0('#skF_2') | ~v2_funct_1(C_934) | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_934)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_934, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_934, k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1(C_934) | ~l1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_73, c_73, c_73, c_73, c_14834])).
% 15.23/8.33  tff(c_23925, plain, (![C_1353]: (k1_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_1353))=k2_struct_0('#skF_2') | ~v2_funct_1(C_1353) | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_1353)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_1353, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_1353, k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1(C_1353))), inference(demodulation, [status(thm), theory('equality')], [c_23917, c_14846])).
% 15.23/8.33  tff(c_23940, plain, (k1_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))=k2_struct_0('#skF_2') | ~v2_funct_1('#skF_3') | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_610, c_23925])).
% 15.23/8.33  tff(c_23948, plain, (k1_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_84, c_86, c_542, c_611, c_23940])).
% 15.23/8.33  tff(c_32, plain, (![A_21, B_22, C_23]: (m1_subset_1(k2_tops_2(A_21, B_22, C_23), k1_zfmisc_1(k2_zfmisc_1(B_22, A_21))) | ~m1_subset_1(C_23, k1_zfmisc_1(k2_zfmisc_1(A_21, B_22))) | ~v1_funct_2(C_23, A_21, B_22) | ~v1_funct_1(C_23))), inference(cnfTransformation, [status(thm)], [f_113])).
% 15.23/8.33  tff(c_619, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1')))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_610, c_32])).
% 15.23/8.33  tff(c_623, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_84, c_86, c_619])).
% 15.23/8.33  tff(c_18, plain, (![A_11, B_12, C_13]: (k2_tops_2(A_11, B_12, C_13)=k2_funct_1(C_13) | ~v2_funct_1(C_13) | k2_relset_1(A_11, B_12, C_13)!=B_12 | ~m1_subset_1(C_13, k1_zfmisc_1(k2_zfmisc_1(A_11, B_12))) | ~v1_funct_2(C_13, A_11, B_12) | ~v1_funct_1(C_13))), inference(cnfTransformation, [status(thm)], [f_77])).
% 15.23/8.33  tff(c_653, plain, (k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3')) | ~v2_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))!=k2_struct_0('#skF_1') | ~v1_funct_2(k2_funct_1('#skF_3'), k2_struct_0('#skF_2'), k2_struct_0('#skF_1')) | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_623, c_18])).
% 15.23/8.33  tff(c_669, plain, (k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3')) | ~v2_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))!=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_614, c_613, c_653])).
% 15.23/8.33  tff(c_744, plain, (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))!=k2_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_669])).
% 15.23/8.33  tff(c_1227, plain, (![B_196, A_197, C_198]: (k2_relset_1(u1_struct_0(B_196), u1_struct_0(A_197), k2_tops_2(u1_struct_0(A_197), u1_struct_0(B_196), C_198))=k2_struct_0(A_197) | ~v2_funct_1(C_198) | k2_relset_1(u1_struct_0(A_197), u1_struct_0(B_196), C_198)!=k2_struct_0(B_196) | ~m1_subset_1(C_198, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_197), u1_struct_0(B_196)))) | ~v1_funct_2(C_198, u1_struct_0(A_197), u1_struct_0(B_196)) | ~v1_funct_1(C_198) | ~l1_struct_0(B_196) | v2_struct_0(B_196) | ~l1_struct_0(A_197))), inference(cnfTransformation, [status(thm)], [f_136])).
% 15.23/8.33  tff(c_1257, plain, (![A_197, C_198]: (k2_relset_1(u1_struct_0('#skF_2'), u1_struct_0(A_197), k2_tops_2(u1_struct_0(A_197), k2_struct_0('#skF_2'), C_198))=k2_struct_0(A_197) | ~v2_funct_1(C_198) | k2_relset_1(u1_struct_0(A_197), u1_struct_0('#skF_2'), C_198)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_198, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_197), u1_struct_0('#skF_2')))) | ~v1_funct_2(C_198, u1_struct_0(A_197), u1_struct_0('#skF_2')) | ~v1_funct_1(C_198) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2') | ~l1_struct_0(A_197))), inference(superposition, [status(thm), theory('equality')], [c_72, c_1227])).
% 15.23/8.33  tff(c_1268, plain, (![A_197, C_198]: (k2_relset_1(k2_struct_0('#skF_2'), u1_struct_0(A_197), k2_tops_2(u1_struct_0(A_197), k2_struct_0('#skF_2'), C_198))=k2_struct_0(A_197) | ~v2_funct_1(C_198) | k2_relset_1(u1_struct_0(A_197), k2_struct_0('#skF_2'), C_198)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_198, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_197), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_198, u1_struct_0(A_197), k2_struct_0('#skF_2')) | ~v1_funct_1(C_198) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2') | ~l1_struct_0(A_197))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_72, c_72, c_72, c_1257])).
% 15.23/8.33  tff(c_1269, plain, (![A_197, C_198]: (k2_relset_1(k2_struct_0('#skF_2'), u1_struct_0(A_197), k2_tops_2(u1_struct_0(A_197), k2_struct_0('#skF_2'), C_198))=k2_struct_0(A_197) | ~v2_funct_1(C_198) | k2_relset_1(u1_struct_0(A_197), k2_struct_0('#skF_2'), C_198)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_198, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_197), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_198, u1_struct_0(A_197), k2_struct_0('#skF_2')) | ~v1_funct_1(C_198) | ~l1_struct_0('#skF_2') | ~l1_struct_0(A_197))), inference(negUnitSimplification, [status(thm)], [c_56, c_1268])).
% 15.23/8.33  tff(c_1289, plain, (~l1_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_1269])).
% 15.23/8.33  tff(c_1292, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_16, c_1289])).
% 15.23/8.33  tff(c_1296, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_1292])).
% 15.23/8.33  tff(c_1298, plain, (l1_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_1269])).
% 15.23/8.33  tff(c_1335, plain, (![B_206, A_207, C_208]: (k1_relset_1(u1_struct_0(B_206), u1_struct_0(A_207), k2_tops_2(u1_struct_0(A_207), u1_struct_0(B_206), C_208))=k2_struct_0(B_206) | ~v2_funct_1(C_208) | k2_relset_1(u1_struct_0(A_207), u1_struct_0(B_206), C_208)!=k2_struct_0(B_206) | ~m1_subset_1(C_208, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_207), u1_struct_0(B_206)))) | ~v1_funct_2(C_208, u1_struct_0(A_207), u1_struct_0(B_206)) | ~v1_funct_1(C_208) | ~l1_struct_0(B_206) | v2_struct_0(B_206) | ~l1_struct_0(A_207))), inference(cnfTransformation, [status(thm)], [f_136])).
% 15.23/8.33  tff(c_1356, plain, (![A_207, C_208]: (k1_relset_1(k2_struct_0('#skF_2'), u1_struct_0(A_207), k2_tops_2(u1_struct_0(A_207), u1_struct_0('#skF_2'), C_208))=k2_struct_0('#skF_2') | ~v2_funct_1(C_208) | k2_relset_1(u1_struct_0(A_207), u1_struct_0('#skF_2'), C_208)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_208, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_207), u1_struct_0('#skF_2')))) | ~v1_funct_2(C_208, u1_struct_0(A_207), u1_struct_0('#skF_2')) | ~v1_funct_1(C_208) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2') | ~l1_struct_0(A_207))), inference(superposition, [status(thm), theory('equality')], [c_72, c_1335])).
% 15.23/8.33  tff(c_1373, plain, (![A_207, C_208]: (k1_relset_1(k2_struct_0('#skF_2'), u1_struct_0(A_207), k2_tops_2(u1_struct_0(A_207), k2_struct_0('#skF_2'), C_208))=k2_struct_0('#skF_2') | ~v2_funct_1(C_208) | k2_relset_1(u1_struct_0(A_207), k2_struct_0('#skF_2'), C_208)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_208, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_207), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_208, u1_struct_0(A_207), k2_struct_0('#skF_2')) | ~v1_funct_1(C_208) | v2_struct_0('#skF_2') | ~l1_struct_0(A_207))), inference(demodulation, [status(thm), theory('equality')], [c_1298, c_72, c_72, c_72, c_72, c_1356])).
% 15.23/8.33  tff(c_1409, plain, (![A_214, C_215]: (k1_relset_1(k2_struct_0('#skF_2'), u1_struct_0(A_214), k2_tops_2(u1_struct_0(A_214), k2_struct_0('#skF_2'), C_215))=k2_struct_0('#skF_2') | ~v2_funct_1(C_215) | k2_relset_1(u1_struct_0(A_214), k2_struct_0('#skF_2'), C_215)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_215, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_214), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_215, u1_struct_0(A_214), k2_struct_0('#skF_2')) | ~v1_funct_1(C_215) | ~l1_struct_0(A_214))), inference(negUnitSimplification, [status(thm)], [c_56, c_1373])).
% 15.23/8.33  tff(c_1418, plain, (![C_215]: (k1_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_215))=k2_struct_0('#skF_2') | ~v2_funct_1(C_215) | k2_relset_1(u1_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_215)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_215, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_215, u1_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1(C_215) | ~l1_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_73, c_1409])).
% 15.23/8.33  tff(c_1430, plain, (![C_215]: (k1_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_215))=k2_struct_0('#skF_2') | ~v2_funct_1(C_215) | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_215)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_215, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_215, k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1(C_215) | ~l1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_73, c_73, c_73, c_73, c_1418])).
% 15.23/8.33  tff(c_1579, plain, (~l1_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_1430])).
% 15.23/8.33  tff(c_1582, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_16, c_1579])).
% 15.23/8.33  tff(c_1586, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_1582])).
% 15.23/8.33  tff(c_1588, plain, (l1_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_1430])).
% 15.23/8.33  tff(c_1541, plain, (![A_229, C_230]: (k2_relset_1(k2_struct_0('#skF_2'), u1_struct_0(A_229), k2_tops_2(u1_struct_0(A_229), k2_struct_0('#skF_2'), C_230))=k2_struct_0(A_229) | ~v2_funct_1(C_230) | k2_relset_1(u1_struct_0(A_229), k2_struct_0('#skF_2'), C_230)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_230, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_229), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_230, u1_struct_0(A_229), k2_struct_0('#skF_2')) | ~v1_funct_1(C_230) | ~l1_struct_0(A_229))), inference(splitRight, [status(thm)], [c_1269])).
% 15.23/8.33  tff(c_1553, plain, (![C_230]: (k2_relset_1(k2_struct_0('#skF_2'), u1_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_230))=k2_struct_0('#skF_1') | ~v2_funct_1(C_230) | k2_relset_1(u1_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_230)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_230, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_230, u1_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1(C_230) | ~l1_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_73, c_1541])).
% 15.23/8.33  tff(c_1563, plain, (![C_230]: (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_230))=k2_struct_0('#skF_1') | ~v2_funct_1(C_230) | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_230)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_230, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_230, k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1(C_230) | ~l1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_73, c_73, c_73, c_73, c_1553])).
% 15.23/8.33  tff(c_1667, plain, (![C_238]: (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_238))=k2_struct_0('#skF_1') | ~v2_funct_1(C_238) | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_238)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_238, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_238, k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1(C_238))), inference(demodulation, [status(thm), theory('equality')], [c_1588, c_1563])).
% 15.23/8.33  tff(c_1676, plain, (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))=k2_struct_0('#skF_1') | ~v2_funct_1('#skF_3') | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_610, c_1667])).
% 15.23/8.33  tff(c_1680, plain, (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_84, c_86, c_542, c_611, c_1676])).
% 15.23/8.33  tff(c_1682, plain, $false, inference(negUnitSimplification, [status(thm)], [c_744, c_1680])).
% 15.23/8.33  tff(c_1684, plain, (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))=k2_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_669])).
% 15.23/8.33  tff(c_8, plain, (![C_4, A_2, B_3]: (v1_relat_1(C_4) | ~m1_subset_1(C_4, k1_zfmisc_1(k2_zfmisc_1(A_2, B_3))))), inference(cnfTransformation, [status(thm)], [f_41])).
% 15.23/8.33  tff(c_90, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_86, c_8])).
% 15.23/8.33  tff(c_2, plain, (![A_1]: (v2_funct_1(k2_funct_1(A_1)) | ~v2_funct_1(A_1) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_37])).
% 15.23/8.33  tff(c_1683, plain, (~v2_funct_1(k2_funct_1('#skF_3')) | k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_669])).
% 15.23/8.33  tff(c_1689, plain, (~v2_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_1683])).
% 15.23/8.33  tff(c_1692, plain, (~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_2, c_1689])).
% 15.23/8.33  tff(c_1696, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_90, c_52, c_611, c_1692])).
% 15.23/8.33  tff(c_1698, plain, (v2_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_1683])).
% 15.23/8.33  tff(c_14535, plain, (![A_914, B_915, C_916]: (v5_pre_topc(k2_tops_2(u1_struct_0(A_914), u1_struct_0(B_915), C_916), B_915, A_914) | ~v3_tops_2(C_916, A_914, B_915) | ~m1_subset_1(C_916, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_914), u1_struct_0(B_915)))) | ~v1_funct_2(C_916, u1_struct_0(A_914), u1_struct_0(B_915)) | ~v1_funct_1(C_916) | ~l1_pre_topc(B_915) | ~l1_pre_topc(A_914))), inference(cnfTransformation, [status(thm)], [f_101])).
% 15.23/8.33  tff(c_14546, plain, (![A_914, C_916]: (v5_pre_topc(k2_tops_2(u1_struct_0(A_914), u1_struct_0('#skF_2'), C_916), '#skF_2', A_914) | ~v3_tops_2(C_916, A_914, '#skF_2') | ~m1_subset_1(C_916, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_914), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_916, u1_struct_0(A_914), u1_struct_0('#skF_2')) | ~v1_funct_1(C_916) | ~l1_pre_topc('#skF_2') | ~l1_pre_topc(A_914))), inference(superposition, [status(thm), theory('equality')], [c_72, c_14535])).
% 15.23/8.33  tff(c_20842, plain, (![A_1223, C_1224]: (v5_pre_topc(k2_tops_2(u1_struct_0(A_1223), k2_struct_0('#skF_2'), C_1224), '#skF_2', A_1223) | ~v3_tops_2(C_1224, A_1223, '#skF_2') | ~m1_subset_1(C_1224, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1223), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_1224, u1_struct_0(A_1223), k2_struct_0('#skF_2')) | ~v1_funct_1(C_1224) | ~l1_pre_topc(A_1223))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_72, c_72, c_14546])).
% 15.23/8.33  tff(c_20847, plain, (![C_1224]: (v5_pre_topc(k2_tops_2(u1_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_1224), '#skF_2', '#skF_1') | ~v3_tops_2(C_1224, '#skF_1', '#skF_2') | ~m1_subset_1(C_1224, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_1224, u1_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1(C_1224) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_73, c_20842])).
% 15.23/8.33  tff(c_20900, plain, (![C_1228]: (v5_pre_topc(k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_1228), '#skF_2', '#skF_1') | ~v3_tops_2(C_1228, '#skF_1', '#skF_2') | ~m1_subset_1(C_1228, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_1228, k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1(C_1228))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_73, c_73, c_20847])).
% 15.23/8.33  tff(c_20913, plain, (v5_pre_topc(k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'), '#skF_2', '#skF_1') | ~v3_tops_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_86, c_20900])).
% 15.23/8.33  tff(c_20923, plain, (v5_pre_topc(k2_funct_1('#skF_3'), '#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_84, c_46, c_610, c_20913])).
% 15.23/8.33  tff(c_718, plain, (![C_133, A_134, B_135]: (v5_pre_topc(C_133, A_134, B_135) | ~v3_tops_2(C_133, A_134, B_135) | ~m1_subset_1(C_133, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_134), u1_struct_0(B_135)))) | ~v1_funct_2(C_133, u1_struct_0(A_134), u1_struct_0(B_135)) | ~v1_funct_1(C_133) | ~l1_pre_topc(B_135) | ~l1_pre_topc(A_134))), inference(cnfTransformation, [status(thm)], [f_101])).
% 15.23/8.33  tff(c_725, plain, (![C_133, B_135]: (v5_pre_topc(C_133, '#skF_1', B_135) | ~v3_tops_2(C_133, '#skF_1', B_135) | ~m1_subset_1(C_133, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), u1_struct_0(B_135)))) | ~v1_funct_2(C_133, u1_struct_0('#skF_1'), u1_struct_0(B_135)) | ~v1_funct_1(C_133) | ~l1_pre_topc(B_135) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_73, c_718])).
% 15.23/8.33  tff(c_14158, plain, (![C_874, B_875]: (v5_pre_topc(C_874, '#skF_1', B_875) | ~v3_tops_2(C_874, '#skF_1', B_875) | ~m1_subset_1(C_874, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), u1_struct_0(B_875)))) | ~v1_funct_2(C_874, k2_struct_0('#skF_1'), u1_struct_0(B_875)) | ~v1_funct_1(C_874) | ~l1_pre_topc(B_875))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_73, c_725])).
% 15.23/8.33  tff(c_14168, plain, (![C_874]: (v5_pre_topc(C_874, '#skF_1', '#skF_2') | ~v3_tops_2(C_874, '#skF_1', '#skF_2') | ~m1_subset_1(C_874, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_874, k2_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1(C_874) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_72, c_14158])).
% 15.23/8.33  tff(c_14180, plain, (![C_877]: (v5_pre_topc(C_877, '#skF_1', '#skF_2') | ~v3_tops_2(C_877, '#skF_1', '#skF_2') | ~m1_subset_1(C_877, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_877, k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1(C_877))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_72, c_14168])).
% 15.23/8.33  tff(c_14190, plain, (v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | ~v3_tops_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_86, c_14180])).
% 15.23/8.33  tff(c_14197, plain, (v5_pre_topc('#skF_3', '#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_84, c_46, c_14190])).
% 15.23/8.33  tff(c_1697, plain, (k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_1683])).
% 15.23/8.33  tff(c_36, plain, (![A_21, B_22, C_23]: (v1_funct_1(k2_tops_2(A_21, B_22, C_23)) | ~m1_subset_1(C_23, k1_zfmisc_1(k2_zfmisc_1(A_21, B_22))) | ~v1_funct_2(C_23, A_21, B_22) | ~v1_funct_1(C_23))), inference(cnfTransformation, [status(thm)], [f_113])).
% 15.23/8.33  tff(c_663, plain, (v1_funct_1(k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))) | ~v1_funct_2(k2_funct_1('#skF_3'), k2_struct_0('#skF_2'), k2_struct_0('#skF_1')) | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_623, c_36])).
% 15.23/8.33  tff(c_681, plain, (v1_funct_1(k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_614, c_613, c_663])).
% 15.23/8.33  tff(c_1713, plain, (v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_1697, c_681])).
% 15.23/8.33  tff(c_34, plain, (![A_21, B_22, C_23]: (v1_funct_2(k2_tops_2(A_21, B_22, C_23), B_22, A_21) | ~m1_subset_1(C_23, k1_zfmisc_1(k2_zfmisc_1(A_21, B_22))) | ~v1_funct_2(C_23, A_21, B_22) | ~v1_funct_1(C_23))), inference(cnfTransformation, [status(thm)], [f_113])).
% 15.23/8.33  tff(c_658, plain, (v1_funct_2(k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3')), k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_2(k2_funct_1('#skF_3'), k2_struct_0('#skF_2'), k2_struct_0('#skF_1')) | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_623, c_34])).
% 15.23/8.33  tff(c_675, plain, (v1_funct_2(k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3')), k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_614, c_613, c_658])).
% 15.23/8.33  tff(c_1712, plain, (v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')), k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_1697, c_675])).
% 15.23/8.33  tff(c_1718, plain, (m1_subset_1(k2_funct_1(k2_funct_1('#skF_3')), k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1')))) | ~v1_funct_2(k2_funct_1('#skF_3'), k2_struct_0('#skF_2'), k2_struct_0('#skF_1')) | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1697, c_32])).
% 15.23/8.33  tff(c_1722, plain, (m1_subset_1(k2_funct_1(k2_funct_1('#skF_3')), k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_614, c_613, c_623, c_1718])).
% 15.23/8.33  tff(c_14924, plain, (![A_943, B_944, C_945]: (r2_funct_2(u1_struct_0(A_943), u1_struct_0(B_944), k2_tops_2(u1_struct_0(B_944), u1_struct_0(A_943), k2_tops_2(u1_struct_0(A_943), u1_struct_0(B_944), C_945)), C_945) | ~v2_funct_1(C_945) | k2_relset_1(u1_struct_0(A_943), u1_struct_0(B_944), C_945)!=k2_struct_0(B_944) | ~m1_subset_1(C_945, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_943), u1_struct_0(B_944)))) | ~v1_funct_2(C_945, u1_struct_0(A_943), u1_struct_0(B_944)) | ~v1_funct_1(C_945) | ~l1_struct_0(B_944) | v2_struct_0(B_944) | ~l1_struct_0(A_943))), inference(cnfTransformation, [status(thm)], [f_157])).
% 15.23/8.33  tff(c_14953, plain, (![A_943, C_945]: (r2_funct_2(u1_struct_0(A_943), u1_struct_0('#skF_2'), k2_tops_2(k2_struct_0('#skF_2'), u1_struct_0(A_943), k2_tops_2(u1_struct_0(A_943), u1_struct_0('#skF_2'), C_945)), C_945) | ~v2_funct_1(C_945) | k2_relset_1(u1_struct_0(A_943), u1_struct_0('#skF_2'), C_945)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_945, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_943), u1_struct_0('#skF_2')))) | ~v1_funct_2(C_945, u1_struct_0(A_943), u1_struct_0('#skF_2')) | ~v1_funct_1(C_945) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2') | ~l1_struct_0(A_943))), inference(superposition, [status(thm), theory('equality')], [c_72, c_14924])).
% 15.23/8.33  tff(c_14976, plain, (![A_943, C_945]: (r2_funct_2(u1_struct_0(A_943), k2_struct_0('#skF_2'), k2_tops_2(k2_struct_0('#skF_2'), u1_struct_0(A_943), k2_tops_2(u1_struct_0(A_943), k2_struct_0('#skF_2'), C_945)), C_945) | ~v2_funct_1(C_945) | k2_relset_1(u1_struct_0(A_943), k2_struct_0('#skF_2'), C_945)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_945, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_943), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_945, u1_struct_0(A_943), k2_struct_0('#skF_2')) | ~v1_funct_1(C_945) | v2_struct_0('#skF_2') | ~l1_struct_0(A_943))), inference(demodulation, [status(thm), theory('equality')], [c_14706, c_72, c_72, c_72, c_72, c_72, c_14953])).
% 15.23/8.33  tff(c_20768, plain, (![A_1217, C_1218]: (r2_funct_2(u1_struct_0(A_1217), k2_struct_0('#skF_2'), k2_tops_2(k2_struct_0('#skF_2'), u1_struct_0(A_1217), k2_tops_2(u1_struct_0(A_1217), k2_struct_0('#skF_2'), C_1218)), C_1218) | ~v2_funct_1(C_1218) | k2_relset_1(u1_struct_0(A_1217), k2_struct_0('#skF_2'), C_1218)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_1218, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1217), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_1218, u1_struct_0(A_1217), k2_struct_0('#skF_2')) | ~v1_funct_1(C_1218) | ~l1_struct_0(A_1217))), inference(negUnitSimplification, [status(thm)], [c_56, c_14976])).
% 15.23/8.33  tff(c_20773, plain, (![C_1218]: (r2_funct_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), k2_tops_2(k2_struct_0('#skF_2'), u1_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_1218)), C_1218) | ~v2_funct_1(C_1218) | k2_relset_1(u1_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_1218)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_1218, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_1218, u1_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1(C_1218) | ~l1_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_73, c_20768])).
% 15.23/8.33  tff(c_20790, plain, (![C_1218]: (r2_funct_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_1218)), C_1218) | ~v2_funct_1(C_1218) | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_1218)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_1218, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_1218, k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1(C_1218) | ~l1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_73, c_73, c_73, c_73, c_73, c_20773])).
% 15.23/8.33  tff(c_25322, plain, (![C_1405]: (r2_funct_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_1405)), C_1405) | ~v2_funct_1(C_1405) | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_1405)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_1405, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_1405, k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1(C_1405))), inference(demodulation, [status(thm), theory('equality')], [c_23917, c_20790])).
% 15.23/8.33  tff(c_25336, plain, (r2_funct_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3')), '#skF_3') | ~v2_funct_1('#skF_3') | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_610, c_25322])).
% 15.23/8.33  tff(c_25345, plain, (r2_funct_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), k2_funct_1(k2_funct_1('#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_84, c_86, c_542, c_611, c_1697, c_25336])).
% 15.23/8.33  tff(c_12, plain, (![D_8, C_7, A_5, B_6]: (D_8=C_7 | ~r2_funct_2(A_5, B_6, C_7, D_8) | ~m1_subset_1(D_8, k1_zfmisc_1(k2_zfmisc_1(A_5, B_6))) | ~v1_funct_2(D_8, A_5, B_6) | ~v1_funct_1(D_8) | ~m1_subset_1(C_7, k1_zfmisc_1(k2_zfmisc_1(A_5, B_6))) | ~v1_funct_2(C_7, A_5, B_6) | ~v1_funct_1(C_7))), inference(cnfTransformation, [status(thm)], [f_57])).
% 15.23/8.33  tff(c_25347, plain, (k2_funct_1(k2_funct_1('#skF_3'))='#skF_3' | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~m1_subset_1(k2_funct_1(k2_funct_1('#skF_3')), k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')), k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(resolution, [status(thm)], [c_25345, c_12])).
% 15.23/8.33  tff(c_25350, plain, (k2_funct_1(k2_funct_1('#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1713, c_1712, c_1722, c_52, c_84, c_86, c_25347])).
% 15.23/8.33  tff(c_25434, plain, (k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_25350, c_1697])).
% 15.23/8.33  tff(c_15402, plain, (![C_988, A_989, B_990]: (v3_tops_2(C_988, A_989, B_990) | ~v5_pre_topc(k2_tops_2(u1_struct_0(A_989), u1_struct_0(B_990), C_988), B_990, A_989) | ~v5_pre_topc(C_988, A_989, B_990) | ~v2_funct_1(C_988) | k2_relset_1(u1_struct_0(A_989), u1_struct_0(B_990), C_988)!=k2_struct_0(B_990) | k1_relset_1(u1_struct_0(A_989), u1_struct_0(B_990), C_988)!=k2_struct_0(A_989) | ~m1_subset_1(C_988, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_989), u1_struct_0(B_990)))) | ~v1_funct_2(C_988, u1_struct_0(A_989), u1_struct_0(B_990)) | ~v1_funct_1(C_988) | ~l1_pre_topc(B_990) | ~l1_pre_topc(A_989))), inference(cnfTransformation, [status(thm)], [f_101])).
% 15.23/8.33  tff(c_15406, plain, (![C_988, A_989]: (v3_tops_2(C_988, A_989, '#skF_1') | ~v5_pre_topc(k2_tops_2(u1_struct_0(A_989), k2_struct_0('#skF_1'), C_988), '#skF_1', A_989) | ~v5_pre_topc(C_988, A_989, '#skF_1') | ~v2_funct_1(C_988) | k2_relset_1(u1_struct_0(A_989), u1_struct_0('#skF_1'), C_988)!=k2_struct_0('#skF_1') | k1_relset_1(u1_struct_0(A_989), u1_struct_0('#skF_1'), C_988)!=k2_struct_0(A_989) | ~m1_subset_1(C_988, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_989), u1_struct_0('#skF_1')))) | ~v1_funct_2(C_988, u1_struct_0(A_989), u1_struct_0('#skF_1')) | ~v1_funct_1(C_988) | ~l1_pre_topc('#skF_1') | ~l1_pre_topc(A_989))), inference(superposition, [status(thm), theory('equality')], [c_73, c_15402])).
% 15.23/8.33  tff(c_25972, plain, (![C_1433, A_1434]: (v3_tops_2(C_1433, A_1434, '#skF_1') | ~v5_pre_topc(k2_tops_2(u1_struct_0(A_1434), k2_struct_0('#skF_1'), C_1433), '#skF_1', A_1434) | ~v5_pre_topc(C_1433, A_1434, '#skF_1') | ~v2_funct_1(C_1433) | k2_relset_1(u1_struct_0(A_1434), k2_struct_0('#skF_1'), C_1433)!=k2_struct_0('#skF_1') | k1_relset_1(u1_struct_0(A_1434), k2_struct_0('#skF_1'), C_1433)!=k2_struct_0(A_1434) | ~m1_subset_1(C_1433, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1434), k2_struct_0('#skF_1')))) | ~v1_funct_2(C_1433, u1_struct_0(A_1434), k2_struct_0('#skF_1')) | ~v1_funct_1(C_1433) | ~l1_pre_topc(A_1434))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_73, c_73, c_73, c_73, c_15406])).
% 15.23/8.33  tff(c_25976, plain, (![C_1433]: (v3_tops_2(C_1433, '#skF_2', '#skF_1') | ~v5_pre_topc(k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), C_1433), '#skF_1', '#skF_2') | ~v5_pre_topc(C_1433, '#skF_2', '#skF_1') | ~v2_funct_1(C_1433) | k2_relset_1(u1_struct_0('#skF_2'), k2_struct_0('#skF_1'), C_1433)!=k2_struct_0('#skF_1') | k1_relset_1(u1_struct_0('#skF_2'), k2_struct_0('#skF_1'), C_1433)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_1433, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), k2_struct_0('#skF_1')))) | ~v1_funct_2(C_1433, u1_struct_0('#skF_2'), k2_struct_0('#skF_1')) | ~v1_funct_1(C_1433) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_72, c_25972])).
% 15.23/8.33  tff(c_25987, plain, (![C_1436]: (v3_tops_2(C_1436, '#skF_2', '#skF_1') | ~v5_pre_topc(k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), C_1436), '#skF_1', '#skF_2') | ~v5_pre_topc(C_1436, '#skF_2', '#skF_1') | ~v2_funct_1(C_1436) | k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), C_1436)!=k2_struct_0('#skF_1') | k1_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), C_1436)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_1436, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1')))) | ~v1_funct_2(C_1436, k2_struct_0('#skF_2'), k2_struct_0('#skF_1')) | ~v1_funct_1(C_1436))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_72, c_72, c_72, c_72, c_25976])).
% 15.23/8.33  tff(c_25990, plain, (v3_tops_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~v5_pre_topc(k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3')), '#skF_1', '#skF_2') | ~v5_pre_topc(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~v2_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))!=k2_struct_0('#skF_1') | k1_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))!=k2_struct_0('#skF_2') | ~v1_funct_2(k2_funct_1('#skF_3'), k2_struct_0('#skF_2'), k2_struct_0('#skF_1')) | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_623, c_25987])).
% 15.23/8.33  tff(c_25997, plain, (v3_tops_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_614, c_613, c_23948, c_1684, c_1698, c_20923, c_14197, c_25434, c_25990])).
% 15.23/8.33  tff(c_25999, plain, $false, inference(negUnitSimplification, [status(thm)], [c_615, c_25997])).
% 15.23/8.33  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 15.23/8.33  
% 15.23/8.33  Inference rules
% 15.23/8.33  ----------------------
% 15.23/8.33  #Ref     : 0
% 15.23/8.33  #Sup     : 4660
% 15.23/8.33  #Fact    : 0
% 15.23/8.33  #Define  : 0
% 15.23/8.33  #Split   : 109
% 15.23/8.33  #Chain   : 0
% 15.23/8.33  #Close   : 0
% 15.23/8.33  
% 15.23/8.33  Ordering : KBO
% 15.23/8.33  
% 15.23/8.33  Simplification rules
% 15.23/8.33  ----------------------
% 15.23/8.33  #Subsume      : 710
% 15.23/8.33  #Demod        : 32870
% 15.23/8.33  #Tautology    : 2058
% 15.23/8.33  #SimpNegUnit  : 280
% 15.23/8.33  #BackRed      : 1619
% 15.23/8.33  
% 15.23/8.33  #Partial instantiations: 0
% 15.23/8.33  #Strategies tried      : 1
% 15.23/8.33  
% 15.23/8.33  Timing (in seconds)
% 15.23/8.33  ----------------------
% 15.53/8.33  Preprocessing        : 0.33
% 15.53/8.33  Parsing              : 0.17
% 15.53/8.33  CNF conversion       : 0.03
% 15.53/8.33  Main loop            : 7.07
% 15.53/8.33  Inferencing          : 1.69
% 15.53/8.33  Reduction            : 3.93
% 15.53/8.33  Demodulation         : 3.33
% 15.53/8.33  BG Simplification    : 0.19
% 15.53/8.33  Subsumption          : 1.00
% 15.53/8.33  Abstraction          : 0.28
% 15.53/8.33  MUC search           : 0.00
% 15.53/8.33  Cooper               : 0.00
% 15.53/8.33  Total                : 7.46
% 15.53/8.33  Index Insertion      : 0.00
% 15.53/8.33  Index Deletion       : 0.00
% 15.53/8.33  Index Matching       : 0.00
% 15.53/8.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
