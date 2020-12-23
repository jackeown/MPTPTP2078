%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:17 EST 2020

% Result     : Theorem 3.05s
% Output     : CNFRefutation 3.35s
% Verified   : 
% Statistics : Number of formulae       :  154 (5054 expanded)
%              Number of leaves         :   39 (1779 expanded)
%              Depth                    :   18
%              Number of atoms          :  313 (15481 expanded)
%              Number of equality atoms :   84 (5035 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k2_tops_2 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_139,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_tops_2)).

tff(f_95,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_35,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_103,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(k2_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_struct_0)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_91,axiom,(
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

tff(f_115,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( k2_relset_1(A,B,C) = B
          & v2_funct_1(C) )
       => k2_tops_2(A,B,C) = k2_funct_1(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_2)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(c_52,plain,(
    l1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_53,plain,(
    ! [A_32] :
      ( u1_struct_0(A_32) = k2_struct_0(A_32)
      | ~ l1_struct_0(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_61,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_52,c_53])).

tff(c_48,plain,(
    l1_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_60,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_53])).

tff(c_42,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_71,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_60,c_42])).

tff(c_79,plain,(
    ! [C_34,A_35,B_36] :
      ( v1_relat_1(C_34)
      | ~ m1_subset_1(C_34,k1_zfmisc_1(k2_zfmisc_1(A_35,B_36))) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_83,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_71,c_79])).

tff(c_46,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_38,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_2,plain,(
    ! [A_1] :
      ( k2_relat_1(k2_funct_1(A_1)) = k1_relat_1(A_1)
      | ~ v2_funct_1(A_1)
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_50,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_84,plain,(
    ! [C_37,A_38,B_39] :
      ( v4_relat_1(C_37,A_38)
      | ~ m1_subset_1(C_37,k1_zfmisc_1(k2_zfmisc_1(A_38,B_39))) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_88,plain,(
    v4_relat_1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_71,c_84])).

tff(c_507,plain,(
    ! [B_97,A_98] :
      ( k1_relat_1(B_97) = A_98
      | ~ v1_partfun1(B_97,A_98)
      | ~ v4_relat_1(B_97,A_98)
      | ~ v1_relat_1(B_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_510,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_88,c_507])).

tff(c_513,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_510])).

tff(c_514,plain,(
    ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_513])).

tff(c_44,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_62,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_44])).

tff(c_72,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_62])).

tff(c_546,plain,(
    ! [C_106,A_107,B_108] :
      ( v1_partfun1(C_106,A_107)
      | ~ v1_funct_2(C_106,A_107,B_108)
      | ~ v1_funct_1(C_106)
      | ~ m1_subset_1(C_106,k1_zfmisc_1(k2_zfmisc_1(A_107,B_108)))
      | v1_xboole_0(B_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_549,plain,
    ( v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3')
    | v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_71,c_546])).

tff(c_552,plain,
    ( v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_72,c_549])).

tff(c_553,plain,(
    v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_514,c_552])).

tff(c_32,plain,(
    ! [A_24] :
      ( ~ v1_xboole_0(k2_struct_0(A_24))
      | ~ l1_struct_0(A_24)
      | v2_struct_0(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_556,plain,
    ( ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_553,c_32])).

tff(c_559,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_556])).

tff(c_561,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_559])).

tff(c_562,plain,(
    k2_struct_0('#skF_1') = k1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_513])).

tff(c_567,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_562,c_71])).

tff(c_638,plain,(
    ! [A_113,B_114,C_115] :
      ( k2_relset_1(A_113,B_114,C_115) = k2_relat_1(C_115)
      | ~ m1_subset_1(C_115,k1_zfmisc_1(k2_zfmisc_1(A_113,B_114))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_642,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_567,c_638])).

tff(c_40,plain,(
    k2_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_74,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_60,c_40])).

tff(c_565,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_562,c_74])).

tff(c_643,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_642,c_565])).

tff(c_566,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_562,c_72])).

tff(c_652,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_643,c_566])).

tff(c_648,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_643,c_642])).

tff(c_651,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_643,c_567])).

tff(c_754,plain,(
    ! [C_130,B_131,A_132] :
      ( m1_subset_1(k2_funct_1(C_130),k1_zfmisc_1(k2_zfmisc_1(B_131,A_132)))
      | k2_relset_1(A_132,B_131,C_130) != B_131
      | ~ v2_funct_1(C_130)
      | ~ m1_subset_1(C_130,k1_zfmisc_1(k2_zfmisc_1(A_132,B_131)))
      | ~ v1_funct_2(C_130,A_132,B_131)
      | ~ v1_funct_1(C_130) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_14,plain,(
    ! [A_11,B_12,C_13] :
      ( k2_relset_1(A_11,B_12,C_13) = k2_relat_1(C_13)
      | ~ m1_subset_1(C_13,k1_zfmisc_1(k2_zfmisc_1(A_11,B_12))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_875,plain,(
    ! [B_145,A_146,C_147] :
      ( k2_relset_1(B_145,A_146,k2_funct_1(C_147)) = k2_relat_1(k2_funct_1(C_147))
      | k2_relset_1(A_146,B_145,C_147) != B_145
      | ~ v2_funct_1(C_147)
      | ~ m1_subset_1(C_147,k1_zfmisc_1(k2_zfmisc_1(A_146,B_145)))
      | ~ v1_funct_2(C_147,A_146,B_145)
      | ~ v1_funct_1(C_147) ) ),
    inference(resolution,[status(thm)],[c_754,c_14])).

tff(c_881,plain,
    ( k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_651,c_875])).

tff(c_885,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_652,c_38,c_648,c_881])).

tff(c_733,plain,(
    ! [A_126,B_127,C_128] :
      ( k2_tops_2(A_126,B_127,C_128) = k2_funct_1(C_128)
      | ~ v2_funct_1(C_128)
      | k2_relset_1(A_126,B_127,C_128) != B_127
      | ~ m1_subset_1(C_128,k1_zfmisc_1(k2_zfmisc_1(A_126,B_127)))
      | ~ v1_funct_2(C_128,A_126,B_127)
      | ~ v1_funct_1(C_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_736,plain,
    ( k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_651,c_733])).

tff(c_739,plain,(
    k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_652,c_648,c_38,c_736])).

tff(c_126,plain,(
    ! [A_48,B_49,C_50] :
      ( k2_relset_1(A_48,B_49,C_50) = k2_relat_1(C_50)
      | ~ m1_subset_1(C_50,k1_zfmisc_1(k2_zfmisc_1(A_48,B_49))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_130,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_71,c_126])).

tff(c_131,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_74])).

tff(c_144,plain,
    ( ~ v1_xboole_0(k2_relat_1('#skF_3'))
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_131,c_32])).

tff(c_148,plain,
    ( ~ v1_xboole_0(k2_relat_1('#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_144])).

tff(c_149,plain,(
    ~ v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_148])).

tff(c_118,plain,(
    ! [B_46,A_47] :
      ( k1_relat_1(B_46) = A_47
      | ~ v1_partfun1(B_46,A_47)
      | ~ v4_relat_1(B_46,A_47)
      | ~ v1_relat_1(B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_121,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_88,c_118])).

tff(c_124,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_121])).

tff(c_125,plain,(
    ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_124])).

tff(c_138,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_72])).

tff(c_139,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_71])).

tff(c_189,plain,(
    ! [C_54,A_55,B_56] :
      ( v1_partfun1(C_54,A_55)
      | ~ v1_funct_2(C_54,A_55,B_56)
      | ~ v1_funct_1(C_54)
      | ~ m1_subset_1(C_54,k1_zfmisc_1(k2_zfmisc_1(A_55,B_56)))
      | v1_xboole_0(B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_192,plain,
    ( v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3')
    | v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_139,c_189])).

tff(c_195,plain,
    ( v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_138,c_192])).

tff(c_197,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_149,c_125,c_195])).

tff(c_198,plain,(
    k2_struct_0('#skF_1') = k1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_124])).

tff(c_203,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_198,c_71])).

tff(c_246,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_203,c_14])).

tff(c_201,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_198,c_74])).

tff(c_257,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_246,c_201])).

tff(c_202,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_198,c_72])).

tff(c_264,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_257,c_202])).

tff(c_262,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_257,c_246])).

tff(c_263,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_257,c_203])).

tff(c_341,plain,(
    ! [A_73,B_74,C_75] :
      ( k2_tops_2(A_73,B_74,C_75) = k2_funct_1(C_75)
      | ~ v2_funct_1(C_75)
      | k2_relset_1(A_73,B_74,C_75) != B_74
      | ~ m1_subset_1(C_75,k1_zfmisc_1(k2_zfmisc_1(A_73,B_74)))
      | ~ v1_funct_2(C_75,A_73,B_74)
      | ~ v1_funct_1(C_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_344,plain,
    ( k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_263,c_341])).

tff(c_347,plain,(
    k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_264,c_262,c_38,c_344])).

tff(c_36,plain,
    ( k2_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_1')
    | k1_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_94,plain,
    ( k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_1')
    | k1_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_61,c_60,c_60,c_61,c_61,c_60,c_60,c_36])).

tff(c_95,plain,(
    k1_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_94])).

tff(c_309,plain,(
    k1_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_257,c_257,c_257,c_198,c_198,c_95])).

tff(c_348,plain,(
    k1_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_347,c_309])).

tff(c_357,plain,(
    ! [C_77,B_78,A_79] :
      ( m1_subset_1(k2_funct_1(C_77),k1_zfmisc_1(k2_zfmisc_1(B_78,A_79)))
      | k2_relset_1(A_79,B_78,C_77) != B_78
      | ~ v2_funct_1(C_77)
      | ~ m1_subset_1(C_77,k1_zfmisc_1(k2_zfmisc_1(A_79,B_78)))
      | ~ v1_funct_2(C_77,A_79,B_78)
      | ~ v1_funct_1(C_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_6,plain,(
    ! [C_4,A_2,B_3] :
      ( v1_relat_1(C_4)
      | ~ m1_subset_1(C_4,k1_zfmisc_1(k2_zfmisc_1(A_2,B_3))) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_394,plain,(
    ! [C_80,A_81,B_82] :
      ( v1_relat_1(k2_funct_1(C_80))
      | k2_relset_1(A_81,B_82,C_80) != B_82
      | ~ v2_funct_1(C_80)
      | ~ m1_subset_1(C_80,k1_zfmisc_1(k2_zfmisc_1(A_81,B_82)))
      | ~ v1_funct_2(C_80,A_81,B_82)
      | ~ v1_funct_1(C_80) ) ),
    inference(resolution,[status(thm)],[c_357,c_6])).

tff(c_400,plain,
    ( v1_relat_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_263,c_394])).

tff(c_404,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_264,c_38,c_262,c_400])).

tff(c_10,plain,(
    ! [C_7,A_5,B_6] :
      ( v4_relat_1(C_7,A_5)
      | ~ m1_subset_1(C_7,k1_zfmisc_1(k2_zfmisc_1(A_5,B_6))) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_416,plain,(
    ! [C_86,B_87,A_88] :
      ( v4_relat_1(k2_funct_1(C_86),B_87)
      | k2_relset_1(A_88,B_87,C_86) != B_87
      | ~ v2_funct_1(C_86)
      | ~ m1_subset_1(C_86,k1_zfmisc_1(k2_zfmisc_1(A_88,B_87)))
      | ~ v1_funct_2(C_86,A_88,B_87)
      | ~ v1_funct_1(C_86) ) ),
    inference(resolution,[status(thm)],[c_357,c_10])).

tff(c_422,plain,
    ( v4_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_263,c_416])).

tff(c_426,plain,(
    v4_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_264,c_38,c_262,c_422])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_relat_1(k2_funct_1(A_1)) = k2_relat_1(A_1)
      | ~ v2_funct_1(A_1)
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_106,plain,(
    ! [A_45] :
      ( k1_relat_1(k2_funct_1(A_45)) = k2_relat_1(A_45)
      | ~ v2_funct_1(A_45)
      | ~ v1_funct_1(A_45)
      | ~ v1_relat_1(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_20,plain,(
    ! [B_19] :
      ( v1_partfun1(B_19,k1_relat_1(B_19))
      | ~ v4_relat_1(B_19,k1_relat_1(B_19))
      | ~ v1_relat_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_323,plain,(
    ! [A_66] :
      ( v1_partfun1(k2_funct_1(A_66),k1_relat_1(k2_funct_1(A_66)))
      | ~ v4_relat_1(k2_funct_1(A_66),k2_relat_1(A_66))
      | ~ v1_relat_1(k2_funct_1(A_66))
      | ~ v2_funct_1(A_66)
      | ~ v1_funct_1(A_66)
      | ~ v1_relat_1(A_66) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_106,c_20])).

tff(c_326,plain,(
    ! [A_1] :
      ( v1_partfun1(k2_funct_1(A_1),k2_relat_1(A_1))
      | ~ v4_relat_1(k2_funct_1(A_1),k2_relat_1(A_1))
      | ~ v1_relat_1(k2_funct_1(A_1))
      | ~ v2_funct_1(A_1)
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1)
      | ~ v2_funct_1(A_1)
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_323])).

tff(c_429,plain,
    ( v1_partfun1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_426,c_326])).

tff(c_435,plain,(
    v1_partfun1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_46,c_38,c_404,c_429])).

tff(c_22,plain,(
    ! [B_19,A_18] :
      ( k1_relat_1(B_19) = A_18
      | ~ v1_partfun1(B_19,A_18)
      | ~ v4_relat_1(B_19,A_18)
      | ~ v1_relat_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_432,plain,
    ( k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3')
    | ~ v1_partfun1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_426,c_22])).

tff(c_438,plain,
    ( k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3')
    | ~ v1_partfun1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_404,c_432])).

tff(c_440,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_435,c_438])).

tff(c_12,plain,(
    ! [A_8,B_9,C_10] :
      ( k1_relset_1(A_8,B_9,C_10) = k1_relat_1(C_10)
      | ~ m1_subset_1(C_10,k1_zfmisc_1(k2_zfmisc_1(A_8,B_9))) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_482,plain,(
    ! [B_92,A_93,C_94] :
      ( k1_relset_1(B_92,A_93,k2_funct_1(C_94)) = k1_relat_1(k2_funct_1(C_94))
      | k2_relset_1(A_93,B_92,C_94) != B_92
      | ~ v2_funct_1(C_94)
      | ~ m1_subset_1(C_94,k1_zfmisc_1(k2_zfmisc_1(A_93,B_92)))
      | ~ v1_funct_2(C_94,A_93,B_92)
      | ~ v1_funct_1(C_94) ) ),
    inference(resolution,[status(thm)],[c_357,c_12])).

tff(c_488,plain,
    ( k1_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_263,c_482])).

tff(c_492,plain,(
    k1_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_264,c_38,c_262,c_440,c_488])).

tff(c_494,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_348,c_492])).

tff(c_495,plain,(
    k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_94])).

tff(c_637,plain,(
    k2_relset_1(k2_struct_0('#skF_2'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_562,c_562,c_562,c_495])).

tff(c_649,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_643,c_643,c_637])).

tff(c_740,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_739,c_649])).

tff(c_898,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_885,c_740])).

tff(c_905,plain,
    ( ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_898])).

tff(c_909,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_46,c_38,c_905])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:42:53 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.05/1.53  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.26/1.55  
% 3.26/1.55  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.26/1.55  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k2_tops_2 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 3.26/1.55  
% 3.26/1.55  %Foreground sorts:
% 3.26/1.55  
% 3.26/1.55  
% 3.26/1.55  %Background operators:
% 3.26/1.55  
% 3.26/1.55  
% 3.26/1.55  %Foreground operators:
% 3.26/1.55  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.26/1.55  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.26/1.55  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.26/1.55  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 3.26/1.55  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.26/1.55  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.26/1.55  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.26/1.55  tff(k2_tops_2, type, k2_tops_2: ($i * $i * $i) > $i).
% 3.26/1.55  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.26/1.55  tff('#skF_2', type, '#skF_2': $i).
% 3.26/1.55  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 3.26/1.55  tff('#skF_3', type, '#skF_3': $i).
% 3.26/1.55  tff('#skF_1', type, '#skF_1': $i).
% 3.26/1.55  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.26/1.55  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.26/1.55  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.26/1.55  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.26/1.55  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.26/1.55  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.26/1.55  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.26/1.55  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.26/1.55  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.26/1.55  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.26/1.55  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.26/1.55  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.26/1.55  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.26/1.55  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.26/1.55  
% 3.35/1.58  tff(f_139, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: ((~v2_struct_0(B) & l1_struct_0(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B)) & v2_funct_1(C)) => ((k1_relset_1(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)) = k2_struct_0(B)) & (k2_relset_1(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)) = k2_struct_0(A)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_tops_2)).
% 3.35/1.58  tff(f_95, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 3.35/1.58  tff(f_39, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.35/1.58  tff(f_35, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 3.35/1.58  tff(f_45, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.35/1.58  tff(f_75, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_partfun1)).
% 3.35/1.58  tff(f_67, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc5_funct_2)).
% 3.35/1.58  tff(f_103, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(k2_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc5_struct_0)).
% 3.35/1.58  tff(f_53, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.35/1.58  tff(f_91, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_funct_2)).
% 3.35/1.58  tff(f_115, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => (k2_tops_2(A, B, C) = k2_funct_1(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tops_2)).
% 3.35/1.58  tff(f_49, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.35/1.58  tff(c_52, plain, (l1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.35/1.58  tff(c_53, plain, (![A_32]: (u1_struct_0(A_32)=k2_struct_0(A_32) | ~l1_struct_0(A_32))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.35/1.58  tff(c_61, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_52, c_53])).
% 3.35/1.58  tff(c_48, plain, (l1_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.35/1.58  tff(c_60, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_48, c_53])).
% 3.35/1.58  tff(c_42, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.35/1.58  tff(c_71, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_61, c_60, c_42])).
% 3.35/1.58  tff(c_79, plain, (![C_34, A_35, B_36]: (v1_relat_1(C_34) | ~m1_subset_1(C_34, k1_zfmisc_1(k2_zfmisc_1(A_35, B_36))))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.35/1.58  tff(c_83, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_71, c_79])).
% 3.35/1.58  tff(c_46, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.35/1.58  tff(c_38, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.35/1.58  tff(c_2, plain, (![A_1]: (k2_relat_1(k2_funct_1(A_1))=k1_relat_1(A_1) | ~v2_funct_1(A_1) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.35/1.58  tff(c_50, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.35/1.58  tff(c_84, plain, (![C_37, A_38, B_39]: (v4_relat_1(C_37, A_38) | ~m1_subset_1(C_37, k1_zfmisc_1(k2_zfmisc_1(A_38, B_39))))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.35/1.58  tff(c_88, plain, (v4_relat_1('#skF_3', k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_71, c_84])).
% 3.35/1.58  tff(c_507, plain, (![B_97, A_98]: (k1_relat_1(B_97)=A_98 | ~v1_partfun1(B_97, A_98) | ~v4_relat_1(B_97, A_98) | ~v1_relat_1(B_97))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.35/1.58  tff(c_510, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_88, c_507])).
% 3.35/1.58  tff(c_513, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_83, c_510])).
% 3.35/1.58  tff(c_514, plain, (~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_513])).
% 3.35/1.58  tff(c_44, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.35/1.58  tff(c_62, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_44])).
% 3.35/1.58  tff(c_72, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_61, c_62])).
% 3.35/1.58  tff(c_546, plain, (![C_106, A_107, B_108]: (v1_partfun1(C_106, A_107) | ~v1_funct_2(C_106, A_107, B_108) | ~v1_funct_1(C_106) | ~m1_subset_1(C_106, k1_zfmisc_1(k2_zfmisc_1(A_107, B_108))) | v1_xboole_0(B_108))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.35/1.58  tff(c_549, plain, (v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | v1_xboole_0(k2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_71, c_546])).
% 3.35/1.58  tff(c_552, plain, (v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | v1_xboole_0(k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_72, c_549])).
% 3.35/1.58  tff(c_553, plain, (v1_xboole_0(k2_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_514, c_552])).
% 3.35/1.58  tff(c_32, plain, (![A_24]: (~v1_xboole_0(k2_struct_0(A_24)) | ~l1_struct_0(A_24) | v2_struct_0(A_24))), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.35/1.58  tff(c_556, plain, (~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_553, c_32])).
% 3.35/1.58  tff(c_559, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_556])).
% 3.35/1.58  tff(c_561, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_559])).
% 3.35/1.58  tff(c_562, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_513])).
% 3.35/1.58  tff(c_567, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_562, c_71])).
% 3.35/1.58  tff(c_638, plain, (![A_113, B_114, C_115]: (k2_relset_1(A_113, B_114, C_115)=k2_relat_1(C_115) | ~m1_subset_1(C_115, k1_zfmisc_1(k2_zfmisc_1(A_113, B_114))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.35/1.58  tff(c_642, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_567, c_638])).
% 3.35/1.58  tff(c_40, plain, (k2_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.35/1.58  tff(c_74, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_61, c_60, c_40])).
% 3.35/1.58  tff(c_565, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_562, c_74])).
% 3.35/1.58  tff(c_643, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_642, c_565])).
% 3.35/1.58  tff(c_566, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_562, c_72])).
% 3.35/1.58  tff(c_652, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_643, c_566])).
% 3.35/1.58  tff(c_648, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_643, c_642])).
% 3.35/1.58  tff(c_651, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_643, c_567])).
% 3.35/1.58  tff(c_754, plain, (![C_130, B_131, A_132]: (m1_subset_1(k2_funct_1(C_130), k1_zfmisc_1(k2_zfmisc_1(B_131, A_132))) | k2_relset_1(A_132, B_131, C_130)!=B_131 | ~v2_funct_1(C_130) | ~m1_subset_1(C_130, k1_zfmisc_1(k2_zfmisc_1(A_132, B_131))) | ~v1_funct_2(C_130, A_132, B_131) | ~v1_funct_1(C_130))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.35/1.58  tff(c_14, plain, (![A_11, B_12, C_13]: (k2_relset_1(A_11, B_12, C_13)=k2_relat_1(C_13) | ~m1_subset_1(C_13, k1_zfmisc_1(k2_zfmisc_1(A_11, B_12))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.35/1.58  tff(c_875, plain, (![B_145, A_146, C_147]: (k2_relset_1(B_145, A_146, k2_funct_1(C_147))=k2_relat_1(k2_funct_1(C_147)) | k2_relset_1(A_146, B_145, C_147)!=B_145 | ~v2_funct_1(C_147) | ~m1_subset_1(C_147, k1_zfmisc_1(k2_zfmisc_1(A_146, B_145))) | ~v1_funct_2(C_147, A_146, B_145) | ~v1_funct_1(C_147))), inference(resolution, [status(thm)], [c_754, c_14])).
% 3.35/1.58  tff(c_881, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_651, c_875])).
% 3.35/1.58  tff(c_885, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_652, c_38, c_648, c_881])).
% 3.35/1.58  tff(c_733, plain, (![A_126, B_127, C_128]: (k2_tops_2(A_126, B_127, C_128)=k2_funct_1(C_128) | ~v2_funct_1(C_128) | k2_relset_1(A_126, B_127, C_128)!=B_127 | ~m1_subset_1(C_128, k1_zfmisc_1(k2_zfmisc_1(A_126, B_127))) | ~v1_funct_2(C_128, A_126, B_127) | ~v1_funct_1(C_128))), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.35/1.58  tff(c_736, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_651, c_733])).
% 3.35/1.58  tff(c_739, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_652, c_648, c_38, c_736])).
% 3.35/1.58  tff(c_126, plain, (![A_48, B_49, C_50]: (k2_relset_1(A_48, B_49, C_50)=k2_relat_1(C_50) | ~m1_subset_1(C_50, k1_zfmisc_1(k2_zfmisc_1(A_48, B_49))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.35/1.58  tff(c_130, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_71, c_126])).
% 3.35/1.58  tff(c_131, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_130, c_74])).
% 3.35/1.58  tff(c_144, plain, (~v1_xboole_0(k2_relat_1('#skF_3')) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_131, c_32])).
% 3.35/1.58  tff(c_148, plain, (~v1_xboole_0(k2_relat_1('#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_144])).
% 3.35/1.58  tff(c_149, plain, (~v1_xboole_0(k2_relat_1('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_50, c_148])).
% 3.35/1.58  tff(c_118, plain, (![B_46, A_47]: (k1_relat_1(B_46)=A_47 | ~v1_partfun1(B_46, A_47) | ~v4_relat_1(B_46, A_47) | ~v1_relat_1(B_46))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.35/1.58  tff(c_121, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_88, c_118])).
% 3.35/1.58  tff(c_124, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_83, c_121])).
% 3.35/1.58  tff(c_125, plain, (~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_124])).
% 3.35/1.58  tff(c_138, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_131, c_72])).
% 3.35/1.58  tff(c_139, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_131, c_71])).
% 3.35/1.58  tff(c_189, plain, (![C_54, A_55, B_56]: (v1_partfun1(C_54, A_55) | ~v1_funct_2(C_54, A_55, B_56) | ~v1_funct_1(C_54) | ~m1_subset_1(C_54, k1_zfmisc_1(k2_zfmisc_1(A_55, B_56))) | v1_xboole_0(B_56))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.35/1.58  tff(c_192, plain, (v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3') | v1_xboole_0(k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_139, c_189])).
% 3.35/1.58  tff(c_195, plain, (v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | v1_xboole_0(k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_138, c_192])).
% 3.35/1.58  tff(c_197, plain, $false, inference(negUnitSimplification, [status(thm)], [c_149, c_125, c_195])).
% 3.35/1.58  tff(c_198, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_124])).
% 3.35/1.58  tff(c_203, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_198, c_71])).
% 3.35/1.58  tff(c_246, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_203, c_14])).
% 3.35/1.58  tff(c_201, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_198, c_74])).
% 3.35/1.58  tff(c_257, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_246, c_201])).
% 3.35/1.58  tff(c_202, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_198, c_72])).
% 3.35/1.58  tff(c_264, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_257, c_202])).
% 3.35/1.58  tff(c_262, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_257, c_246])).
% 3.35/1.58  tff(c_263, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_257, c_203])).
% 3.35/1.58  tff(c_341, plain, (![A_73, B_74, C_75]: (k2_tops_2(A_73, B_74, C_75)=k2_funct_1(C_75) | ~v2_funct_1(C_75) | k2_relset_1(A_73, B_74, C_75)!=B_74 | ~m1_subset_1(C_75, k1_zfmisc_1(k2_zfmisc_1(A_73, B_74))) | ~v1_funct_2(C_75, A_73, B_74) | ~v1_funct_1(C_75))), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.35/1.58  tff(c_344, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_263, c_341])).
% 3.35/1.58  tff(c_347, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_264, c_262, c_38, c_344])).
% 3.35/1.58  tff(c_36, plain, (k2_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_1') | k1_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.35/1.58  tff(c_94, plain, (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_1') | k1_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_61, c_61, c_60, c_60, c_61, c_61, c_60, c_60, c_36])).
% 3.35/1.58  tff(c_95, plain, (k1_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_94])).
% 3.35/1.58  tff(c_309, plain, (k1_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_257, c_257, c_257, c_198, c_198, c_95])).
% 3.35/1.58  tff(c_348, plain, (k1_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_347, c_309])).
% 3.35/1.58  tff(c_357, plain, (![C_77, B_78, A_79]: (m1_subset_1(k2_funct_1(C_77), k1_zfmisc_1(k2_zfmisc_1(B_78, A_79))) | k2_relset_1(A_79, B_78, C_77)!=B_78 | ~v2_funct_1(C_77) | ~m1_subset_1(C_77, k1_zfmisc_1(k2_zfmisc_1(A_79, B_78))) | ~v1_funct_2(C_77, A_79, B_78) | ~v1_funct_1(C_77))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.35/1.58  tff(c_6, plain, (![C_4, A_2, B_3]: (v1_relat_1(C_4) | ~m1_subset_1(C_4, k1_zfmisc_1(k2_zfmisc_1(A_2, B_3))))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.35/1.58  tff(c_394, plain, (![C_80, A_81, B_82]: (v1_relat_1(k2_funct_1(C_80)) | k2_relset_1(A_81, B_82, C_80)!=B_82 | ~v2_funct_1(C_80) | ~m1_subset_1(C_80, k1_zfmisc_1(k2_zfmisc_1(A_81, B_82))) | ~v1_funct_2(C_80, A_81, B_82) | ~v1_funct_1(C_80))), inference(resolution, [status(thm)], [c_357, c_6])).
% 3.35/1.58  tff(c_400, plain, (v1_relat_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_263, c_394])).
% 3.35/1.58  tff(c_404, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_264, c_38, c_262, c_400])).
% 3.35/1.58  tff(c_10, plain, (![C_7, A_5, B_6]: (v4_relat_1(C_7, A_5) | ~m1_subset_1(C_7, k1_zfmisc_1(k2_zfmisc_1(A_5, B_6))))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.35/1.58  tff(c_416, plain, (![C_86, B_87, A_88]: (v4_relat_1(k2_funct_1(C_86), B_87) | k2_relset_1(A_88, B_87, C_86)!=B_87 | ~v2_funct_1(C_86) | ~m1_subset_1(C_86, k1_zfmisc_1(k2_zfmisc_1(A_88, B_87))) | ~v1_funct_2(C_86, A_88, B_87) | ~v1_funct_1(C_86))), inference(resolution, [status(thm)], [c_357, c_10])).
% 3.35/1.58  tff(c_422, plain, (v4_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_263, c_416])).
% 3.35/1.58  tff(c_426, plain, (v4_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_264, c_38, c_262, c_422])).
% 3.35/1.58  tff(c_4, plain, (![A_1]: (k1_relat_1(k2_funct_1(A_1))=k2_relat_1(A_1) | ~v2_funct_1(A_1) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.35/1.58  tff(c_106, plain, (![A_45]: (k1_relat_1(k2_funct_1(A_45))=k2_relat_1(A_45) | ~v2_funct_1(A_45) | ~v1_funct_1(A_45) | ~v1_relat_1(A_45))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.35/1.58  tff(c_20, plain, (![B_19]: (v1_partfun1(B_19, k1_relat_1(B_19)) | ~v4_relat_1(B_19, k1_relat_1(B_19)) | ~v1_relat_1(B_19))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.35/1.58  tff(c_323, plain, (![A_66]: (v1_partfun1(k2_funct_1(A_66), k1_relat_1(k2_funct_1(A_66))) | ~v4_relat_1(k2_funct_1(A_66), k2_relat_1(A_66)) | ~v1_relat_1(k2_funct_1(A_66)) | ~v2_funct_1(A_66) | ~v1_funct_1(A_66) | ~v1_relat_1(A_66))), inference(superposition, [status(thm), theory('equality')], [c_106, c_20])).
% 3.35/1.58  tff(c_326, plain, (![A_1]: (v1_partfun1(k2_funct_1(A_1), k2_relat_1(A_1)) | ~v4_relat_1(k2_funct_1(A_1), k2_relat_1(A_1)) | ~v1_relat_1(k2_funct_1(A_1)) | ~v2_funct_1(A_1) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1) | ~v2_funct_1(A_1) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(superposition, [status(thm), theory('equality')], [c_4, c_323])).
% 3.35/1.58  tff(c_429, plain, (v1_partfun1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_426, c_326])).
% 3.35/1.58  tff(c_435, plain, (v1_partfun1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_83, c_46, c_38, c_404, c_429])).
% 3.35/1.58  tff(c_22, plain, (![B_19, A_18]: (k1_relat_1(B_19)=A_18 | ~v1_partfun1(B_19, A_18) | ~v4_relat_1(B_19, A_18) | ~v1_relat_1(B_19))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.35/1.58  tff(c_432, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3') | ~v1_partfun1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_426, c_22])).
% 3.35/1.58  tff(c_438, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3') | ~v1_partfun1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_404, c_432])).
% 3.35/1.58  tff(c_440, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_435, c_438])).
% 3.35/1.58  tff(c_12, plain, (![A_8, B_9, C_10]: (k1_relset_1(A_8, B_9, C_10)=k1_relat_1(C_10) | ~m1_subset_1(C_10, k1_zfmisc_1(k2_zfmisc_1(A_8, B_9))))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.35/1.58  tff(c_482, plain, (![B_92, A_93, C_94]: (k1_relset_1(B_92, A_93, k2_funct_1(C_94))=k1_relat_1(k2_funct_1(C_94)) | k2_relset_1(A_93, B_92, C_94)!=B_92 | ~v2_funct_1(C_94) | ~m1_subset_1(C_94, k1_zfmisc_1(k2_zfmisc_1(A_93, B_92))) | ~v1_funct_2(C_94, A_93, B_92) | ~v1_funct_1(C_94))), inference(resolution, [status(thm)], [c_357, c_12])).
% 3.35/1.58  tff(c_488, plain, (k1_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_263, c_482])).
% 3.35/1.58  tff(c_492, plain, (k1_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_264, c_38, c_262, c_440, c_488])).
% 3.35/1.58  tff(c_494, plain, $false, inference(negUnitSimplification, [status(thm)], [c_348, c_492])).
% 3.35/1.58  tff(c_495, plain, (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_94])).
% 3.35/1.58  tff(c_637, plain, (k2_relset_1(k2_struct_0('#skF_2'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_562, c_562, c_562, c_495])).
% 3.35/1.58  tff(c_649, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_643, c_643, c_637])).
% 3.35/1.58  tff(c_740, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_739, c_649])).
% 3.35/1.58  tff(c_898, plain, (k2_relat_1(k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_885, c_740])).
% 3.35/1.58  tff(c_905, plain, (~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2, c_898])).
% 3.35/1.58  tff(c_909, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_83, c_46, c_38, c_905])).
% 3.35/1.58  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.35/1.58  
% 3.35/1.58  Inference rules
% 3.35/1.58  ----------------------
% 3.35/1.58  #Ref     : 0
% 3.35/1.58  #Sup     : 194
% 3.35/1.58  #Fact    : 0
% 3.35/1.58  #Define  : 0
% 3.35/1.58  #Split   : 5
% 3.35/1.58  #Chain   : 0
% 3.35/1.58  #Close   : 0
% 3.35/1.58  
% 3.35/1.58  Ordering : KBO
% 3.35/1.58  
% 3.35/1.58  Simplification rules
% 3.35/1.58  ----------------------
% 3.35/1.58  #Subsume      : 0
% 3.35/1.58  #Demod        : 234
% 3.35/1.58  #Tautology    : 116
% 3.35/1.58  #SimpNegUnit  : 10
% 3.35/1.58  #BackRed      : 36
% 3.35/1.58  
% 3.35/1.58  #Partial instantiations: 0
% 3.35/1.58  #Strategies tried      : 1
% 3.35/1.58  
% 3.35/1.58  Timing (in seconds)
% 3.35/1.58  ----------------------
% 3.35/1.58  Preprocessing        : 0.35
% 3.35/1.58  Parsing              : 0.19
% 3.35/1.58  CNF conversion       : 0.02
% 3.35/1.58  Main loop            : 0.39
% 3.35/1.58  Inferencing          : 0.14
% 3.35/1.58  Reduction            : 0.13
% 3.35/1.58  Demodulation         : 0.09
% 3.35/1.58  BG Simplification    : 0.02
% 3.35/1.58  Subsumption          : 0.06
% 3.35/1.58  Abstraction          : 0.02
% 3.35/1.58  MUC search           : 0.00
% 3.35/1.58  Cooper               : 0.00
% 3.35/1.58  Total                : 0.80
% 3.35/1.58  Index Insertion      : 0.00
% 3.35/1.58  Index Deletion       : 0.00
% 3.35/1.58  Index Matching       : 0.00
% 3.35/1.58  BG Taut test         : 0.00
%------------------------------------------------------------------------------
