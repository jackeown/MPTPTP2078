%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:50 EST 2020

% Result     : Theorem 6.83s
% Output     : CNFRefutation 7.16s
% Verified   : 
% Statistics : Number of formulae       :  215 (9105 expanded)
%              Number of leaves         :   35 (3090 expanded)
%              Depth                    :   23
%              Number of atoms          :  778 (25489 expanded)
%              Number of equality atoms :  123 (4260 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_pre_topc > v3_tops_2 > v1_funct_2 > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_relat_1 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k2_tops_2 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k2_struct_0 > k2_funct_1 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_159,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_tops_2)).

tff(f_50,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_46,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( k2_relset_1(A,B,C) = B
          & v2_funct_1(C) )
       => k2_tops_2(A,B,C) = k2_funct_1(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_2)).

tff(f_86,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tops_2)).

tff(f_98,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( v1_funct_1(k2_tops_2(A,B,C))
        & v1_funct_2(k2_tops_2(A,B,C),B,A)
        & m1_subset_1(k2_tops_2(A,B,C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_2)).

tff(f_139,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ! [B] :
          ( l1_struct_0(B)
         => ! [C] :
              ( ( v1_funct_1(C)
                & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
             => ( ( k2_relset_1(u1_struct_0(A),u1_struct_0(B),C) = k2_struct_0(B)
                  & v2_funct_1(C) )
               => v2_funct_1(k2_tops_2(u1_struct_0(A),u1_struct_0(B),C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_tops_2)).

tff(f_121,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_tops_2)).

tff(f_34,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_42,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(k2_funct_1(A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_1)).

tff(c_46,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_52,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_10,plain,(
    ! [A_8] :
      ( l1_struct_0(A_8)
      | ~ l1_pre_topc(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_55,plain,(
    ! [A_43] :
      ( u1_struct_0(A_43) = k2_struct_0(A_43)
      | ~ l1_struct_0(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_60,plain,(
    ! [A_44] :
      ( u1_struct_0(A_44) = k2_struct_0(A_44)
      | ~ l1_pre_topc(A_44) ) ),
    inference(resolution,[status(thm)],[c_10,c_55])).

tff(c_68,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_52,c_60])).

tff(c_48,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_67,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_60])).

tff(c_44,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_70,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_44])).

tff(c_79,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_70])).

tff(c_42,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_69,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_42])).

tff(c_82,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_69])).

tff(c_144,plain,(
    ! [A_60,B_61,C_62] :
      ( k2_tops_2(A_60,B_61,C_62) = k2_funct_1(C_62)
      | ~ v2_funct_1(C_62)
      | k2_relset_1(A_60,B_61,C_62) != B_61
      | ~ m1_subset_1(C_62,k1_zfmisc_1(k2_zfmisc_1(A_60,B_61)))
      | ~ v1_funct_2(C_62,A_60,B_61)
      | ~ v1_funct_1(C_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_150,plain,
    ( k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_82,c_144])).

tff(c_154,plain,
    ( k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_79,c_150])).

tff(c_155,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_154])).

tff(c_40,plain,(
    v3_tops_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_352,plain,(
    ! [A_87,B_88,C_89] :
      ( k2_relset_1(u1_struct_0(A_87),u1_struct_0(B_88),C_89) = k2_struct_0(B_88)
      | ~ v3_tops_2(C_89,A_87,B_88)
      | ~ m1_subset_1(C_89,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_87),u1_struct_0(B_88))))
      | ~ v1_funct_2(C_89,u1_struct_0(A_87),u1_struct_0(B_88))
      | ~ v1_funct_1(C_89)
      | ~ l1_pre_topc(B_88)
      | ~ l1_pre_topc(A_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_359,plain,(
    ! [B_88,C_89] :
      ( k2_relset_1(u1_struct_0('#skF_1'),u1_struct_0(B_88),C_89) = k2_struct_0(B_88)
      | ~ v3_tops_2(C_89,'#skF_1',B_88)
      | ~ m1_subset_1(C_89,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),u1_struct_0(B_88))))
      | ~ v1_funct_2(C_89,u1_struct_0('#skF_1'),u1_struct_0(B_88))
      | ~ v1_funct_1(C_89)
      | ~ l1_pre_topc(B_88)
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_352])).

tff(c_498,plain,(
    ! [B_106,C_107] :
      ( k2_relset_1(k2_struct_0('#skF_1'),u1_struct_0(B_106),C_107) = k2_struct_0(B_106)
      | ~ v3_tops_2(C_107,'#skF_1',B_106)
      | ~ m1_subset_1(C_107,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),u1_struct_0(B_106))))
      | ~ v1_funct_2(C_107,k2_struct_0('#skF_1'),u1_struct_0(B_106))
      | ~ v1_funct_1(C_107)
      | ~ l1_pre_topc(B_106) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_68,c_68,c_359])).

tff(c_508,plain,(
    ! [C_107] :
      ( k2_relset_1(k2_struct_0('#skF_1'),u1_struct_0('#skF_2'),C_107) = k2_struct_0('#skF_2')
      | ~ v3_tops_2(C_107,'#skF_1','#skF_2')
      | ~ m1_subset_1(C_107,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_107,k2_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_107)
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_67,c_498])).

tff(c_514,plain,(
    ! [C_108] :
      ( k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_108) = k2_struct_0('#skF_2')
      | ~ v3_tops_2(C_108,'#skF_1','#skF_2')
      | ~ m1_subset_1(C_108,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_108,k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_108) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_67,c_67,c_508])).

tff(c_521,plain,
    ( k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2')
    | ~ v3_tops_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_82,c_514])).

tff(c_525,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_79,c_40,c_521])).

tff(c_527,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_155,c_525])).

tff(c_528,plain,
    ( ~ v2_funct_1('#skF_3')
    | k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_154])).

tff(c_534,plain,(
    ~ v2_funct_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_528])).

tff(c_535,plain,(
    ! [C_109,A_110,B_111] :
      ( v2_funct_1(C_109)
      | ~ v3_tops_2(C_109,A_110,B_111)
      | ~ m1_subset_1(C_109,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_110),u1_struct_0(B_111))))
      | ~ v1_funct_2(C_109,u1_struct_0(A_110),u1_struct_0(B_111))
      | ~ v1_funct_1(C_109)
      | ~ l1_pre_topc(B_111)
      | ~ l1_pre_topc(A_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_542,plain,(
    ! [C_109,B_111] :
      ( v2_funct_1(C_109)
      | ~ v3_tops_2(C_109,'#skF_1',B_111)
      | ~ m1_subset_1(C_109,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),u1_struct_0(B_111))))
      | ~ v1_funct_2(C_109,u1_struct_0('#skF_1'),u1_struct_0(B_111))
      | ~ v1_funct_1(C_109)
      | ~ l1_pre_topc(B_111)
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_535])).

tff(c_561,plain,(
    ! [C_112,B_113] :
      ( v2_funct_1(C_112)
      | ~ v3_tops_2(C_112,'#skF_1',B_113)
      | ~ m1_subset_1(C_112,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),u1_struct_0(B_113))))
      | ~ v1_funct_2(C_112,k2_struct_0('#skF_1'),u1_struct_0(B_113))
      | ~ v1_funct_1(C_112)
      | ~ l1_pre_topc(B_113) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_68,c_542])).

tff(c_571,plain,(
    ! [C_112] :
      ( v2_funct_1(C_112)
      | ~ v3_tops_2(C_112,'#skF_1','#skF_2')
      | ~ m1_subset_1(C_112,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_112,k2_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_112)
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_67,c_561])).

tff(c_583,plain,(
    ! [C_115] :
      ( v2_funct_1(C_115)
      | ~ v3_tops_2(C_115,'#skF_1','#skF_2')
      | ~ m1_subset_1(C_115,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_115,k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_115) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_67,c_571])).

tff(c_590,plain,
    ( v2_funct_1('#skF_3')
    | ~ v3_tops_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_82,c_583])).

tff(c_594,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_79,c_40,c_590])).

tff(c_596,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_534,c_594])).

tff(c_597,plain,(
    k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_528])).

tff(c_38,plain,(
    ~ v3_tops_2(k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3'),'#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_81,plain,(
    ~ v3_tops_2(k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3'),'#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_67,c_38])).

tff(c_628,plain,(
    ~ v3_tops_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_597,c_81])).

tff(c_106,plain,(
    ! [A_48,B_49,C_50] :
      ( v1_funct_1(k2_tops_2(A_48,B_49,C_50))
      | ~ m1_subset_1(C_50,k1_zfmisc_1(k2_zfmisc_1(A_48,B_49)))
      | ~ v1_funct_2(C_50,A_48,B_49)
      | ~ v1_funct_1(C_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_109,plain,
    ( v1_funct_1(k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3'))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_82,c_106])).

tff(c_112,plain,(
    v1_funct_1(k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_79,c_109])).

tff(c_627,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_597,c_112])).

tff(c_113,plain,(
    ! [A_51,B_52,C_53] :
      ( v1_funct_2(k2_tops_2(A_51,B_52,C_53),B_52,A_51)
      | ~ m1_subset_1(C_53,k1_zfmisc_1(k2_zfmisc_1(A_51,B_52)))
      | ~ v1_funct_2(C_53,A_51,B_52)
      | ~ v1_funct_1(C_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_115,plain,
    ( v1_funct_2(k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3'),k2_struct_0('#skF_2'),k2_struct_0('#skF_1'))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_82,c_113])).

tff(c_118,plain,(
    v1_funct_2(k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3'),k2_struct_0('#skF_2'),k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_79,c_115])).

tff(c_626,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),k2_struct_0('#skF_2'),k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_597,c_118])).

tff(c_529,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_154])).

tff(c_598,plain,(
    v2_funct_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_528])).

tff(c_2813,plain,(
    ! [A_355,B_356,C_357] :
      ( v2_funct_1(k2_tops_2(u1_struct_0(A_355),u1_struct_0(B_356),C_357))
      | ~ v2_funct_1(C_357)
      | k2_relset_1(u1_struct_0(A_355),u1_struct_0(B_356),C_357) != k2_struct_0(B_356)
      | ~ m1_subset_1(C_357,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_355),u1_struct_0(B_356))))
      | ~ v1_funct_2(C_357,u1_struct_0(A_355),u1_struct_0(B_356))
      | ~ v1_funct_1(C_357)
      | ~ l1_struct_0(B_356)
      | ~ l1_struct_0(A_355) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_2823,plain,(
    ! [A_355,C_357] :
      ( v2_funct_1(k2_tops_2(u1_struct_0(A_355),u1_struct_0('#skF_1'),C_357))
      | ~ v2_funct_1(C_357)
      | k2_relset_1(u1_struct_0(A_355),u1_struct_0('#skF_1'),C_357) != k2_struct_0('#skF_1')
      | ~ m1_subset_1(C_357,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_355),k2_struct_0('#skF_1'))))
      | ~ v1_funct_2(C_357,u1_struct_0(A_355),u1_struct_0('#skF_1'))
      | ~ v1_funct_1(C_357)
      | ~ l1_struct_0('#skF_1')
      | ~ l1_struct_0(A_355) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_2813])).

tff(c_2832,plain,(
    ! [A_355,C_357] :
      ( v2_funct_1(k2_tops_2(u1_struct_0(A_355),k2_struct_0('#skF_1'),C_357))
      | ~ v2_funct_1(C_357)
      | k2_relset_1(u1_struct_0(A_355),k2_struct_0('#skF_1'),C_357) != k2_struct_0('#skF_1')
      | ~ m1_subset_1(C_357,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_355),k2_struct_0('#skF_1'))))
      | ~ v1_funct_2(C_357,u1_struct_0(A_355),k2_struct_0('#skF_1'))
      | ~ v1_funct_1(C_357)
      | ~ l1_struct_0('#skF_1')
      | ~ l1_struct_0(A_355) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_68,c_68,c_2823])).

tff(c_3509,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_2832])).

tff(c_3512,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_10,c_3509])).

tff(c_3516,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_3512])).

tff(c_3518,plain,(
    l1_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_2832])).

tff(c_50,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_2957,plain,(
    ! [B_362,A_363,C_364] :
      ( k1_relset_1(u1_struct_0(B_362),u1_struct_0(A_363),k2_tops_2(u1_struct_0(A_363),u1_struct_0(B_362),C_364)) = k2_struct_0(B_362)
      | ~ v2_funct_1(C_364)
      | k2_relset_1(u1_struct_0(A_363),u1_struct_0(B_362),C_364) != k2_struct_0(B_362)
      | ~ m1_subset_1(C_364,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_363),u1_struct_0(B_362))))
      | ~ v1_funct_2(C_364,u1_struct_0(A_363),u1_struct_0(B_362))
      | ~ v1_funct_1(C_364)
      | ~ l1_struct_0(B_362)
      | v2_struct_0(B_362)
      | ~ l1_struct_0(A_363) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_2978,plain,(
    ! [A_363,C_364] :
      ( k1_relset_1(k2_struct_0('#skF_2'),u1_struct_0(A_363),k2_tops_2(u1_struct_0(A_363),u1_struct_0('#skF_2'),C_364)) = k2_struct_0('#skF_2')
      | ~ v2_funct_1(C_364)
      | k2_relset_1(u1_struct_0(A_363),u1_struct_0('#skF_2'),C_364) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_364,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_363),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_364,u1_struct_0(A_363),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_364)
      | ~ l1_struct_0('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_struct_0(A_363) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_67,c_2957])).

tff(c_2994,plain,(
    ! [A_363,C_364] :
      ( k1_relset_1(k2_struct_0('#skF_2'),u1_struct_0(A_363),k2_tops_2(u1_struct_0(A_363),k2_struct_0('#skF_2'),C_364)) = k2_struct_0('#skF_2')
      | ~ v2_funct_1(C_364)
      | k2_relset_1(u1_struct_0(A_363),k2_struct_0('#skF_2'),C_364) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_364,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_363),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_364,u1_struct_0(A_363),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_364)
      | ~ l1_struct_0('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_struct_0(A_363) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_67,c_67,c_67,c_2978])).

tff(c_2995,plain,(
    ! [A_363,C_364] :
      ( k1_relset_1(k2_struct_0('#skF_2'),u1_struct_0(A_363),k2_tops_2(u1_struct_0(A_363),k2_struct_0('#skF_2'),C_364)) = k2_struct_0('#skF_2')
      | ~ v2_funct_1(C_364)
      | k2_relset_1(u1_struct_0(A_363),k2_struct_0('#skF_2'),C_364) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_364,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_363),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_364,u1_struct_0(A_363),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_364)
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0(A_363) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_2994])).

tff(c_3016,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_2995])).

tff(c_3019,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_10,c_3016])).

tff(c_3023,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_3019])).

tff(c_3025,plain,(
    l1_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_2995])).

tff(c_2987,plain,(
    ! [A_363,C_364] :
      ( k1_relset_1(u1_struct_0('#skF_2'),u1_struct_0(A_363),k2_tops_2(u1_struct_0(A_363),k2_struct_0('#skF_2'),C_364)) = k2_struct_0('#skF_2')
      | ~ v2_funct_1(C_364)
      | k2_relset_1(u1_struct_0(A_363),u1_struct_0('#skF_2'),C_364) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_364,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_363),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_364,u1_struct_0(A_363),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_364)
      | ~ l1_struct_0('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_struct_0(A_363) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_67,c_2957])).

tff(c_2998,plain,(
    ! [A_363,C_364] :
      ( k1_relset_1(k2_struct_0('#skF_2'),u1_struct_0(A_363),k2_tops_2(u1_struct_0(A_363),k2_struct_0('#skF_2'),C_364)) = k2_struct_0('#skF_2')
      | ~ v2_funct_1(C_364)
      | k2_relset_1(u1_struct_0(A_363),k2_struct_0('#skF_2'),C_364) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_364,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_363),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_364,u1_struct_0(A_363),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_364)
      | ~ l1_struct_0('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_struct_0(A_363) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_67,c_67,c_67,c_2987])).

tff(c_2999,plain,(
    ! [A_363,C_364] :
      ( k1_relset_1(k2_struct_0('#skF_2'),u1_struct_0(A_363),k2_tops_2(u1_struct_0(A_363),k2_struct_0('#skF_2'),C_364)) = k2_struct_0('#skF_2')
      | ~ v2_funct_1(C_364)
      | k2_relset_1(u1_struct_0(A_363),k2_struct_0('#skF_2'),C_364) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_364,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_363),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_364,u1_struct_0(A_363),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_364)
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0(A_363) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_2998])).

tff(c_3414,plain,(
    ! [A_405,C_406] :
      ( k1_relset_1(k2_struct_0('#skF_2'),u1_struct_0(A_405),k2_tops_2(u1_struct_0(A_405),k2_struct_0('#skF_2'),C_406)) = k2_struct_0('#skF_2')
      | ~ v2_funct_1(C_406)
      | k2_relset_1(u1_struct_0(A_405),k2_struct_0('#skF_2'),C_406) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_406,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_405),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_406,u1_struct_0(A_405),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_406)
      | ~ l1_struct_0(A_405) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3025,c_2999])).

tff(c_3426,plain,(
    ! [C_406] :
      ( k1_relset_1(k2_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_406)) = k2_struct_0('#skF_2')
      | ~ v2_funct_1(C_406)
      | k2_relset_1(u1_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_406) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_406,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_406,u1_struct_0('#skF_1'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_406)
      | ~ l1_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_3414])).

tff(c_3436,plain,(
    ! [C_406] :
      ( k1_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_406)) = k2_struct_0('#skF_2')
      | ~ v2_funct_1(C_406)
      | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_406) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_406,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_406,k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_406)
      | ~ l1_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_68,c_68,c_68,c_3426])).

tff(c_3739,plain,(
    ! [C_439] :
      ( k1_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_439)) = k2_struct_0('#skF_2')
      | ~ v2_funct_1(C_439)
      | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_439) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_439,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_439,k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_439) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3518,c_3436])).

tff(c_3751,plain,
    ( k1_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) = k2_struct_0('#skF_2')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_597,c_3739])).

tff(c_3757,plain,(
    k1_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_79,c_82,c_529,c_598,c_3751])).

tff(c_26,plain,(
    ! [A_19,B_20,C_21] :
      ( m1_subset_1(k2_tops_2(A_19,B_20,C_21),k1_zfmisc_1(k2_zfmisc_1(B_20,A_19)))
      | ~ m1_subset_1(C_21,k1_zfmisc_1(k2_zfmisc_1(A_19,B_20)))
      | ~ v1_funct_2(C_21,A_19,B_20)
      | ~ v1_funct_1(C_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_632,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'))))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_597,c_26])).

tff(c_636,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_79,c_82,c_632])).

tff(c_12,plain,(
    ! [A_9,B_10,C_11] :
      ( k2_tops_2(A_9,B_10,C_11) = k2_funct_1(C_11)
      | ~ v2_funct_1(C_11)
      | k2_relset_1(A_9,B_10,C_11) != B_10
      | ~ m1_subset_1(C_11,k1_zfmisc_1(k2_zfmisc_1(A_9,B_10)))
      | ~ v1_funct_2(C_11,A_9,B_10)
      | ~ v1_funct_1(C_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_640,plain,
    ( k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) != k2_struct_0('#skF_1')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),k2_struct_0('#skF_2'),k2_struct_0('#skF_1'))
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_636,c_12])).

tff(c_654,plain,
    ( k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) != k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_627,c_626,c_640])).

tff(c_693,plain,(
    k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) != k2_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_654])).

tff(c_1156,plain,(
    ! [A_177,B_178,C_179] :
      ( v2_funct_1(k2_tops_2(u1_struct_0(A_177),u1_struct_0(B_178),C_179))
      | ~ v2_funct_1(C_179)
      | k2_relset_1(u1_struct_0(A_177),u1_struct_0(B_178),C_179) != k2_struct_0(B_178)
      | ~ m1_subset_1(C_179,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_177),u1_struct_0(B_178))))
      | ~ v1_funct_2(C_179,u1_struct_0(A_177),u1_struct_0(B_178))
      | ~ v1_funct_1(C_179)
      | ~ l1_struct_0(B_178)
      | ~ l1_struct_0(A_177) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_1166,plain,(
    ! [A_177,C_179] :
      ( v2_funct_1(k2_tops_2(u1_struct_0(A_177),u1_struct_0('#skF_1'),C_179))
      | ~ v2_funct_1(C_179)
      | k2_relset_1(u1_struct_0(A_177),u1_struct_0('#skF_1'),C_179) != k2_struct_0('#skF_1')
      | ~ m1_subset_1(C_179,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_177),k2_struct_0('#skF_1'))))
      | ~ v1_funct_2(C_179,u1_struct_0(A_177),u1_struct_0('#skF_1'))
      | ~ v1_funct_1(C_179)
      | ~ l1_struct_0('#skF_1')
      | ~ l1_struct_0(A_177) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_1156])).

tff(c_1175,plain,(
    ! [A_177,C_179] :
      ( v2_funct_1(k2_tops_2(u1_struct_0(A_177),k2_struct_0('#skF_1'),C_179))
      | ~ v2_funct_1(C_179)
      | k2_relset_1(u1_struct_0(A_177),k2_struct_0('#skF_1'),C_179) != k2_struct_0('#skF_1')
      | ~ m1_subset_1(C_179,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_177),k2_struct_0('#skF_1'))))
      | ~ v1_funct_2(C_179,u1_struct_0(A_177),k2_struct_0('#skF_1'))
      | ~ v1_funct_1(C_179)
      | ~ l1_struct_0('#skF_1')
      | ~ l1_struct_0(A_177) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_68,c_68,c_1166])).

tff(c_1421,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_1175])).

tff(c_1424,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_10,c_1421])).

tff(c_1428,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_1424])).

tff(c_1430,plain,(
    l1_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_1175])).

tff(c_1269,plain,(
    ! [B_192,A_193,C_194] :
      ( k1_relset_1(u1_struct_0(B_192),u1_struct_0(A_193),k2_tops_2(u1_struct_0(A_193),u1_struct_0(B_192),C_194)) = k2_struct_0(B_192)
      | ~ v2_funct_1(C_194)
      | k2_relset_1(u1_struct_0(A_193),u1_struct_0(B_192),C_194) != k2_struct_0(B_192)
      | ~ m1_subset_1(C_194,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_193),u1_struct_0(B_192))))
      | ~ v1_funct_2(C_194,u1_struct_0(A_193),u1_struct_0(B_192))
      | ~ v1_funct_1(C_194)
      | ~ l1_struct_0(B_192)
      | v2_struct_0(B_192)
      | ~ l1_struct_0(A_193) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_1299,plain,(
    ! [A_193,C_194] :
      ( k1_relset_1(u1_struct_0('#skF_2'),u1_struct_0(A_193),k2_tops_2(u1_struct_0(A_193),k2_struct_0('#skF_2'),C_194)) = k2_struct_0('#skF_2')
      | ~ v2_funct_1(C_194)
      | k2_relset_1(u1_struct_0(A_193),u1_struct_0('#skF_2'),C_194) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_194,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_193),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_194,u1_struct_0(A_193),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_194)
      | ~ l1_struct_0('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_struct_0(A_193) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_67,c_1269])).

tff(c_1310,plain,(
    ! [A_193,C_194] :
      ( k1_relset_1(k2_struct_0('#skF_2'),u1_struct_0(A_193),k2_tops_2(u1_struct_0(A_193),k2_struct_0('#skF_2'),C_194)) = k2_struct_0('#skF_2')
      | ~ v2_funct_1(C_194)
      | k2_relset_1(u1_struct_0(A_193),k2_struct_0('#skF_2'),C_194) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_194,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_193),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_194,u1_struct_0(A_193),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_194)
      | ~ l1_struct_0('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_struct_0(A_193) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_67,c_67,c_67,c_1299])).

tff(c_1311,plain,(
    ! [A_193,C_194] :
      ( k1_relset_1(k2_struct_0('#skF_2'),u1_struct_0(A_193),k2_tops_2(u1_struct_0(A_193),k2_struct_0('#skF_2'),C_194)) = k2_struct_0('#skF_2')
      | ~ v2_funct_1(C_194)
      | k2_relset_1(u1_struct_0(A_193),k2_struct_0('#skF_2'),C_194) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_194,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_193),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_194,u1_struct_0(A_193),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_194)
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0(A_193) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_1310])).

tff(c_1339,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_1311])).

tff(c_1342,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_10,c_1339])).

tff(c_1346,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_1342])).

tff(c_1348,plain,(
    l1_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_1311])).

tff(c_1374,plain,(
    ! [B_206,A_207,C_208] :
      ( k2_relset_1(u1_struct_0(B_206),u1_struct_0(A_207),k2_tops_2(u1_struct_0(A_207),u1_struct_0(B_206),C_208)) = k2_struct_0(A_207)
      | ~ v2_funct_1(C_208)
      | k2_relset_1(u1_struct_0(A_207),u1_struct_0(B_206),C_208) != k2_struct_0(B_206)
      | ~ m1_subset_1(C_208,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_207),u1_struct_0(B_206))))
      | ~ v1_funct_2(C_208,u1_struct_0(A_207),u1_struct_0(B_206))
      | ~ v1_funct_1(C_208)
      | ~ l1_struct_0(B_206)
      | v2_struct_0(B_206)
      | ~ l1_struct_0(A_207) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_1395,plain,(
    ! [A_207,C_208] :
      ( k2_relset_1(k2_struct_0('#skF_2'),u1_struct_0(A_207),k2_tops_2(u1_struct_0(A_207),u1_struct_0('#skF_2'),C_208)) = k2_struct_0(A_207)
      | ~ v2_funct_1(C_208)
      | k2_relset_1(u1_struct_0(A_207),u1_struct_0('#skF_2'),C_208) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_208,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_207),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_208,u1_struct_0(A_207),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_208)
      | ~ l1_struct_0('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_struct_0(A_207) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_67,c_1374])).

tff(c_1412,plain,(
    ! [A_207,C_208] :
      ( k2_relset_1(k2_struct_0('#skF_2'),u1_struct_0(A_207),k2_tops_2(u1_struct_0(A_207),k2_struct_0('#skF_2'),C_208)) = k2_struct_0(A_207)
      | ~ v2_funct_1(C_208)
      | k2_relset_1(u1_struct_0(A_207),k2_struct_0('#skF_2'),C_208) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_208,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_207),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_208,u1_struct_0(A_207),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_208)
      | v2_struct_0('#skF_2')
      | ~ l1_struct_0(A_207) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1348,c_67,c_67,c_67,c_67,c_1395])).

tff(c_1436,plain,(
    ! [A_209,C_210] :
      ( k2_relset_1(k2_struct_0('#skF_2'),u1_struct_0(A_209),k2_tops_2(u1_struct_0(A_209),k2_struct_0('#skF_2'),C_210)) = k2_struct_0(A_209)
      | ~ v2_funct_1(C_210)
      | k2_relset_1(u1_struct_0(A_209),k2_struct_0('#skF_2'),C_210) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_210,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_209),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_210,u1_struct_0(A_209),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_210)
      | ~ l1_struct_0(A_209) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_1412])).

tff(c_1445,plain,(
    ! [C_210] :
      ( k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_210)) = k2_struct_0('#skF_1')
      | ~ v2_funct_1(C_210)
      | k2_relset_1(u1_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_210) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_210,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_210,u1_struct_0('#skF_1'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_210)
      | ~ l1_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_1436])).

tff(c_1597,plain,(
    ! [C_227] :
      ( k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_227)) = k2_struct_0('#skF_1')
      | ~ v2_funct_1(C_227)
      | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_227) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_227,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_227,k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_227) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1430,c_68,c_68,c_68,c_68,c_1445])).

tff(c_1606,plain,
    ( k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) = k2_struct_0('#skF_1')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_597,c_1597])).

tff(c_1610,plain,(
    k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) = k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_79,c_82,c_529,c_598,c_1606])).

tff(c_1612,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_693,c_1610])).

tff(c_1614,plain,(
    k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) = k2_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_654])).

tff(c_1613,plain,
    ( ~ v2_funct_1(k2_funct_1('#skF_3'))
    | k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_654])).

tff(c_1619,plain,(
    ~ v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1613])).

tff(c_2133,plain,(
    ! [B_290,A_291,C_292] :
      ( k2_relset_1(u1_struct_0(B_290),u1_struct_0(A_291),k2_tops_2(u1_struct_0(A_291),u1_struct_0(B_290),C_292)) = k2_struct_0(A_291)
      | ~ v2_funct_1(C_292)
      | k2_relset_1(u1_struct_0(A_291),u1_struct_0(B_290),C_292) != k2_struct_0(B_290)
      | ~ m1_subset_1(C_292,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_291),u1_struct_0(B_290))))
      | ~ v1_funct_2(C_292,u1_struct_0(A_291),u1_struct_0(B_290))
      | ~ v1_funct_1(C_292)
      | ~ l1_struct_0(B_290)
      | v2_struct_0(B_290)
      | ~ l1_struct_0(A_291) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_2154,plain,(
    ! [A_291,C_292] :
      ( k2_relset_1(k2_struct_0('#skF_2'),u1_struct_0(A_291),k2_tops_2(u1_struct_0(A_291),u1_struct_0('#skF_2'),C_292)) = k2_struct_0(A_291)
      | ~ v2_funct_1(C_292)
      | k2_relset_1(u1_struct_0(A_291),u1_struct_0('#skF_2'),C_292) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_292,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_291),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_292,u1_struct_0(A_291),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_292)
      | ~ l1_struct_0('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_struct_0(A_291) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_67,c_2133])).

tff(c_2170,plain,(
    ! [A_291,C_292] :
      ( k2_relset_1(k2_struct_0('#skF_2'),u1_struct_0(A_291),k2_tops_2(u1_struct_0(A_291),k2_struct_0('#skF_2'),C_292)) = k2_struct_0(A_291)
      | ~ v2_funct_1(C_292)
      | k2_relset_1(u1_struct_0(A_291),k2_struct_0('#skF_2'),C_292) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_292,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_291),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_292,u1_struct_0(A_291),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_292)
      | ~ l1_struct_0('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_struct_0(A_291) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_67,c_67,c_67,c_2154])).

tff(c_2171,plain,(
    ! [A_291,C_292] :
      ( k2_relset_1(k2_struct_0('#skF_2'),u1_struct_0(A_291),k2_tops_2(u1_struct_0(A_291),k2_struct_0('#skF_2'),C_292)) = k2_struct_0(A_291)
      | ~ v2_funct_1(C_292)
      | k2_relset_1(u1_struct_0(A_291),k2_struct_0('#skF_2'),C_292) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_292,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_291),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_292,u1_struct_0(A_291),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_292)
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0(A_291) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_2170])).

tff(c_2194,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_2171])).

tff(c_2197,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_10,c_2194])).

tff(c_2201,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_2197])).

tff(c_2203,plain,(
    l1_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_2171])).

tff(c_1994,plain,(
    ! [A_272,B_273,C_274] :
      ( v2_funct_1(k2_tops_2(u1_struct_0(A_272),u1_struct_0(B_273),C_274))
      | ~ v2_funct_1(C_274)
      | k2_relset_1(u1_struct_0(A_272),u1_struct_0(B_273),C_274) != k2_struct_0(B_273)
      | ~ m1_subset_1(C_274,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_272),u1_struct_0(B_273))))
      | ~ v1_funct_2(C_274,u1_struct_0(A_272),u1_struct_0(B_273))
      | ~ v1_funct_1(C_274)
      | ~ l1_struct_0(B_273)
      | ~ l1_struct_0(A_272) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_2001,plain,(
    ! [B_273,C_274] :
      ( v2_funct_1(k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0(B_273),C_274))
      | ~ v2_funct_1(C_274)
      | k2_relset_1(u1_struct_0('#skF_1'),u1_struct_0(B_273),C_274) != k2_struct_0(B_273)
      | ~ m1_subset_1(C_274,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),u1_struct_0(B_273))))
      | ~ v1_funct_2(C_274,u1_struct_0('#skF_1'),u1_struct_0(B_273))
      | ~ v1_funct_1(C_274)
      | ~ l1_struct_0(B_273)
      | ~ l1_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_1994])).

tff(c_2012,plain,(
    ! [B_273,C_274] :
      ( v2_funct_1(k2_tops_2(k2_struct_0('#skF_1'),u1_struct_0(B_273),C_274))
      | ~ v2_funct_1(C_274)
      | k2_relset_1(k2_struct_0('#skF_1'),u1_struct_0(B_273),C_274) != k2_struct_0(B_273)
      | ~ m1_subset_1(C_274,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),u1_struct_0(B_273))))
      | ~ v1_funct_2(C_274,k2_struct_0('#skF_1'),u1_struct_0(B_273))
      | ~ v1_funct_1(C_274)
      | ~ l1_struct_0(B_273)
      | ~ l1_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_68,c_68,c_2001])).

tff(c_2374,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_2012])).

tff(c_2394,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_10,c_2374])).

tff(c_2398,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_2394])).

tff(c_2406,plain,(
    ! [B_320,C_321] :
      ( v2_funct_1(k2_tops_2(k2_struct_0('#skF_1'),u1_struct_0(B_320),C_321))
      | ~ v2_funct_1(C_321)
      | k2_relset_1(k2_struct_0('#skF_1'),u1_struct_0(B_320),C_321) != k2_struct_0(B_320)
      | ~ m1_subset_1(C_321,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),u1_struct_0(B_320))))
      | ~ v1_funct_2(C_321,k2_struct_0('#skF_1'),u1_struct_0(B_320))
      | ~ v1_funct_1(C_321)
      | ~ l1_struct_0(B_320) ) ),
    inference(splitRight,[status(thm)],[c_2012])).

tff(c_2416,plain,(
    ! [C_321] :
      ( v2_funct_1(k2_tops_2(k2_struct_0('#skF_1'),u1_struct_0('#skF_2'),C_321))
      | ~ v2_funct_1(C_321)
      | k2_relset_1(k2_struct_0('#skF_1'),u1_struct_0('#skF_2'),C_321) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_321,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_321,k2_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_321)
      | ~ l1_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_67,c_2406])).

tff(c_2428,plain,(
    ! [C_323] :
      ( v2_funct_1(k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_323))
      | ~ v2_funct_1(C_323)
      | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_323) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_323,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_323,k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_323) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2203,c_67,c_67,c_67,c_2416])).

tff(c_2435,plain,
    ( v2_funct_1(k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_82,c_2428])).

tff(c_2439,plain,(
    v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_79,c_529,c_598,c_597,c_2435])).

tff(c_2441,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1619,c_2439])).

tff(c_2443,plain,(
    v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1613])).

tff(c_2697,plain,(
    ! [A_342,B_343,C_344] :
      ( v5_pre_topc(k2_tops_2(u1_struct_0(A_342),u1_struct_0(B_343),C_344),B_343,A_342)
      | ~ v3_tops_2(C_344,A_342,B_343)
      | ~ m1_subset_1(C_344,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_342),u1_struct_0(B_343))))
      | ~ v1_funct_2(C_344,u1_struct_0(A_342),u1_struct_0(B_343))
      | ~ v1_funct_1(C_344)
      | ~ l1_pre_topc(B_343)
      | ~ l1_pre_topc(A_342) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_2702,plain,(
    ! [B_343,C_344] :
      ( v5_pre_topc(k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0(B_343),C_344),B_343,'#skF_1')
      | ~ v3_tops_2(C_344,'#skF_1',B_343)
      | ~ m1_subset_1(C_344,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),u1_struct_0(B_343))))
      | ~ v1_funct_2(C_344,u1_struct_0('#skF_1'),u1_struct_0(B_343))
      | ~ v1_funct_1(C_344)
      | ~ l1_pre_topc(B_343)
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_2697])).

tff(c_3381,plain,(
    ! [B_402,C_403] :
      ( v5_pre_topc(k2_tops_2(k2_struct_0('#skF_1'),u1_struct_0(B_402),C_403),B_402,'#skF_1')
      | ~ v3_tops_2(C_403,'#skF_1',B_402)
      | ~ m1_subset_1(C_403,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),u1_struct_0(B_402))))
      | ~ v1_funct_2(C_403,k2_struct_0('#skF_1'),u1_struct_0(B_402))
      | ~ v1_funct_1(C_403)
      | ~ l1_pre_topc(B_402) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_68,c_68,c_2702])).

tff(c_3388,plain,(
    ! [C_403] :
      ( v5_pre_topc(k2_tops_2(k2_struct_0('#skF_1'),u1_struct_0('#skF_2'),C_403),'#skF_2','#skF_1')
      | ~ v3_tops_2(C_403,'#skF_1','#skF_2')
      | ~ m1_subset_1(C_403,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_403,k2_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_403)
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_67,c_3381])).

tff(c_3394,plain,(
    ! [C_404] :
      ( v5_pre_topc(k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_404),'#skF_2','#skF_1')
      | ~ v3_tops_2(C_404,'#skF_1','#skF_2')
      | ~ m1_subset_1(C_404,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_404,k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_404) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_67,c_67,c_3388])).

tff(c_3404,plain,
    ( v5_pre_topc(k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3'),'#skF_2','#skF_1')
    | ~ v3_tops_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_82,c_3394])).

tff(c_3411,plain,(
    v5_pre_topc(k2_funct_1('#skF_3'),'#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_79,c_40,c_597,c_3404])).

tff(c_2442,plain,(
    k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1613])).

tff(c_30,plain,(
    ! [A_19,B_20,C_21] :
      ( v1_funct_1(k2_tops_2(A_19,B_20,C_21))
      | ~ m1_subset_1(C_21,k1_zfmisc_1(k2_zfmisc_1(A_19,B_20)))
      | ~ v1_funct_2(C_21,A_19,B_20)
      | ~ v1_funct_1(C_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_648,plain,
    ( v1_funct_1(k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')))
    | ~ v1_funct_2(k2_funct_1('#skF_3'),k2_struct_0('#skF_2'),k2_struct_0('#skF_1'))
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_636,c_30])).

tff(c_663,plain,(
    v1_funct_1(k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_627,c_626,c_648])).

tff(c_2445,plain,(
    v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2442,c_663])).

tff(c_28,plain,(
    ! [A_19,B_20,C_21] :
      ( v1_funct_2(k2_tops_2(A_19,B_20,C_21),B_20,A_19)
      | ~ m1_subset_1(C_21,k1_zfmisc_1(k2_zfmisc_1(A_19,B_20)))
      | ~ v1_funct_2(C_21,A_19,B_20)
      | ~ v1_funct_1(C_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_645,plain,
    ( v1_funct_2(k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')),k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_2(k2_funct_1('#skF_3'),k2_struct_0('#skF_2'),k2_struct_0('#skF_1'))
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_636,c_28])).

tff(c_660,plain,(
    v1_funct_2(k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')),k2_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_627,c_626,c_645])).

tff(c_2444,plain,(
    v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')),k2_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2442,c_660])).

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_2,plain,(
    ! [B_3,A_1] :
      ( v1_relat_1(B_3)
      | ~ m1_subset_1(B_3,k1_zfmisc_1(A_1))
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_85,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_82,c_2])).

tff(c_88,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_85])).

tff(c_6,plain,(
    ! [A_6] :
      ( k2_funct_1(k2_funct_1(A_6)) = A_6
      | ~ v2_funct_1(A_6)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_2450,plain,
    ( m1_subset_1(k2_funct_1(k2_funct_1('#skF_3')),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
    | ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'))))
    | ~ v1_funct_2(k2_funct_1('#skF_3'),k2_struct_0('#skF_2'),k2_struct_0('#skF_1'))
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2442,c_26])).

tff(c_2454,plain,(
    m1_subset_1(k2_funct_1(k2_funct_1('#skF_3')),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_627,c_626,c_636,c_2450])).

tff(c_599,plain,(
    ! [C_116,A_117,B_118] :
      ( v2_funct_1(C_116)
      | ~ v3_tops_2(C_116,A_117,B_118)
      | ~ m1_subset_1(C_116,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_117),u1_struct_0(B_118))))
      | ~ v1_funct_2(C_116,u1_struct_0(A_117),u1_struct_0(B_118))
      | ~ v1_funct_1(C_116)
      | ~ l1_pre_topc(B_118)
      | ~ l1_pre_topc(A_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_606,plain,(
    ! [C_116,B_118] :
      ( v2_funct_1(C_116)
      | ~ v3_tops_2(C_116,'#skF_1',B_118)
      | ~ m1_subset_1(C_116,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),u1_struct_0(B_118))))
      | ~ v1_funct_2(C_116,u1_struct_0('#skF_1'),u1_struct_0(B_118))
      | ~ v1_funct_1(C_116)
      | ~ l1_pre_topc(B_118)
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_599])).

tff(c_2628,plain,(
    ! [C_337,B_338] :
      ( v2_funct_1(C_337)
      | ~ v3_tops_2(C_337,'#skF_1',B_338)
      | ~ m1_subset_1(C_337,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),u1_struct_0(B_338))))
      | ~ v1_funct_2(C_337,k2_struct_0('#skF_1'),u1_struct_0(B_338))
      | ~ v1_funct_1(C_337)
      | ~ l1_pre_topc(B_338) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_68,c_606])).

tff(c_2638,plain,(
    ! [C_337] :
      ( v2_funct_1(C_337)
      | ~ v3_tops_2(C_337,'#skF_1','#skF_2')
      | ~ m1_subset_1(C_337,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_337,k2_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_337)
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_67,c_2628])).

tff(c_2644,plain,(
    ! [C_339] :
      ( v2_funct_1(C_339)
      | ~ v3_tops_2(C_339,'#skF_1','#skF_2')
      | ~ m1_subset_1(C_339,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_339,k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_339) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_67,c_2638])).

tff(c_2647,plain,
    ( v2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v3_tops_2(k2_funct_1(k2_funct_1('#skF_3')),'#skF_1','#skF_2')
    | ~ v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')),k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_2454,c_2644])).

tff(c_2657,plain,
    ( v2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v3_tops_2(k2_funct_1(k2_funct_1('#skF_3')),'#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2445,c_2444,c_2647])).

tff(c_2662,plain,(
    ~ v3_tops_2(k2_funct_1(k2_funct_1('#skF_3')),'#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_2657])).

tff(c_2665,plain,
    ( ~ v3_tops_2('#skF_3','#skF_1','#skF_2')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_2662])).

tff(c_2668,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_46,c_598,c_40,c_2665])).

tff(c_2670,plain,(
    v3_tops_2(k2_funct_1(k2_funct_1('#skF_3')),'#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_2657])).

tff(c_667,plain,(
    ! [C_119,A_120,B_121] :
      ( v5_pre_topc(C_119,A_120,B_121)
      | ~ v3_tops_2(C_119,A_120,B_121)
      | ~ m1_subset_1(C_119,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_120),u1_struct_0(B_121))))
      | ~ v1_funct_2(C_119,u1_struct_0(A_120),u1_struct_0(B_121))
      | ~ v1_funct_1(C_119)
      | ~ l1_pre_topc(B_121)
      | ~ l1_pre_topc(A_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_683,plain,(
    ! [C_119,A_120] :
      ( v5_pre_topc(C_119,A_120,'#skF_2')
      | ~ v3_tops_2(C_119,A_120,'#skF_2')
      | ~ m1_subset_1(C_119,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_120),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_119,u1_struct_0(A_120),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_119)
      | ~ l1_pre_topc('#skF_2')
      | ~ l1_pre_topc(A_120) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_67,c_667])).

tff(c_2774,plain,(
    ! [C_352,A_353] :
      ( v5_pre_topc(C_352,A_353,'#skF_2')
      | ~ v3_tops_2(C_352,A_353,'#skF_2')
      | ~ m1_subset_1(C_352,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_353),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_352,u1_struct_0(A_353),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_352)
      | ~ l1_pre_topc(A_353) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_67,c_683])).

tff(c_2781,plain,(
    ! [C_352] :
      ( v5_pre_topc(C_352,'#skF_1','#skF_2')
      | ~ v3_tops_2(C_352,'#skF_1','#skF_2')
      | ~ m1_subset_1(C_352,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_352,u1_struct_0('#skF_1'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_352)
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_2774])).

tff(c_2790,plain,(
    ! [C_354] :
      ( v5_pre_topc(C_354,'#skF_1','#skF_2')
      | ~ v3_tops_2(C_354,'#skF_1','#skF_2')
      | ~ m1_subset_1(C_354,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_354,k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_354) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_68,c_2781])).

tff(c_2793,plain,
    ( v5_pre_topc(k2_funct_1(k2_funct_1('#skF_3')),'#skF_1','#skF_2')
    | ~ v3_tops_2(k2_funct_1(k2_funct_1('#skF_3')),'#skF_1','#skF_2')
    | ~ v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')),k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_2454,c_2790])).

tff(c_2803,plain,(
    v5_pre_topc(k2_funct_1(k2_funct_1('#skF_3')),'#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2445,c_2444,c_2670,c_2793])).

tff(c_3232,plain,(
    ! [C_382,A_383,B_384] :
      ( v3_tops_2(C_382,A_383,B_384)
      | ~ v5_pre_topc(k2_tops_2(u1_struct_0(A_383),u1_struct_0(B_384),C_382),B_384,A_383)
      | ~ v5_pre_topc(C_382,A_383,B_384)
      | ~ v2_funct_1(C_382)
      | k2_relset_1(u1_struct_0(A_383),u1_struct_0(B_384),C_382) != k2_struct_0(B_384)
      | k1_relset_1(u1_struct_0(A_383),u1_struct_0(B_384),C_382) != k2_struct_0(A_383)
      | ~ m1_subset_1(C_382,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_383),u1_struct_0(B_384))))
      | ~ v1_funct_2(C_382,u1_struct_0(A_383),u1_struct_0(B_384))
      | ~ v1_funct_1(C_382)
      | ~ l1_pre_topc(B_384)
      | ~ l1_pre_topc(A_383) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_3238,plain,(
    ! [C_382,B_384] :
      ( v3_tops_2(C_382,'#skF_2',B_384)
      | ~ v5_pre_topc(k2_tops_2(k2_struct_0('#skF_2'),u1_struct_0(B_384),C_382),B_384,'#skF_2')
      | ~ v5_pre_topc(C_382,'#skF_2',B_384)
      | ~ v2_funct_1(C_382)
      | k2_relset_1(u1_struct_0('#skF_2'),u1_struct_0(B_384),C_382) != k2_struct_0(B_384)
      | k1_relset_1(u1_struct_0('#skF_2'),u1_struct_0(B_384),C_382) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_382,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0(B_384))))
      | ~ v1_funct_2(C_382,u1_struct_0('#skF_2'),u1_struct_0(B_384))
      | ~ v1_funct_1(C_382)
      | ~ l1_pre_topc(B_384)
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_67,c_3232])).

tff(c_4398,plain,(
    ! [C_492,B_493] :
      ( v3_tops_2(C_492,'#skF_2',B_493)
      | ~ v5_pre_topc(k2_tops_2(k2_struct_0('#skF_2'),u1_struct_0(B_493),C_492),B_493,'#skF_2')
      | ~ v5_pre_topc(C_492,'#skF_2',B_493)
      | ~ v2_funct_1(C_492)
      | k2_relset_1(k2_struct_0('#skF_2'),u1_struct_0(B_493),C_492) != k2_struct_0(B_493)
      | k1_relset_1(k2_struct_0('#skF_2'),u1_struct_0(B_493),C_492) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_492,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),u1_struct_0(B_493))))
      | ~ v1_funct_2(C_492,k2_struct_0('#skF_2'),u1_struct_0(B_493))
      | ~ v1_funct_1(C_492)
      | ~ l1_pre_topc(B_493) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_67,c_67,c_67,c_67,c_3238])).

tff(c_4400,plain,(
    ! [C_492] :
      ( v3_tops_2(C_492,'#skF_2','#skF_1')
      | ~ v5_pre_topc(k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),C_492),'#skF_1','#skF_2')
      | ~ v5_pre_topc(C_492,'#skF_2','#skF_1')
      | ~ v2_funct_1(C_492)
      | k2_relset_1(k2_struct_0('#skF_2'),u1_struct_0('#skF_1'),C_492) != k2_struct_0('#skF_1')
      | k1_relset_1(k2_struct_0('#skF_2'),u1_struct_0('#skF_1'),C_492) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_492,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),u1_struct_0('#skF_1'))))
      | ~ v1_funct_2(C_492,k2_struct_0('#skF_2'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1(C_492)
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_4398])).

tff(c_4407,plain,(
    ! [C_494] :
      ( v3_tops_2(C_494,'#skF_2','#skF_1')
      | ~ v5_pre_topc(k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),C_494),'#skF_1','#skF_2')
      | ~ v5_pre_topc(C_494,'#skF_2','#skF_1')
      | ~ v2_funct_1(C_494)
      | k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),C_494) != k2_struct_0('#skF_1')
      | k1_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),C_494) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_494,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'))))
      | ~ v1_funct_2(C_494,k2_struct_0('#skF_2'),k2_struct_0('#skF_1'))
      | ~ v1_funct_1(C_494) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_68,c_68,c_68,c_68,c_4400])).

tff(c_4410,plain,
    ( v3_tops_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ v5_pre_topc(k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')),'#skF_1','#skF_2')
    | ~ v5_pre_topc(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) != k2_struct_0('#skF_1')
    | k1_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) != k2_struct_0('#skF_2')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),k2_struct_0('#skF_2'),k2_struct_0('#skF_1'))
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_636,c_4407])).

tff(c_4417,plain,(
    v3_tops_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_627,c_626,c_3757,c_1614,c_2443,c_3411,c_2803,c_2442,c_4410])).

tff(c_4419,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_628,c_4417])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:29:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.83/2.43  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.83/2.46  
% 6.83/2.46  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.83/2.46  %$ v5_pre_topc > v3_tops_2 > v1_funct_2 > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_relat_1 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k2_tops_2 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k2_struct_0 > k2_funct_1 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 6.83/2.46  
% 6.83/2.46  %Foreground sorts:
% 6.83/2.46  
% 6.83/2.46  
% 6.83/2.46  %Background operators:
% 6.83/2.46  
% 6.83/2.46  
% 6.83/2.46  %Foreground operators:
% 6.83/2.46  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 6.83/2.46  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 6.83/2.46  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.83/2.46  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 6.83/2.46  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 6.83/2.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.83/2.46  tff(v3_tops_2, type, v3_tops_2: ($i * $i * $i) > $o).
% 6.83/2.46  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 6.83/2.46  tff(k2_tops_2, type, k2_tops_2: ($i * $i * $i) > $i).
% 6.83/2.46  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.83/2.46  tff('#skF_2', type, '#skF_2': $i).
% 6.83/2.46  tff('#skF_3', type, '#skF_3': $i).
% 6.83/2.46  tff('#skF_1', type, '#skF_1': $i).
% 6.83/2.46  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 6.83/2.46  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.83/2.47  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 6.83/2.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.83/2.47  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.83/2.47  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.83/2.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.83/2.47  tff(v5_pre_topc, type, v5_pre_topc: ($i * $i * $i) > $o).
% 6.83/2.47  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 6.83/2.47  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 6.83/2.47  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.83/2.47  
% 7.16/2.52  tff(f_159, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: ((~v2_struct_0(B) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (v3_tops_2(C, A, B) => v3_tops_2(k2_tops_2(u1_struct_0(A), u1_struct_0(B), C), B, A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_tops_2)).
% 7.16/2.52  tff(f_50, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 7.16/2.52  tff(f_46, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 7.16/2.52  tff(f_62, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => (k2_tops_2(A, B, C) = k2_funct_1(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tops_2)).
% 7.16/2.52  tff(f_86, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (v3_tops_2(C, A, B) <=> (((((k1_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(A)) & (k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B))) & v2_funct_1(C)) & v5_pre_topc(C, A, B)) & v5_pre_topc(k2_tops_2(u1_struct_0(A), u1_struct_0(B), C), B, A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_tops_2)).
% 7.16/2.52  tff(f_98, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v1_funct_1(k2_tops_2(A, B, C)) & v1_funct_2(k2_tops_2(A, B, C), B, A)) & m1_subset_1(k2_tops_2(A, B, C), k1_zfmisc_1(k2_zfmisc_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_tops_2)).
% 7.16/2.52  tff(f_139, axiom, (![A]: (l1_struct_0(A) => (![B]: (l1_struct_0(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B)) & v2_funct_1(C)) => v2_funct_1(k2_tops_2(u1_struct_0(A), u1_struct_0(B), C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_tops_2)).
% 7.16/2.52  tff(f_121, axiom, (![A]: (l1_struct_0(A) => (![B]: ((~v2_struct_0(B) & l1_struct_0(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B)) & v2_funct_1(C)) => ((k1_relset_1(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)) = k2_struct_0(B)) & (k2_relset_1(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)) = k2_struct_0(A)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_tops_2)).
% 7.16/2.52  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 7.16/2.52  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 7.16/2.52  tff(f_42, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(k2_funct_1(A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_funct_1)).
% 7.16/2.52  tff(c_46, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_159])).
% 7.16/2.52  tff(c_52, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_159])).
% 7.16/2.52  tff(c_10, plain, (![A_8]: (l1_struct_0(A_8) | ~l1_pre_topc(A_8))), inference(cnfTransformation, [status(thm)], [f_50])).
% 7.16/2.52  tff(c_55, plain, (![A_43]: (u1_struct_0(A_43)=k2_struct_0(A_43) | ~l1_struct_0(A_43))), inference(cnfTransformation, [status(thm)], [f_46])).
% 7.16/2.52  tff(c_60, plain, (![A_44]: (u1_struct_0(A_44)=k2_struct_0(A_44) | ~l1_pre_topc(A_44))), inference(resolution, [status(thm)], [c_10, c_55])).
% 7.16/2.52  tff(c_68, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_52, c_60])).
% 7.16/2.52  tff(c_48, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_159])).
% 7.16/2.52  tff(c_67, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_48, c_60])).
% 7.16/2.52  tff(c_44, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_159])).
% 7.16/2.52  tff(c_70, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_67, c_44])).
% 7.16/2.52  tff(c_79, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_70])).
% 7.16/2.52  tff(c_42, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_159])).
% 7.16/2.52  tff(c_69, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_67, c_42])).
% 7.16/2.52  tff(c_82, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_69])).
% 7.16/2.52  tff(c_144, plain, (![A_60, B_61, C_62]: (k2_tops_2(A_60, B_61, C_62)=k2_funct_1(C_62) | ~v2_funct_1(C_62) | k2_relset_1(A_60, B_61, C_62)!=B_61 | ~m1_subset_1(C_62, k1_zfmisc_1(k2_zfmisc_1(A_60, B_61))) | ~v1_funct_2(C_62, A_60, B_61) | ~v1_funct_1(C_62))), inference(cnfTransformation, [status(thm)], [f_62])).
% 7.16/2.52  tff(c_150, plain, (k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_82, c_144])).
% 7.16/2.52  tff(c_154, plain, (k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_79, c_150])).
% 7.16/2.52  tff(c_155, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_154])).
% 7.16/2.52  tff(c_40, plain, (v3_tops_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_159])).
% 7.16/2.52  tff(c_352, plain, (![A_87, B_88, C_89]: (k2_relset_1(u1_struct_0(A_87), u1_struct_0(B_88), C_89)=k2_struct_0(B_88) | ~v3_tops_2(C_89, A_87, B_88) | ~m1_subset_1(C_89, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_87), u1_struct_0(B_88)))) | ~v1_funct_2(C_89, u1_struct_0(A_87), u1_struct_0(B_88)) | ~v1_funct_1(C_89) | ~l1_pre_topc(B_88) | ~l1_pre_topc(A_87))), inference(cnfTransformation, [status(thm)], [f_86])).
% 7.16/2.52  tff(c_359, plain, (![B_88, C_89]: (k2_relset_1(u1_struct_0('#skF_1'), u1_struct_0(B_88), C_89)=k2_struct_0(B_88) | ~v3_tops_2(C_89, '#skF_1', B_88) | ~m1_subset_1(C_89, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), u1_struct_0(B_88)))) | ~v1_funct_2(C_89, u1_struct_0('#skF_1'), u1_struct_0(B_88)) | ~v1_funct_1(C_89) | ~l1_pre_topc(B_88) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_68, c_352])).
% 7.16/2.52  tff(c_498, plain, (![B_106, C_107]: (k2_relset_1(k2_struct_0('#skF_1'), u1_struct_0(B_106), C_107)=k2_struct_0(B_106) | ~v3_tops_2(C_107, '#skF_1', B_106) | ~m1_subset_1(C_107, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), u1_struct_0(B_106)))) | ~v1_funct_2(C_107, k2_struct_0('#skF_1'), u1_struct_0(B_106)) | ~v1_funct_1(C_107) | ~l1_pre_topc(B_106))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_68, c_68, c_359])).
% 7.16/2.52  tff(c_508, plain, (![C_107]: (k2_relset_1(k2_struct_0('#skF_1'), u1_struct_0('#skF_2'), C_107)=k2_struct_0('#skF_2') | ~v3_tops_2(C_107, '#skF_1', '#skF_2') | ~m1_subset_1(C_107, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_107, k2_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1(C_107) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_67, c_498])).
% 7.16/2.52  tff(c_514, plain, (![C_108]: (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_108)=k2_struct_0('#skF_2') | ~v3_tops_2(C_108, '#skF_1', '#skF_2') | ~m1_subset_1(C_108, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_108, k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1(C_108))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_67, c_67, c_508])).
% 7.16/2.52  tff(c_521, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2') | ~v3_tops_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_82, c_514])).
% 7.16/2.52  tff(c_525, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_79, c_40, c_521])).
% 7.16/2.52  tff(c_527, plain, $false, inference(negUnitSimplification, [status(thm)], [c_155, c_525])).
% 7.16/2.52  tff(c_528, plain, (~v2_funct_1('#skF_3') | k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_funct_1('#skF_3')), inference(splitRight, [status(thm)], [c_154])).
% 7.16/2.52  tff(c_534, plain, (~v2_funct_1('#skF_3')), inference(splitLeft, [status(thm)], [c_528])).
% 7.16/2.52  tff(c_535, plain, (![C_109, A_110, B_111]: (v2_funct_1(C_109) | ~v3_tops_2(C_109, A_110, B_111) | ~m1_subset_1(C_109, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_110), u1_struct_0(B_111)))) | ~v1_funct_2(C_109, u1_struct_0(A_110), u1_struct_0(B_111)) | ~v1_funct_1(C_109) | ~l1_pre_topc(B_111) | ~l1_pre_topc(A_110))), inference(cnfTransformation, [status(thm)], [f_86])).
% 7.16/2.52  tff(c_542, plain, (![C_109, B_111]: (v2_funct_1(C_109) | ~v3_tops_2(C_109, '#skF_1', B_111) | ~m1_subset_1(C_109, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), u1_struct_0(B_111)))) | ~v1_funct_2(C_109, u1_struct_0('#skF_1'), u1_struct_0(B_111)) | ~v1_funct_1(C_109) | ~l1_pre_topc(B_111) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_68, c_535])).
% 7.16/2.52  tff(c_561, plain, (![C_112, B_113]: (v2_funct_1(C_112) | ~v3_tops_2(C_112, '#skF_1', B_113) | ~m1_subset_1(C_112, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), u1_struct_0(B_113)))) | ~v1_funct_2(C_112, k2_struct_0('#skF_1'), u1_struct_0(B_113)) | ~v1_funct_1(C_112) | ~l1_pre_topc(B_113))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_68, c_542])).
% 7.16/2.52  tff(c_571, plain, (![C_112]: (v2_funct_1(C_112) | ~v3_tops_2(C_112, '#skF_1', '#skF_2') | ~m1_subset_1(C_112, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_112, k2_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1(C_112) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_67, c_561])).
% 7.16/2.52  tff(c_583, plain, (![C_115]: (v2_funct_1(C_115) | ~v3_tops_2(C_115, '#skF_1', '#skF_2') | ~m1_subset_1(C_115, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_115, k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1(C_115))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_67, c_571])).
% 7.16/2.52  tff(c_590, plain, (v2_funct_1('#skF_3') | ~v3_tops_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_82, c_583])).
% 7.16/2.52  tff(c_594, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_79, c_40, c_590])).
% 7.16/2.52  tff(c_596, plain, $false, inference(negUnitSimplification, [status(thm)], [c_534, c_594])).
% 7.16/2.52  tff(c_597, plain, (k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_funct_1('#skF_3')), inference(splitRight, [status(thm)], [c_528])).
% 7.16/2.52  tff(c_38, plain, (~v3_tops_2(k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'), '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_159])).
% 7.16/2.52  tff(c_81, plain, (~v3_tops_2(k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'), '#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_67, c_38])).
% 7.16/2.52  tff(c_628, plain, (~v3_tops_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_597, c_81])).
% 7.16/2.52  tff(c_106, plain, (![A_48, B_49, C_50]: (v1_funct_1(k2_tops_2(A_48, B_49, C_50)) | ~m1_subset_1(C_50, k1_zfmisc_1(k2_zfmisc_1(A_48, B_49))) | ~v1_funct_2(C_50, A_48, B_49) | ~v1_funct_1(C_50))), inference(cnfTransformation, [status(thm)], [f_98])).
% 7.16/2.52  tff(c_109, plain, (v1_funct_1(k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_82, c_106])).
% 7.16/2.52  tff(c_112, plain, (v1_funct_1(k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_79, c_109])).
% 7.16/2.52  tff(c_627, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_597, c_112])).
% 7.16/2.52  tff(c_113, plain, (![A_51, B_52, C_53]: (v1_funct_2(k2_tops_2(A_51, B_52, C_53), B_52, A_51) | ~m1_subset_1(C_53, k1_zfmisc_1(k2_zfmisc_1(A_51, B_52))) | ~v1_funct_2(C_53, A_51, B_52) | ~v1_funct_1(C_53))), inference(cnfTransformation, [status(thm)], [f_98])).
% 7.16/2.52  tff(c_115, plain, (v1_funct_2(k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'), k2_struct_0('#skF_2'), k2_struct_0('#skF_1')) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_82, c_113])).
% 7.16/2.52  tff(c_118, plain, (v1_funct_2(k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'), k2_struct_0('#skF_2'), k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_79, c_115])).
% 7.16/2.52  tff(c_626, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_struct_0('#skF_2'), k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_597, c_118])).
% 7.16/2.52  tff(c_529, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_154])).
% 7.16/2.52  tff(c_598, plain, (v2_funct_1('#skF_3')), inference(splitRight, [status(thm)], [c_528])).
% 7.16/2.52  tff(c_2813, plain, (![A_355, B_356, C_357]: (v2_funct_1(k2_tops_2(u1_struct_0(A_355), u1_struct_0(B_356), C_357)) | ~v2_funct_1(C_357) | k2_relset_1(u1_struct_0(A_355), u1_struct_0(B_356), C_357)!=k2_struct_0(B_356) | ~m1_subset_1(C_357, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_355), u1_struct_0(B_356)))) | ~v1_funct_2(C_357, u1_struct_0(A_355), u1_struct_0(B_356)) | ~v1_funct_1(C_357) | ~l1_struct_0(B_356) | ~l1_struct_0(A_355))), inference(cnfTransformation, [status(thm)], [f_139])).
% 7.16/2.52  tff(c_2823, plain, (![A_355, C_357]: (v2_funct_1(k2_tops_2(u1_struct_0(A_355), u1_struct_0('#skF_1'), C_357)) | ~v2_funct_1(C_357) | k2_relset_1(u1_struct_0(A_355), u1_struct_0('#skF_1'), C_357)!=k2_struct_0('#skF_1') | ~m1_subset_1(C_357, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_355), k2_struct_0('#skF_1')))) | ~v1_funct_2(C_357, u1_struct_0(A_355), u1_struct_0('#skF_1')) | ~v1_funct_1(C_357) | ~l1_struct_0('#skF_1') | ~l1_struct_0(A_355))), inference(superposition, [status(thm), theory('equality')], [c_68, c_2813])).
% 7.16/2.52  tff(c_2832, plain, (![A_355, C_357]: (v2_funct_1(k2_tops_2(u1_struct_0(A_355), k2_struct_0('#skF_1'), C_357)) | ~v2_funct_1(C_357) | k2_relset_1(u1_struct_0(A_355), k2_struct_0('#skF_1'), C_357)!=k2_struct_0('#skF_1') | ~m1_subset_1(C_357, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_355), k2_struct_0('#skF_1')))) | ~v1_funct_2(C_357, u1_struct_0(A_355), k2_struct_0('#skF_1')) | ~v1_funct_1(C_357) | ~l1_struct_0('#skF_1') | ~l1_struct_0(A_355))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_68, c_68, c_2823])).
% 7.16/2.52  tff(c_3509, plain, (~l1_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_2832])).
% 7.16/2.52  tff(c_3512, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_10, c_3509])).
% 7.16/2.52  tff(c_3516, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_3512])).
% 7.16/2.52  tff(c_3518, plain, (l1_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_2832])).
% 7.16/2.52  tff(c_50, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_159])).
% 7.16/2.52  tff(c_2957, plain, (![B_362, A_363, C_364]: (k1_relset_1(u1_struct_0(B_362), u1_struct_0(A_363), k2_tops_2(u1_struct_0(A_363), u1_struct_0(B_362), C_364))=k2_struct_0(B_362) | ~v2_funct_1(C_364) | k2_relset_1(u1_struct_0(A_363), u1_struct_0(B_362), C_364)!=k2_struct_0(B_362) | ~m1_subset_1(C_364, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_363), u1_struct_0(B_362)))) | ~v1_funct_2(C_364, u1_struct_0(A_363), u1_struct_0(B_362)) | ~v1_funct_1(C_364) | ~l1_struct_0(B_362) | v2_struct_0(B_362) | ~l1_struct_0(A_363))), inference(cnfTransformation, [status(thm)], [f_121])).
% 7.16/2.52  tff(c_2978, plain, (![A_363, C_364]: (k1_relset_1(k2_struct_0('#skF_2'), u1_struct_0(A_363), k2_tops_2(u1_struct_0(A_363), u1_struct_0('#skF_2'), C_364))=k2_struct_0('#skF_2') | ~v2_funct_1(C_364) | k2_relset_1(u1_struct_0(A_363), u1_struct_0('#skF_2'), C_364)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_364, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_363), u1_struct_0('#skF_2')))) | ~v1_funct_2(C_364, u1_struct_0(A_363), u1_struct_0('#skF_2')) | ~v1_funct_1(C_364) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2') | ~l1_struct_0(A_363))), inference(superposition, [status(thm), theory('equality')], [c_67, c_2957])).
% 7.16/2.52  tff(c_2994, plain, (![A_363, C_364]: (k1_relset_1(k2_struct_0('#skF_2'), u1_struct_0(A_363), k2_tops_2(u1_struct_0(A_363), k2_struct_0('#skF_2'), C_364))=k2_struct_0('#skF_2') | ~v2_funct_1(C_364) | k2_relset_1(u1_struct_0(A_363), k2_struct_0('#skF_2'), C_364)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_364, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_363), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_364, u1_struct_0(A_363), k2_struct_0('#skF_2')) | ~v1_funct_1(C_364) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2') | ~l1_struct_0(A_363))), inference(demodulation, [status(thm), theory('equality')], [c_67, c_67, c_67, c_67, c_2978])).
% 7.16/2.52  tff(c_2995, plain, (![A_363, C_364]: (k1_relset_1(k2_struct_0('#skF_2'), u1_struct_0(A_363), k2_tops_2(u1_struct_0(A_363), k2_struct_0('#skF_2'), C_364))=k2_struct_0('#skF_2') | ~v2_funct_1(C_364) | k2_relset_1(u1_struct_0(A_363), k2_struct_0('#skF_2'), C_364)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_364, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_363), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_364, u1_struct_0(A_363), k2_struct_0('#skF_2')) | ~v1_funct_1(C_364) | ~l1_struct_0('#skF_2') | ~l1_struct_0(A_363))), inference(negUnitSimplification, [status(thm)], [c_50, c_2994])).
% 7.16/2.52  tff(c_3016, plain, (~l1_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_2995])).
% 7.16/2.52  tff(c_3019, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_10, c_3016])).
% 7.16/2.52  tff(c_3023, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_3019])).
% 7.16/2.52  tff(c_3025, plain, (l1_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_2995])).
% 7.16/2.52  tff(c_2987, plain, (![A_363, C_364]: (k1_relset_1(u1_struct_0('#skF_2'), u1_struct_0(A_363), k2_tops_2(u1_struct_0(A_363), k2_struct_0('#skF_2'), C_364))=k2_struct_0('#skF_2') | ~v2_funct_1(C_364) | k2_relset_1(u1_struct_0(A_363), u1_struct_0('#skF_2'), C_364)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_364, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_363), u1_struct_0('#skF_2')))) | ~v1_funct_2(C_364, u1_struct_0(A_363), u1_struct_0('#skF_2')) | ~v1_funct_1(C_364) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2') | ~l1_struct_0(A_363))), inference(superposition, [status(thm), theory('equality')], [c_67, c_2957])).
% 7.16/2.52  tff(c_2998, plain, (![A_363, C_364]: (k1_relset_1(k2_struct_0('#skF_2'), u1_struct_0(A_363), k2_tops_2(u1_struct_0(A_363), k2_struct_0('#skF_2'), C_364))=k2_struct_0('#skF_2') | ~v2_funct_1(C_364) | k2_relset_1(u1_struct_0(A_363), k2_struct_0('#skF_2'), C_364)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_364, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_363), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_364, u1_struct_0(A_363), k2_struct_0('#skF_2')) | ~v1_funct_1(C_364) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2') | ~l1_struct_0(A_363))), inference(demodulation, [status(thm), theory('equality')], [c_67, c_67, c_67, c_67, c_2987])).
% 7.16/2.52  tff(c_2999, plain, (![A_363, C_364]: (k1_relset_1(k2_struct_0('#skF_2'), u1_struct_0(A_363), k2_tops_2(u1_struct_0(A_363), k2_struct_0('#skF_2'), C_364))=k2_struct_0('#skF_2') | ~v2_funct_1(C_364) | k2_relset_1(u1_struct_0(A_363), k2_struct_0('#skF_2'), C_364)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_364, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_363), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_364, u1_struct_0(A_363), k2_struct_0('#skF_2')) | ~v1_funct_1(C_364) | ~l1_struct_0('#skF_2') | ~l1_struct_0(A_363))), inference(negUnitSimplification, [status(thm)], [c_50, c_2998])).
% 7.16/2.52  tff(c_3414, plain, (![A_405, C_406]: (k1_relset_1(k2_struct_0('#skF_2'), u1_struct_0(A_405), k2_tops_2(u1_struct_0(A_405), k2_struct_0('#skF_2'), C_406))=k2_struct_0('#skF_2') | ~v2_funct_1(C_406) | k2_relset_1(u1_struct_0(A_405), k2_struct_0('#skF_2'), C_406)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_406, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_405), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_406, u1_struct_0(A_405), k2_struct_0('#skF_2')) | ~v1_funct_1(C_406) | ~l1_struct_0(A_405))), inference(demodulation, [status(thm), theory('equality')], [c_3025, c_2999])).
% 7.16/2.52  tff(c_3426, plain, (![C_406]: (k1_relset_1(k2_struct_0('#skF_2'), u1_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_406))=k2_struct_0('#skF_2') | ~v2_funct_1(C_406) | k2_relset_1(u1_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_406)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_406, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_406, u1_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1(C_406) | ~l1_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_68, c_3414])).
% 7.16/2.52  tff(c_3436, plain, (![C_406]: (k1_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_406))=k2_struct_0('#skF_2') | ~v2_funct_1(C_406) | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_406)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_406, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_406, k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1(C_406) | ~l1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_68, c_68, c_68, c_3426])).
% 7.16/2.52  tff(c_3739, plain, (![C_439]: (k1_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_439))=k2_struct_0('#skF_2') | ~v2_funct_1(C_439) | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_439)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_439, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_439, k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1(C_439))), inference(demodulation, [status(thm), theory('equality')], [c_3518, c_3436])).
% 7.16/2.52  tff(c_3751, plain, (k1_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))=k2_struct_0('#skF_2') | ~v2_funct_1('#skF_3') | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_597, c_3739])).
% 7.16/2.52  tff(c_3757, plain, (k1_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_79, c_82, c_529, c_598, c_3751])).
% 7.16/2.52  tff(c_26, plain, (![A_19, B_20, C_21]: (m1_subset_1(k2_tops_2(A_19, B_20, C_21), k1_zfmisc_1(k2_zfmisc_1(B_20, A_19))) | ~m1_subset_1(C_21, k1_zfmisc_1(k2_zfmisc_1(A_19, B_20))) | ~v1_funct_2(C_21, A_19, B_20) | ~v1_funct_1(C_21))), inference(cnfTransformation, [status(thm)], [f_98])).
% 7.16/2.52  tff(c_632, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1')))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_597, c_26])).
% 7.16/2.52  tff(c_636, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_79, c_82, c_632])).
% 7.16/2.52  tff(c_12, plain, (![A_9, B_10, C_11]: (k2_tops_2(A_9, B_10, C_11)=k2_funct_1(C_11) | ~v2_funct_1(C_11) | k2_relset_1(A_9, B_10, C_11)!=B_10 | ~m1_subset_1(C_11, k1_zfmisc_1(k2_zfmisc_1(A_9, B_10))) | ~v1_funct_2(C_11, A_9, B_10) | ~v1_funct_1(C_11))), inference(cnfTransformation, [status(thm)], [f_62])).
% 7.16/2.52  tff(c_640, plain, (k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3')) | ~v2_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))!=k2_struct_0('#skF_1') | ~v1_funct_2(k2_funct_1('#skF_3'), k2_struct_0('#skF_2'), k2_struct_0('#skF_1')) | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_636, c_12])).
% 7.16/2.52  tff(c_654, plain, (k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3')) | ~v2_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))!=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_627, c_626, c_640])).
% 7.16/2.52  tff(c_693, plain, (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))!=k2_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_654])).
% 7.16/2.52  tff(c_1156, plain, (![A_177, B_178, C_179]: (v2_funct_1(k2_tops_2(u1_struct_0(A_177), u1_struct_0(B_178), C_179)) | ~v2_funct_1(C_179) | k2_relset_1(u1_struct_0(A_177), u1_struct_0(B_178), C_179)!=k2_struct_0(B_178) | ~m1_subset_1(C_179, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_177), u1_struct_0(B_178)))) | ~v1_funct_2(C_179, u1_struct_0(A_177), u1_struct_0(B_178)) | ~v1_funct_1(C_179) | ~l1_struct_0(B_178) | ~l1_struct_0(A_177))), inference(cnfTransformation, [status(thm)], [f_139])).
% 7.16/2.52  tff(c_1166, plain, (![A_177, C_179]: (v2_funct_1(k2_tops_2(u1_struct_0(A_177), u1_struct_0('#skF_1'), C_179)) | ~v2_funct_1(C_179) | k2_relset_1(u1_struct_0(A_177), u1_struct_0('#skF_1'), C_179)!=k2_struct_0('#skF_1') | ~m1_subset_1(C_179, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_177), k2_struct_0('#skF_1')))) | ~v1_funct_2(C_179, u1_struct_0(A_177), u1_struct_0('#skF_1')) | ~v1_funct_1(C_179) | ~l1_struct_0('#skF_1') | ~l1_struct_0(A_177))), inference(superposition, [status(thm), theory('equality')], [c_68, c_1156])).
% 7.16/2.52  tff(c_1175, plain, (![A_177, C_179]: (v2_funct_1(k2_tops_2(u1_struct_0(A_177), k2_struct_0('#skF_1'), C_179)) | ~v2_funct_1(C_179) | k2_relset_1(u1_struct_0(A_177), k2_struct_0('#skF_1'), C_179)!=k2_struct_0('#skF_1') | ~m1_subset_1(C_179, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_177), k2_struct_0('#skF_1')))) | ~v1_funct_2(C_179, u1_struct_0(A_177), k2_struct_0('#skF_1')) | ~v1_funct_1(C_179) | ~l1_struct_0('#skF_1') | ~l1_struct_0(A_177))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_68, c_68, c_1166])).
% 7.16/2.52  tff(c_1421, plain, (~l1_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_1175])).
% 7.16/2.52  tff(c_1424, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_10, c_1421])).
% 7.16/2.52  tff(c_1428, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_1424])).
% 7.16/2.52  tff(c_1430, plain, (l1_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_1175])).
% 7.16/2.52  tff(c_1269, plain, (![B_192, A_193, C_194]: (k1_relset_1(u1_struct_0(B_192), u1_struct_0(A_193), k2_tops_2(u1_struct_0(A_193), u1_struct_0(B_192), C_194))=k2_struct_0(B_192) | ~v2_funct_1(C_194) | k2_relset_1(u1_struct_0(A_193), u1_struct_0(B_192), C_194)!=k2_struct_0(B_192) | ~m1_subset_1(C_194, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_193), u1_struct_0(B_192)))) | ~v1_funct_2(C_194, u1_struct_0(A_193), u1_struct_0(B_192)) | ~v1_funct_1(C_194) | ~l1_struct_0(B_192) | v2_struct_0(B_192) | ~l1_struct_0(A_193))), inference(cnfTransformation, [status(thm)], [f_121])).
% 7.16/2.52  tff(c_1299, plain, (![A_193, C_194]: (k1_relset_1(u1_struct_0('#skF_2'), u1_struct_0(A_193), k2_tops_2(u1_struct_0(A_193), k2_struct_0('#skF_2'), C_194))=k2_struct_0('#skF_2') | ~v2_funct_1(C_194) | k2_relset_1(u1_struct_0(A_193), u1_struct_0('#skF_2'), C_194)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_194, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_193), u1_struct_0('#skF_2')))) | ~v1_funct_2(C_194, u1_struct_0(A_193), u1_struct_0('#skF_2')) | ~v1_funct_1(C_194) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2') | ~l1_struct_0(A_193))), inference(superposition, [status(thm), theory('equality')], [c_67, c_1269])).
% 7.16/2.52  tff(c_1310, plain, (![A_193, C_194]: (k1_relset_1(k2_struct_0('#skF_2'), u1_struct_0(A_193), k2_tops_2(u1_struct_0(A_193), k2_struct_0('#skF_2'), C_194))=k2_struct_0('#skF_2') | ~v2_funct_1(C_194) | k2_relset_1(u1_struct_0(A_193), k2_struct_0('#skF_2'), C_194)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_194, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_193), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_194, u1_struct_0(A_193), k2_struct_0('#skF_2')) | ~v1_funct_1(C_194) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2') | ~l1_struct_0(A_193))), inference(demodulation, [status(thm), theory('equality')], [c_67, c_67, c_67, c_67, c_1299])).
% 7.16/2.52  tff(c_1311, plain, (![A_193, C_194]: (k1_relset_1(k2_struct_0('#skF_2'), u1_struct_0(A_193), k2_tops_2(u1_struct_0(A_193), k2_struct_0('#skF_2'), C_194))=k2_struct_0('#skF_2') | ~v2_funct_1(C_194) | k2_relset_1(u1_struct_0(A_193), k2_struct_0('#skF_2'), C_194)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_194, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_193), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_194, u1_struct_0(A_193), k2_struct_0('#skF_2')) | ~v1_funct_1(C_194) | ~l1_struct_0('#skF_2') | ~l1_struct_0(A_193))), inference(negUnitSimplification, [status(thm)], [c_50, c_1310])).
% 7.16/2.52  tff(c_1339, plain, (~l1_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_1311])).
% 7.16/2.52  tff(c_1342, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_10, c_1339])).
% 7.16/2.52  tff(c_1346, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_1342])).
% 7.16/2.52  tff(c_1348, plain, (l1_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_1311])).
% 7.16/2.52  tff(c_1374, plain, (![B_206, A_207, C_208]: (k2_relset_1(u1_struct_0(B_206), u1_struct_0(A_207), k2_tops_2(u1_struct_0(A_207), u1_struct_0(B_206), C_208))=k2_struct_0(A_207) | ~v2_funct_1(C_208) | k2_relset_1(u1_struct_0(A_207), u1_struct_0(B_206), C_208)!=k2_struct_0(B_206) | ~m1_subset_1(C_208, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_207), u1_struct_0(B_206)))) | ~v1_funct_2(C_208, u1_struct_0(A_207), u1_struct_0(B_206)) | ~v1_funct_1(C_208) | ~l1_struct_0(B_206) | v2_struct_0(B_206) | ~l1_struct_0(A_207))), inference(cnfTransformation, [status(thm)], [f_121])).
% 7.16/2.52  tff(c_1395, plain, (![A_207, C_208]: (k2_relset_1(k2_struct_0('#skF_2'), u1_struct_0(A_207), k2_tops_2(u1_struct_0(A_207), u1_struct_0('#skF_2'), C_208))=k2_struct_0(A_207) | ~v2_funct_1(C_208) | k2_relset_1(u1_struct_0(A_207), u1_struct_0('#skF_2'), C_208)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_208, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_207), u1_struct_0('#skF_2')))) | ~v1_funct_2(C_208, u1_struct_0(A_207), u1_struct_0('#skF_2')) | ~v1_funct_1(C_208) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2') | ~l1_struct_0(A_207))), inference(superposition, [status(thm), theory('equality')], [c_67, c_1374])).
% 7.16/2.52  tff(c_1412, plain, (![A_207, C_208]: (k2_relset_1(k2_struct_0('#skF_2'), u1_struct_0(A_207), k2_tops_2(u1_struct_0(A_207), k2_struct_0('#skF_2'), C_208))=k2_struct_0(A_207) | ~v2_funct_1(C_208) | k2_relset_1(u1_struct_0(A_207), k2_struct_0('#skF_2'), C_208)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_208, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_207), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_208, u1_struct_0(A_207), k2_struct_0('#skF_2')) | ~v1_funct_1(C_208) | v2_struct_0('#skF_2') | ~l1_struct_0(A_207))), inference(demodulation, [status(thm), theory('equality')], [c_1348, c_67, c_67, c_67, c_67, c_1395])).
% 7.16/2.52  tff(c_1436, plain, (![A_209, C_210]: (k2_relset_1(k2_struct_0('#skF_2'), u1_struct_0(A_209), k2_tops_2(u1_struct_0(A_209), k2_struct_0('#skF_2'), C_210))=k2_struct_0(A_209) | ~v2_funct_1(C_210) | k2_relset_1(u1_struct_0(A_209), k2_struct_0('#skF_2'), C_210)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_210, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_209), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_210, u1_struct_0(A_209), k2_struct_0('#skF_2')) | ~v1_funct_1(C_210) | ~l1_struct_0(A_209))), inference(negUnitSimplification, [status(thm)], [c_50, c_1412])).
% 7.16/2.52  tff(c_1445, plain, (![C_210]: (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_210))=k2_struct_0('#skF_1') | ~v2_funct_1(C_210) | k2_relset_1(u1_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_210)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_210, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_210, u1_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1(C_210) | ~l1_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_68, c_1436])).
% 7.16/2.52  tff(c_1597, plain, (![C_227]: (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_227))=k2_struct_0('#skF_1') | ~v2_funct_1(C_227) | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_227)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_227, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_227, k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1(C_227))), inference(demodulation, [status(thm), theory('equality')], [c_1430, c_68, c_68, c_68, c_68, c_1445])).
% 7.16/2.52  tff(c_1606, plain, (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))=k2_struct_0('#skF_1') | ~v2_funct_1('#skF_3') | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_597, c_1597])).
% 7.16/2.52  tff(c_1610, plain, (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_79, c_82, c_529, c_598, c_1606])).
% 7.16/2.52  tff(c_1612, plain, $false, inference(negUnitSimplification, [status(thm)], [c_693, c_1610])).
% 7.16/2.52  tff(c_1614, plain, (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))=k2_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_654])).
% 7.16/2.52  tff(c_1613, plain, (~v2_funct_1(k2_funct_1('#skF_3')) | k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_654])).
% 7.16/2.52  tff(c_1619, plain, (~v2_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_1613])).
% 7.16/2.52  tff(c_2133, plain, (![B_290, A_291, C_292]: (k2_relset_1(u1_struct_0(B_290), u1_struct_0(A_291), k2_tops_2(u1_struct_0(A_291), u1_struct_0(B_290), C_292))=k2_struct_0(A_291) | ~v2_funct_1(C_292) | k2_relset_1(u1_struct_0(A_291), u1_struct_0(B_290), C_292)!=k2_struct_0(B_290) | ~m1_subset_1(C_292, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_291), u1_struct_0(B_290)))) | ~v1_funct_2(C_292, u1_struct_0(A_291), u1_struct_0(B_290)) | ~v1_funct_1(C_292) | ~l1_struct_0(B_290) | v2_struct_0(B_290) | ~l1_struct_0(A_291))), inference(cnfTransformation, [status(thm)], [f_121])).
% 7.16/2.52  tff(c_2154, plain, (![A_291, C_292]: (k2_relset_1(k2_struct_0('#skF_2'), u1_struct_0(A_291), k2_tops_2(u1_struct_0(A_291), u1_struct_0('#skF_2'), C_292))=k2_struct_0(A_291) | ~v2_funct_1(C_292) | k2_relset_1(u1_struct_0(A_291), u1_struct_0('#skF_2'), C_292)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_292, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_291), u1_struct_0('#skF_2')))) | ~v1_funct_2(C_292, u1_struct_0(A_291), u1_struct_0('#skF_2')) | ~v1_funct_1(C_292) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2') | ~l1_struct_0(A_291))), inference(superposition, [status(thm), theory('equality')], [c_67, c_2133])).
% 7.16/2.52  tff(c_2170, plain, (![A_291, C_292]: (k2_relset_1(k2_struct_0('#skF_2'), u1_struct_0(A_291), k2_tops_2(u1_struct_0(A_291), k2_struct_0('#skF_2'), C_292))=k2_struct_0(A_291) | ~v2_funct_1(C_292) | k2_relset_1(u1_struct_0(A_291), k2_struct_0('#skF_2'), C_292)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_292, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_291), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_292, u1_struct_0(A_291), k2_struct_0('#skF_2')) | ~v1_funct_1(C_292) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2') | ~l1_struct_0(A_291))), inference(demodulation, [status(thm), theory('equality')], [c_67, c_67, c_67, c_67, c_2154])).
% 7.16/2.52  tff(c_2171, plain, (![A_291, C_292]: (k2_relset_1(k2_struct_0('#skF_2'), u1_struct_0(A_291), k2_tops_2(u1_struct_0(A_291), k2_struct_0('#skF_2'), C_292))=k2_struct_0(A_291) | ~v2_funct_1(C_292) | k2_relset_1(u1_struct_0(A_291), k2_struct_0('#skF_2'), C_292)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_292, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_291), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_292, u1_struct_0(A_291), k2_struct_0('#skF_2')) | ~v1_funct_1(C_292) | ~l1_struct_0('#skF_2') | ~l1_struct_0(A_291))), inference(negUnitSimplification, [status(thm)], [c_50, c_2170])).
% 7.16/2.52  tff(c_2194, plain, (~l1_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_2171])).
% 7.16/2.52  tff(c_2197, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_10, c_2194])).
% 7.16/2.52  tff(c_2201, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_2197])).
% 7.16/2.52  tff(c_2203, plain, (l1_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_2171])).
% 7.16/2.52  tff(c_1994, plain, (![A_272, B_273, C_274]: (v2_funct_1(k2_tops_2(u1_struct_0(A_272), u1_struct_0(B_273), C_274)) | ~v2_funct_1(C_274) | k2_relset_1(u1_struct_0(A_272), u1_struct_0(B_273), C_274)!=k2_struct_0(B_273) | ~m1_subset_1(C_274, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_272), u1_struct_0(B_273)))) | ~v1_funct_2(C_274, u1_struct_0(A_272), u1_struct_0(B_273)) | ~v1_funct_1(C_274) | ~l1_struct_0(B_273) | ~l1_struct_0(A_272))), inference(cnfTransformation, [status(thm)], [f_139])).
% 7.16/2.52  tff(c_2001, plain, (![B_273, C_274]: (v2_funct_1(k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0(B_273), C_274)) | ~v2_funct_1(C_274) | k2_relset_1(u1_struct_0('#skF_1'), u1_struct_0(B_273), C_274)!=k2_struct_0(B_273) | ~m1_subset_1(C_274, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), u1_struct_0(B_273)))) | ~v1_funct_2(C_274, u1_struct_0('#skF_1'), u1_struct_0(B_273)) | ~v1_funct_1(C_274) | ~l1_struct_0(B_273) | ~l1_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_68, c_1994])).
% 7.16/2.52  tff(c_2012, plain, (![B_273, C_274]: (v2_funct_1(k2_tops_2(k2_struct_0('#skF_1'), u1_struct_0(B_273), C_274)) | ~v2_funct_1(C_274) | k2_relset_1(k2_struct_0('#skF_1'), u1_struct_0(B_273), C_274)!=k2_struct_0(B_273) | ~m1_subset_1(C_274, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), u1_struct_0(B_273)))) | ~v1_funct_2(C_274, k2_struct_0('#skF_1'), u1_struct_0(B_273)) | ~v1_funct_1(C_274) | ~l1_struct_0(B_273) | ~l1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_68, c_68, c_2001])).
% 7.16/2.52  tff(c_2374, plain, (~l1_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_2012])).
% 7.16/2.52  tff(c_2394, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_10, c_2374])).
% 7.16/2.52  tff(c_2398, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_2394])).
% 7.16/2.52  tff(c_2406, plain, (![B_320, C_321]: (v2_funct_1(k2_tops_2(k2_struct_0('#skF_1'), u1_struct_0(B_320), C_321)) | ~v2_funct_1(C_321) | k2_relset_1(k2_struct_0('#skF_1'), u1_struct_0(B_320), C_321)!=k2_struct_0(B_320) | ~m1_subset_1(C_321, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), u1_struct_0(B_320)))) | ~v1_funct_2(C_321, k2_struct_0('#skF_1'), u1_struct_0(B_320)) | ~v1_funct_1(C_321) | ~l1_struct_0(B_320))), inference(splitRight, [status(thm)], [c_2012])).
% 7.16/2.52  tff(c_2416, plain, (![C_321]: (v2_funct_1(k2_tops_2(k2_struct_0('#skF_1'), u1_struct_0('#skF_2'), C_321)) | ~v2_funct_1(C_321) | k2_relset_1(k2_struct_0('#skF_1'), u1_struct_0('#skF_2'), C_321)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_321, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_321, k2_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1(C_321) | ~l1_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_67, c_2406])).
% 7.16/2.52  tff(c_2428, plain, (![C_323]: (v2_funct_1(k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_323)) | ~v2_funct_1(C_323) | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_323)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_323, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_323, k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1(C_323))), inference(demodulation, [status(thm), theory('equality')], [c_2203, c_67, c_67, c_67, c_2416])).
% 7.16/2.52  tff(c_2435, plain, (v2_funct_1(k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')) | ~v2_funct_1('#skF_3') | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_82, c_2428])).
% 7.16/2.52  tff(c_2439, plain, (v2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_79, c_529, c_598, c_597, c_2435])).
% 7.16/2.52  tff(c_2441, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1619, c_2439])).
% 7.16/2.52  tff(c_2443, plain, (v2_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_1613])).
% 7.16/2.52  tff(c_2697, plain, (![A_342, B_343, C_344]: (v5_pre_topc(k2_tops_2(u1_struct_0(A_342), u1_struct_0(B_343), C_344), B_343, A_342) | ~v3_tops_2(C_344, A_342, B_343) | ~m1_subset_1(C_344, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_342), u1_struct_0(B_343)))) | ~v1_funct_2(C_344, u1_struct_0(A_342), u1_struct_0(B_343)) | ~v1_funct_1(C_344) | ~l1_pre_topc(B_343) | ~l1_pre_topc(A_342))), inference(cnfTransformation, [status(thm)], [f_86])).
% 7.16/2.52  tff(c_2702, plain, (![B_343, C_344]: (v5_pre_topc(k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0(B_343), C_344), B_343, '#skF_1') | ~v3_tops_2(C_344, '#skF_1', B_343) | ~m1_subset_1(C_344, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), u1_struct_0(B_343)))) | ~v1_funct_2(C_344, u1_struct_0('#skF_1'), u1_struct_0(B_343)) | ~v1_funct_1(C_344) | ~l1_pre_topc(B_343) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_68, c_2697])).
% 7.16/2.52  tff(c_3381, plain, (![B_402, C_403]: (v5_pre_topc(k2_tops_2(k2_struct_0('#skF_1'), u1_struct_0(B_402), C_403), B_402, '#skF_1') | ~v3_tops_2(C_403, '#skF_1', B_402) | ~m1_subset_1(C_403, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), u1_struct_0(B_402)))) | ~v1_funct_2(C_403, k2_struct_0('#skF_1'), u1_struct_0(B_402)) | ~v1_funct_1(C_403) | ~l1_pre_topc(B_402))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_68, c_68, c_2702])).
% 7.16/2.52  tff(c_3388, plain, (![C_403]: (v5_pre_topc(k2_tops_2(k2_struct_0('#skF_1'), u1_struct_0('#skF_2'), C_403), '#skF_2', '#skF_1') | ~v3_tops_2(C_403, '#skF_1', '#skF_2') | ~m1_subset_1(C_403, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_403, k2_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1(C_403) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_67, c_3381])).
% 7.16/2.52  tff(c_3394, plain, (![C_404]: (v5_pre_topc(k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_404), '#skF_2', '#skF_1') | ~v3_tops_2(C_404, '#skF_1', '#skF_2') | ~m1_subset_1(C_404, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_404, k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1(C_404))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_67, c_67, c_3388])).
% 7.16/2.52  tff(c_3404, plain, (v5_pre_topc(k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'), '#skF_2', '#skF_1') | ~v3_tops_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_82, c_3394])).
% 7.16/2.52  tff(c_3411, plain, (v5_pre_topc(k2_funct_1('#skF_3'), '#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_79, c_40, c_597, c_3404])).
% 7.16/2.52  tff(c_2442, plain, (k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_1613])).
% 7.16/2.52  tff(c_30, plain, (![A_19, B_20, C_21]: (v1_funct_1(k2_tops_2(A_19, B_20, C_21)) | ~m1_subset_1(C_21, k1_zfmisc_1(k2_zfmisc_1(A_19, B_20))) | ~v1_funct_2(C_21, A_19, B_20) | ~v1_funct_1(C_21))), inference(cnfTransformation, [status(thm)], [f_98])).
% 7.16/2.52  tff(c_648, plain, (v1_funct_1(k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))) | ~v1_funct_2(k2_funct_1('#skF_3'), k2_struct_0('#skF_2'), k2_struct_0('#skF_1')) | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_636, c_30])).
% 7.16/2.52  tff(c_663, plain, (v1_funct_1(k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_627, c_626, c_648])).
% 7.16/2.52  tff(c_2445, plain, (v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_2442, c_663])).
% 7.16/2.52  tff(c_28, plain, (![A_19, B_20, C_21]: (v1_funct_2(k2_tops_2(A_19, B_20, C_21), B_20, A_19) | ~m1_subset_1(C_21, k1_zfmisc_1(k2_zfmisc_1(A_19, B_20))) | ~v1_funct_2(C_21, A_19, B_20) | ~v1_funct_1(C_21))), inference(cnfTransformation, [status(thm)], [f_98])).
% 7.16/2.52  tff(c_645, plain, (v1_funct_2(k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3')), k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_2(k2_funct_1('#skF_3'), k2_struct_0('#skF_2'), k2_struct_0('#skF_1')) | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_636, c_28])).
% 7.16/2.52  tff(c_660, plain, (v1_funct_2(k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3')), k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_627, c_626, c_645])).
% 7.16/2.52  tff(c_2444, plain, (v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')), k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2442, c_660])).
% 7.16/2.52  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 7.16/2.52  tff(c_2, plain, (![B_3, A_1]: (v1_relat_1(B_3) | ~m1_subset_1(B_3, k1_zfmisc_1(A_1)) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.16/2.52  tff(c_85, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_82, c_2])).
% 7.16/2.52  tff(c_88, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_85])).
% 7.16/2.52  tff(c_6, plain, (![A_6]: (k2_funct_1(k2_funct_1(A_6))=A_6 | ~v2_funct_1(A_6) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_42])).
% 7.16/2.52  tff(c_2450, plain, (m1_subset_1(k2_funct_1(k2_funct_1('#skF_3')), k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1')))) | ~v1_funct_2(k2_funct_1('#skF_3'), k2_struct_0('#skF_2'), k2_struct_0('#skF_1')) | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_2442, c_26])).
% 7.16/2.52  tff(c_2454, plain, (m1_subset_1(k2_funct_1(k2_funct_1('#skF_3')), k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_627, c_626, c_636, c_2450])).
% 7.16/2.52  tff(c_599, plain, (![C_116, A_117, B_118]: (v2_funct_1(C_116) | ~v3_tops_2(C_116, A_117, B_118) | ~m1_subset_1(C_116, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_117), u1_struct_0(B_118)))) | ~v1_funct_2(C_116, u1_struct_0(A_117), u1_struct_0(B_118)) | ~v1_funct_1(C_116) | ~l1_pre_topc(B_118) | ~l1_pre_topc(A_117))), inference(cnfTransformation, [status(thm)], [f_86])).
% 7.16/2.52  tff(c_606, plain, (![C_116, B_118]: (v2_funct_1(C_116) | ~v3_tops_2(C_116, '#skF_1', B_118) | ~m1_subset_1(C_116, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), u1_struct_0(B_118)))) | ~v1_funct_2(C_116, u1_struct_0('#skF_1'), u1_struct_0(B_118)) | ~v1_funct_1(C_116) | ~l1_pre_topc(B_118) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_68, c_599])).
% 7.16/2.52  tff(c_2628, plain, (![C_337, B_338]: (v2_funct_1(C_337) | ~v3_tops_2(C_337, '#skF_1', B_338) | ~m1_subset_1(C_337, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), u1_struct_0(B_338)))) | ~v1_funct_2(C_337, k2_struct_0('#skF_1'), u1_struct_0(B_338)) | ~v1_funct_1(C_337) | ~l1_pre_topc(B_338))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_68, c_606])).
% 7.16/2.52  tff(c_2638, plain, (![C_337]: (v2_funct_1(C_337) | ~v3_tops_2(C_337, '#skF_1', '#skF_2') | ~m1_subset_1(C_337, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_337, k2_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1(C_337) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_67, c_2628])).
% 7.16/2.52  tff(c_2644, plain, (![C_339]: (v2_funct_1(C_339) | ~v3_tops_2(C_339, '#skF_1', '#skF_2') | ~m1_subset_1(C_339, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_339, k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1(C_339))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_67, c_2638])).
% 7.16/2.52  tff(c_2647, plain, (v2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v3_tops_2(k2_funct_1(k2_funct_1('#skF_3')), '#skF_1', '#skF_2') | ~v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')), k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(resolution, [status(thm)], [c_2454, c_2644])).
% 7.16/2.52  tff(c_2657, plain, (v2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v3_tops_2(k2_funct_1(k2_funct_1('#skF_3')), '#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2445, c_2444, c_2647])).
% 7.16/2.52  tff(c_2662, plain, (~v3_tops_2(k2_funct_1(k2_funct_1('#skF_3')), '#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_2657])).
% 7.16/2.52  tff(c_2665, plain, (~v3_tops_2('#skF_3', '#skF_1', '#skF_2') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_6, c_2662])).
% 7.16/2.52  tff(c_2668, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_88, c_46, c_598, c_40, c_2665])).
% 7.16/2.52  tff(c_2670, plain, (v3_tops_2(k2_funct_1(k2_funct_1('#skF_3')), '#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_2657])).
% 7.16/2.52  tff(c_667, plain, (![C_119, A_120, B_121]: (v5_pre_topc(C_119, A_120, B_121) | ~v3_tops_2(C_119, A_120, B_121) | ~m1_subset_1(C_119, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_120), u1_struct_0(B_121)))) | ~v1_funct_2(C_119, u1_struct_0(A_120), u1_struct_0(B_121)) | ~v1_funct_1(C_119) | ~l1_pre_topc(B_121) | ~l1_pre_topc(A_120))), inference(cnfTransformation, [status(thm)], [f_86])).
% 7.16/2.52  tff(c_683, plain, (![C_119, A_120]: (v5_pre_topc(C_119, A_120, '#skF_2') | ~v3_tops_2(C_119, A_120, '#skF_2') | ~m1_subset_1(C_119, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_120), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_119, u1_struct_0(A_120), u1_struct_0('#skF_2')) | ~v1_funct_1(C_119) | ~l1_pre_topc('#skF_2') | ~l1_pre_topc(A_120))), inference(superposition, [status(thm), theory('equality')], [c_67, c_667])).
% 7.16/2.52  tff(c_2774, plain, (![C_352, A_353]: (v5_pre_topc(C_352, A_353, '#skF_2') | ~v3_tops_2(C_352, A_353, '#skF_2') | ~m1_subset_1(C_352, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_353), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_352, u1_struct_0(A_353), k2_struct_0('#skF_2')) | ~v1_funct_1(C_352) | ~l1_pre_topc(A_353))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_67, c_683])).
% 7.16/2.52  tff(c_2781, plain, (![C_352]: (v5_pre_topc(C_352, '#skF_1', '#skF_2') | ~v3_tops_2(C_352, '#skF_1', '#skF_2') | ~m1_subset_1(C_352, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_352, u1_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1(C_352) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_68, c_2774])).
% 7.16/2.52  tff(c_2790, plain, (![C_354]: (v5_pre_topc(C_354, '#skF_1', '#skF_2') | ~v3_tops_2(C_354, '#skF_1', '#skF_2') | ~m1_subset_1(C_354, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_354, k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1(C_354))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_68, c_2781])).
% 7.16/2.52  tff(c_2793, plain, (v5_pre_topc(k2_funct_1(k2_funct_1('#skF_3')), '#skF_1', '#skF_2') | ~v3_tops_2(k2_funct_1(k2_funct_1('#skF_3')), '#skF_1', '#skF_2') | ~v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')), k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(resolution, [status(thm)], [c_2454, c_2790])).
% 7.16/2.52  tff(c_2803, plain, (v5_pre_topc(k2_funct_1(k2_funct_1('#skF_3')), '#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2445, c_2444, c_2670, c_2793])).
% 7.16/2.52  tff(c_3232, plain, (![C_382, A_383, B_384]: (v3_tops_2(C_382, A_383, B_384) | ~v5_pre_topc(k2_tops_2(u1_struct_0(A_383), u1_struct_0(B_384), C_382), B_384, A_383) | ~v5_pre_topc(C_382, A_383, B_384) | ~v2_funct_1(C_382) | k2_relset_1(u1_struct_0(A_383), u1_struct_0(B_384), C_382)!=k2_struct_0(B_384) | k1_relset_1(u1_struct_0(A_383), u1_struct_0(B_384), C_382)!=k2_struct_0(A_383) | ~m1_subset_1(C_382, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_383), u1_struct_0(B_384)))) | ~v1_funct_2(C_382, u1_struct_0(A_383), u1_struct_0(B_384)) | ~v1_funct_1(C_382) | ~l1_pre_topc(B_384) | ~l1_pre_topc(A_383))), inference(cnfTransformation, [status(thm)], [f_86])).
% 7.16/2.52  tff(c_3238, plain, (![C_382, B_384]: (v3_tops_2(C_382, '#skF_2', B_384) | ~v5_pre_topc(k2_tops_2(k2_struct_0('#skF_2'), u1_struct_0(B_384), C_382), B_384, '#skF_2') | ~v5_pre_topc(C_382, '#skF_2', B_384) | ~v2_funct_1(C_382) | k2_relset_1(u1_struct_0('#skF_2'), u1_struct_0(B_384), C_382)!=k2_struct_0(B_384) | k1_relset_1(u1_struct_0('#skF_2'), u1_struct_0(B_384), C_382)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_382, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0(B_384)))) | ~v1_funct_2(C_382, u1_struct_0('#skF_2'), u1_struct_0(B_384)) | ~v1_funct_1(C_382) | ~l1_pre_topc(B_384) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_67, c_3232])).
% 7.16/2.52  tff(c_4398, plain, (![C_492, B_493]: (v3_tops_2(C_492, '#skF_2', B_493) | ~v5_pre_topc(k2_tops_2(k2_struct_0('#skF_2'), u1_struct_0(B_493), C_492), B_493, '#skF_2') | ~v5_pre_topc(C_492, '#skF_2', B_493) | ~v2_funct_1(C_492) | k2_relset_1(k2_struct_0('#skF_2'), u1_struct_0(B_493), C_492)!=k2_struct_0(B_493) | k1_relset_1(k2_struct_0('#skF_2'), u1_struct_0(B_493), C_492)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_492, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), u1_struct_0(B_493)))) | ~v1_funct_2(C_492, k2_struct_0('#skF_2'), u1_struct_0(B_493)) | ~v1_funct_1(C_492) | ~l1_pre_topc(B_493))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_67, c_67, c_67, c_67, c_3238])).
% 7.16/2.52  tff(c_4400, plain, (![C_492]: (v3_tops_2(C_492, '#skF_2', '#skF_1') | ~v5_pre_topc(k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), C_492), '#skF_1', '#skF_2') | ~v5_pre_topc(C_492, '#skF_2', '#skF_1') | ~v2_funct_1(C_492) | k2_relset_1(k2_struct_0('#skF_2'), u1_struct_0('#skF_1'), C_492)!=k2_struct_0('#skF_1') | k1_relset_1(k2_struct_0('#skF_2'), u1_struct_0('#skF_1'), C_492)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_492, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), u1_struct_0('#skF_1')))) | ~v1_funct_2(C_492, k2_struct_0('#skF_2'), u1_struct_0('#skF_1')) | ~v1_funct_1(C_492) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_68, c_4398])).
% 7.16/2.52  tff(c_4407, plain, (![C_494]: (v3_tops_2(C_494, '#skF_2', '#skF_1') | ~v5_pre_topc(k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), C_494), '#skF_1', '#skF_2') | ~v5_pre_topc(C_494, '#skF_2', '#skF_1') | ~v2_funct_1(C_494) | k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), C_494)!=k2_struct_0('#skF_1') | k1_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), C_494)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_494, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1')))) | ~v1_funct_2(C_494, k2_struct_0('#skF_2'), k2_struct_0('#skF_1')) | ~v1_funct_1(C_494))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_68, c_68, c_68, c_68, c_4400])).
% 7.16/2.52  tff(c_4410, plain, (v3_tops_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~v5_pre_topc(k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3')), '#skF_1', '#skF_2') | ~v5_pre_topc(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~v2_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))!=k2_struct_0('#skF_1') | k1_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))!=k2_struct_0('#skF_2') | ~v1_funct_2(k2_funct_1('#skF_3'), k2_struct_0('#skF_2'), k2_struct_0('#skF_1')) | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_636, c_4407])).
% 7.16/2.52  tff(c_4417, plain, (v3_tops_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_627, c_626, c_3757, c_1614, c_2443, c_3411, c_2803, c_2442, c_4410])).
% 7.16/2.52  tff(c_4419, plain, $false, inference(negUnitSimplification, [status(thm)], [c_628, c_4417])).
% 7.16/2.52  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.16/2.52  
% 7.16/2.52  Inference rules
% 7.16/2.52  ----------------------
% 7.16/2.52  #Ref     : 0
% 7.16/2.52  #Sup     : 836
% 7.16/2.52  #Fact    : 0
% 7.16/2.52  #Define  : 0
% 7.16/2.52  #Split   : 13
% 7.16/2.52  #Chain   : 0
% 7.16/2.52  #Close   : 0
% 7.16/2.52  
% 7.16/2.52  Ordering : KBO
% 7.16/2.52  
% 7.16/2.52  Simplification rules
% 7.16/2.52  ----------------------
% 7.16/2.52  #Subsume      : 144
% 7.16/2.52  #Demod        : 2337
% 7.16/2.52  #Tautology    : 162
% 7.16/2.52  #SimpNegUnit  : 27
% 7.16/2.52  #BackRed      : 15
% 7.16/2.52  
% 7.16/2.52  #Partial instantiations: 0
% 7.16/2.52  #Strategies tried      : 1
% 7.16/2.52  
% 7.16/2.52  Timing (in seconds)
% 7.16/2.52  ----------------------
% 7.16/2.52  Preprocessing        : 0.35
% 7.16/2.52  Parsing              : 0.18
% 7.16/2.52  CNF conversion       : 0.02
% 7.16/2.52  Main loop            : 1.35
% 7.16/2.52  Inferencing          : 0.45
% 7.16/2.52  Reduction            : 0.53
% 7.16/2.52  Demodulation         : 0.41
% 7.16/2.52  BG Simplification    : 0.06
% 7.16/2.52  Subsumption          : 0.23
% 7.16/2.52  Abstraction          : 0.06
% 7.16/2.52  MUC search           : 0.00
% 7.16/2.52  Cooper               : 0.00
% 7.16/2.52  Total                : 1.79
% 7.16/2.52  Index Insertion      : 0.00
% 7.16/2.52  Index Deletion       : 0.00
% 7.16/2.52  Index Matching       : 0.00
% 7.16/2.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
