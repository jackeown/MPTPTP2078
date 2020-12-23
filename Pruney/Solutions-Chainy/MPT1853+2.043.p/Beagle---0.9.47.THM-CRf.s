%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:06 EST 2020

% Result     : Theorem 3.14s
% Output     : CNFRefutation 3.14s
% Verified   : 
% Statistics : Number of formulae       :  140 ( 617 expanded)
%              Number of leaves         :   34 ( 218 expanded)
%              Depth                    :   14
%              Number of atoms          :  307 (1802 expanded)
%              Number of equality atoms :   14 (  61 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_tex_2 > v1_subset_1 > m1_subset_1 > m1_pre_topc > v7_struct_0 > v2_struct_0 > v1_zfmisc_1 > v1_xboole_0 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k6_domain_1 > k1_tex_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff(v1_tex_2,type,(
    v1_tex_2: ( $i * $i ) > $o )).

tff(v7_struct_0,type,(
    v7_struct_0: $i > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k1_tex_2,type,(
    k1_tex_2: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_168,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ( v1_tex_2(k1_tex_2(A,B),A)
            <=> v1_subset_1(k6_domain_1(u1_struct_0(A),B),u1_struct_0(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_tex_2)).

tff(f_106,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ( ~ v2_struct_0(k1_tex_2(A,B))
        & v1_pre_topc(k1_tex_2(A,B))
        & m1_pre_topc(k1_tex_2(A,B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tex_2)).

tff(f_36,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_29,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_120,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ( ~ v2_struct_0(k1_tex_2(A,B))
        & v7_struct_0(k1_tex_2(A,B))
        & v1_pre_topc(k1_tex_2(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_tex_2)).

tff(f_131,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,A)
         => ~ ( v1_subset_1(k6_domain_1(A,B),A)
              & v1_zfmisc_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_tex_2)).

tff(f_85,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ( v1_tex_2(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( C = u1_struct_0(B)
                 => v1_subset_1(C,u1_struct_0(A)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tex_2)).

tff(f_92,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( v1_subset_1(B,A)
      <=> B != A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).

tff(f_50,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_142,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & ~ v1_zfmisc_1(A) )
     => ! [B] :
          ( m1_subset_1(B,A)
         => v1_subset_1(k6_domain_1(A,B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tex_2)).

tff(f_155,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ~ ( v1_subset_1(k6_domain_1(u1_struct_0(A),B),u1_struct_0(A))
              & v7_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_tex_2)).

tff(f_57,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_71,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_zfmisc_1(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => ( ~ v1_xboole_0(B)
           => ~ v1_subset_1(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_tex_2)).

tff(c_46,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_48,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_44,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_670,plain,(
    ! [A_132,B_133] :
      ( m1_pre_topc(k1_tex_2(A_132,B_133),A_132)
      | ~ m1_subset_1(B_133,u1_struct_0(A_132))
      | ~ l1_pre_topc(A_132)
      | v2_struct_0(A_132) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_672,plain,
    ( m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_670])).

tff(c_675,plain,
    ( m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_672])).

tff(c_676,plain,(
    m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_675])).

tff(c_4,plain,(
    ! [B_4,A_2] :
      ( l1_pre_topc(B_4)
      | ~ m1_pre_topc(B_4,A_2)
      | ~ l1_pre_topc(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_679,plain,
    ( l1_pre_topc(k1_tex_2('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_676,c_4])).

tff(c_682,plain,(
    l1_pre_topc(k1_tex_2('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_679])).

tff(c_2,plain,(
    ! [A_1] :
      ( l1_struct_0(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_652,plain,(
    ! [A_126,B_127] :
      ( ~ v2_struct_0(k1_tex_2(A_126,B_127))
      | ~ m1_subset_1(B_127,u1_struct_0(A_126))
      | ~ l1_pre_topc(A_126)
      | v2_struct_0(A_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_655,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_652])).

tff(c_658,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_655])).

tff(c_659,plain,(
    ~ v2_struct_0(k1_tex_2('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_658])).

tff(c_50,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0('#skF_2'),'#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_tex_2(k1_tex_2('#skF_2','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_67,plain,(
    ~ v1_tex_2(k1_tex_2('#skF_2','#skF_3'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_56,plain,
    ( v1_tex_2(k1_tex_2('#skF_2','#skF_3'),'#skF_2')
    | v1_subset_1(k6_domain_1(u1_struct_0('#skF_2'),'#skF_3'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_95,plain,(
    v1_subset_1(k6_domain_1(u1_struct_0('#skF_2'),'#skF_3'),u1_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_67,c_56])).

tff(c_97,plain,(
    ! [A_56,B_57] :
      ( ~ v1_zfmisc_1(A_56)
      | ~ v1_subset_1(k6_domain_1(A_56,B_57),A_56)
      | ~ m1_subset_1(B_57,A_56)
      | v1_xboole_0(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_103,plain,
    ( ~ v1_zfmisc_1(u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_95,c_97])).

tff(c_107,plain,
    ( ~ v1_zfmisc_1(u1_struct_0('#skF_2'))
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_103])).

tff(c_108,plain,(
    ~ v1_zfmisc_1(u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_107])).

tff(c_122,plain,(
    ! [A_62,B_63] :
      ( m1_pre_topc(k1_tex_2(A_62,B_63),A_62)
      | ~ m1_subset_1(B_63,u1_struct_0(A_62))
      | ~ l1_pre_topc(A_62)
      | v2_struct_0(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_124,plain,
    ( m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_122])).

tff(c_127,plain,
    ( m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_124])).

tff(c_128,plain,(
    m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_127])).

tff(c_251,plain,(
    ! [A_76,B_77] :
      ( m1_subset_1('#skF_1'(A_76,B_77),k1_zfmisc_1(u1_struct_0(A_76)))
      | v1_tex_2(B_77,A_76)
      | ~ m1_pre_topc(B_77,A_76)
      | ~ l1_pre_topc(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_22,plain,(
    ! [B_24,A_23] :
      ( v1_subset_1(B_24,A_23)
      | B_24 = A_23
      | ~ m1_subset_1(B_24,k1_zfmisc_1(A_23)) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_531,plain,(
    ! [A_113,B_114] :
      ( v1_subset_1('#skF_1'(A_113,B_114),u1_struct_0(A_113))
      | u1_struct_0(A_113) = '#skF_1'(A_113,B_114)
      | v1_tex_2(B_114,A_113)
      | ~ m1_pre_topc(B_114,A_113)
      | ~ l1_pre_topc(A_113) ) ),
    inference(resolution,[status(thm)],[c_251,c_22])).

tff(c_16,plain,(
    ! [A_13,B_19] :
      ( ~ v1_subset_1('#skF_1'(A_13,B_19),u1_struct_0(A_13))
      | v1_tex_2(B_19,A_13)
      | ~ m1_pre_topc(B_19,A_13)
      | ~ l1_pre_topc(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_541,plain,(
    ! [A_115,B_116] :
      ( u1_struct_0(A_115) = '#skF_1'(A_115,B_116)
      | v1_tex_2(B_116,A_115)
      | ~ m1_pre_topc(B_116,A_115)
      | ~ l1_pre_topc(A_115) ) ),
    inference(resolution,[status(thm)],[c_531,c_16])).

tff(c_552,plain,
    ( '#skF_1'('#skF_2',k1_tex_2('#skF_2','#skF_3')) = u1_struct_0('#skF_2')
    | ~ m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_541,c_67])).

tff(c_559,plain,(
    '#skF_1'('#skF_2',k1_tex_2('#skF_2','#skF_3')) = u1_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_128,c_552])).

tff(c_404,plain,(
    ! [A_97,B_98] :
      ( v1_subset_1('#skF_1'(A_97,B_98),u1_struct_0(A_97))
      | u1_struct_0(A_97) = '#skF_1'(A_97,B_98)
      | v1_tex_2(B_98,A_97)
      | ~ m1_pre_topc(B_98,A_97)
      | ~ l1_pre_topc(A_97) ) ),
    inference(resolution,[status(thm)],[c_251,c_22])).

tff(c_414,plain,(
    ! [A_99,B_100] :
      ( u1_struct_0(A_99) = '#skF_1'(A_99,B_100)
      | v1_tex_2(B_100,A_99)
      | ~ m1_pre_topc(B_100,A_99)
      | ~ l1_pre_topc(A_99) ) ),
    inference(resolution,[status(thm)],[c_404,c_16])).

tff(c_421,plain,
    ( '#skF_1'('#skF_2',k1_tex_2('#skF_2','#skF_3')) = u1_struct_0('#skF_2')
    | ~ m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_414,c_67])).

tff(c_425,plain,(
    '#skF_1'('#skF_2',k1_tex_2('#skF_2','#skF_3')) = u1_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_128,c_421])).

tff(c_131,plain,
    ( l1_pre_topc(k1_tex_2('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_128,c_4])).

tff(c_134,plain,(
    l1_pre_topc(k1_tex_2('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_131])).

tff(c_79,plain,(
    ! [A_50,B_51] :
      ( ~ v2_struct_0(k1_tex_2(A_50,B_51))
      | ~ m1_subset_1(B_51,u1_struct_0(A_50))
      | ~ l1_pre_topc(A_50)
      | v2_struct_0(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_82,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_79])).

tff(c_85,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_82])).

tff(c_86,plain,(
    ~ v2_struct_0(k1_tex_2('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_85])).

tff(c_135,plain,(
    ! [B_64,A_65] :
      ( u1_struct_0(B_64) = '#skF_1'(A_65,B_64)
      | v1_tex_2(B_64,A_65)
      | ~ m1_pre_topc(B_64,A_65)
      | ~ l1_pre_topc(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_138,plain,
    ( u1_struct_0(k1_tex_2('#skF_2','#skF_3')) = '#skF_1'('#skF_2',k1_tex_2('#skF_2','#skF_3'))
    | ~ m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_135,c_67])).

tff(c_141,plain,(
    u1_struct_0(k1_tex_2('#skF_2','#skF_3')) = '#skF_1'('#skF_2',k1_tex_2('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_128,c_138])).

tff(c_8,plain,(
    ! [A_6] :
      ( ~ v1_xboole_0(u1_struct_0(A_6))
      | ~ l1_struct_0(A_6)
      | v2_struct_0(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_171,plain,
    ( ~ v1_xboole_0('#skF_1'('#skF_2',k1_tex_2('#skF_2','#skF_3')))
    | ~ l1_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | v2_struct_0(k1_tex_2('#skF_2','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_141,c_8])).

tff(c_192,plain,
    ( ~ v1_xboole_0('#skF_1'('#skF_2',k1_tex_2('#skF_2','#skF_3')))
    | ~ l1_struct_0(k1_tex_2('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_171])).

tff(c_194,plain,(
    ~ l1_struct_0(k1_tex_2('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_192])).

tff(c_197,plain,(
    ~ l1_pre_topc(k1_tex_2('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_2,c_194])).

tff(c_201,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_197])).

tff(c_202,plain,(
    ~ v1_xboole_0('#skF_1'('#skF_2',k1_tex_2('#skF_2','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_192])).

tff(c_203,plain,(
    l1_struct_0(k1_tex_2('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_192])).

tff(c_109,plain,(
    ! [A_58,B_59] :
      ( v7_struct_0(k1_tex_2(A_58,B_59))
      | ~ m1_subset_1(B_59,u1_struct_0(A_58))
      | ~ l1_pre_topc(A_58)
      | v2_struct_0(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_112,plain,
    ( v7_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_109])).

tff(c_115,plain,
    ( v7_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_112])).

tff(c_116,plain,(
    v7_struct_0(k1_tex_2('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_115])).

tff(c_40,plain,(
    ! [A_32,B_34] :
      ( v1_subset_1(k6_domain_1(A_32,B_34),A_32)
      | ~ m1_subset_1(B_34,A_32)
      | v1_zfmisc_1(A_32)
      | v1_xboole_0(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_281,plain,(
    ! [A_79,B_80] :
      ( ~ v7_struct_0(A_79)
      | ~ v1_subset_1(k6_domain_1(u1_struct_0(A_79),B_80),u1_struct_0(A_79))
      | ~ m1_subset_1(B_80,u1_struct_0(A_79))
      | ~ l1_struct_0(A_79)
      | v2_struct_0(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_351,plain,(
    ! [A_87,B_88] :
      ( ~ v7_struct_0(A_87)
      | ~ l1_struct_0(A_87)
      | v2_struct_0(A_87)
      | ~ m1_subset_1(B_88,u1_struct_0(A_87))
      | v1_zfmisc_1(u1_struct_0(A_87))
      | v1_xboole_0(u1_struct_0(A_87)) ) ),
    inference(resolution,[status(thm)],[c_40,c_281])).

tff(c_354,plain,(
    ! [B_88] :
      ( ~ v7_struct_0(k1_tex_2('#skF_2','#skF_3'))
      | ~ l1_struct_0(k1_tex_2('#skF_2','#skF_3'))
      | v2_struct_0(k1_tex_2('#skF_2','#skF_3'))
      | ~ m1_subset_1(B_88,'#skF_1'('#skF_2',k1_tex_2('#skF_2','#skF_3')))
      | v1_zfmisc_1(u1_struct_0(k1_tex_2('#skF_2','#skF_3')))
      | v1_xboole_0(u1_struct_0(k1_tex_2('#skF_2','#skF_3'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_141,c_351])).

tff(c_359,plain,(
    ! [B_88] :
      ( v2_struct_0(k1_tex_2('#skF_2','#skF_3'))
      | ~ m1_subset_1(B_88,'#skF_1'('#skF_2',k1_tex_2('#skF_2','#skF_3')))
      | v1_zfmisc_1('#skF_1'('#skF_2',k1_tex_2('#skF_2','#skF_3')))
      | v1_xboole_0('#skF_1'('#skF_2',k1_tex_2('#skF_2','#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_141,c_203,c_116,c_354])).

tff(c_360,plain,(
    ! [B_88] :
      ( ~ m1_subset_1(B_88,'#skF_1'('#skF_2',k1_tex_2('#skF_2','#skF_3')))
      | v1_zfmisc_1('#skF_1'('#skF_2',k1_tex_2('#skF_2','#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_202,c_86,c_359])).

tff(c_365,plain,(
    ! [B_88] : ~ m1_subset_1(B_88,'#skF_1'('#skF_2',k1_tex_2('#skF_2','#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_360])).

tff(c_427,plain,(
    ! [B_88] : ~ m1_subset_1(B_88,u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_425,c_365])).

tff(c_455,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_427,c_44])).

tff(c_456,plain,(
    v1_zfmisc_1('#skF_1'('#skF_2',k1_tex_2('#skF_2','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_360])).

tff(c_563,plain,(
    v1_zfmisc_1(u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_559,c_456])).

tff(c_575,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_108,c_563])).

tff(c_576,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_107])).

tff(c_580,plain,
    ( ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_576,c_8])).

tff(c_583,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_580])).

tff(c_586,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_2,c_583])).

tff(c_590,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_586])).

tff(c_592,plain,(
    v1_tex_2(k1_tex_2('#skF_2','#skF_3'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_609,plain,(
    ! [A_120,B_121] :
      ( v1_subset_1(k6_domain_1(A_120,B_121),A_120)
      | ~ m1_subset_1(B_121,A_120)
      | v1_zfmisc_1(A_120)
      | v1_xboole_0(A_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_591,plain,(
    ~ v1_subset_1(k6_domain_1(u1_struct_0('#skF_2'),'#skF_3'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_593,plain,(
    v1_subset_1(k6_domain_1(u1_struct_0('#skF_2'),'#skF_3'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_594,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_591,c_593])).

tff(c_596,plain,(
    ~ v1_subset_1(k6_domain_1(u1_struct_0('#skF_2'),'#skF_3'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_612,plain,
    ( ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | v1_zfmisc_1(u1_struct_0('#skF_2'))
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_609,c_596])).

tff(c_615,plain,
    ( v1_zfmisc_1(u1_struct_0('#skF_2'))
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_612])).

tff(c_616,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_615])).

tff(c_619,plain,
    ( ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_616,c_8])).

tff(c_622,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_619])).

tff(c_625,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_2,c_622])).

tff(c_629,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_625])).

tff(c_631,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_615])).

tff(c_630,plain,(
    v1_zfmisc_1(u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_615])).

tff(c_10,plain,(
    ! [B_9,A_7] :
      ( m1_subset_1(u1_struct_0(B_9),k1_zfmisc_1(u1_struct_0(A_7)))
      | ~ m1_pre_topc(B_9,A_7)
      | ~ l1_pre_topc(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_714,plain,(
    ! [B_146,A_147] :
      ( v1_subset_1(u1_struct_0(B_146),u1_struct_0(A_147))
      | ~ m1_subset_1(u1_struct_0(B_146),k1_zfmisc_1(u1_struct_0(A_147)))
      | ~ v1_tex_2(B_146,A_147)
      | ~ m1_pre_topc(B_146,A_147)
      | ~ l1_pre_topc(A_147) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_718,plain,(
    ! [B_9,A_7] :
      ( v1_subset_1(u1_struct_0(B_9),u1_struct_0(A_7))
      | ~ v1_tex_2(B_9,A_7)
      | ~ m1_pre_topc(B_9,A_7)
      | ~ l1_pre_topc(A_7) ) ),
    inference(resolution,[status(thm)],[c_10,c_714])).

tff(c_665,plain,(
    ! [B_130,A_131] :
      ( ~ v1_subset_1(B_130,A_131)
      | v1_xboole_0(B_130)
      | ~ m1_subset_1(B_130,k1_zfmisc_1(A_131))
      | ~ v1_zfmisc_1(A_131)
      | v1_xboole_0(A_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_743,plain,(
    ! [B_156,A_157] :
      ( ~ v1_subset_1(u1_struct_0(B_156),u1_struct_0(A_157))
      | v1_xboole_0(u1_struct_0(B_156))
      | ~ v1_zfmisc_1(u1_struct_0(A_157))
      | v1_xboole_0(u1_struct_0(A_157))
      | ~ m1_pre_topc(B_156,A_157)
      | ~ l1_pre_topc(A_157) ) ),
    inference(resolution,[status(thm)],[c_10,c_665])).

tff(c_752,plain,(
    ! [B_158,A_159] :
      ( v1_xboole_0(u1_struct_0(B_158))
      | ~ v1_zfmisc_1(u1_struct_0(A_159))
      | v1_xboole_0(u1_struct_0(A_159))
      | ~ v1_tex_2(B_158,A_159)
      | ~ m1_pre_topc(B_158,A_159)
      | ~ l1_pre_topc(A_159) ) ),
    inference(resolution,[status(thm)],[c_718,c_743])).

tff(c_754,plain,(
    ! [B_158] :
      ( v1_xboole_0(u1_struct_0(B_158))
      | v1_xboole_0(u1_struct_0('#skF_2'))
      | ~ v1_tex_2(B_158,'#skF_2')
      | ~ m1_pre_topc(B_158,'#skF_2')
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_630,c_752])).

tff(c_757,plain,(
    ! [B_158] :
      ( v1_xboole_0(u1_struct_0(B_158))
      | v1_xboole_0(u1_struct_0('#skF_2'))
      | ~ v1_tex_2(B_158,'#skF_2')
      | ~ m1_pre_topc(B_158,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_754])).

tff(c_759,plain,(
    ! [B_160] :
      ( v1_xboole_0(u1_struct_0(B_160))
      | ~ v1_tex_2(B_160,'#skF_2')
      | ~ m1_pre_topc(B_160,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_631,c_757])).

tff(c_769,plain,(
    ! [B_161] :
      ( ~ l1_struct_0(B_161)
      | v2_struct_0(B_161)
      | ~ v1_tex_2(B_161,'#skF_2')
      | ~ m1_pre_topc(B_161,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_759,c_8])).

tff(c_780,plain,
    ( ~ l1_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | v2_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | ~ m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_592,c_769])).

tff(c_789,plain,
    ( ~ l1_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | v2_struct_0(k1_tex_2('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_676,c_780])).

tff(c_790,plain,(
    ~ l1_struct_0(k1_tex_2('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_659,c_789])).

tff(c_793,plain,(
    ~ l1_pre_topc(k1_tex_2('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_2,c_790])).

tff(c_797,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_682,c_793])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:27:01 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.14/1.46  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.14/1.48  
% 3.14/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.14/1.48  %$ v1_tex_2 > v1_subset_1 > m1_subset_1 > m1_pre_topc > v7_struct_0 > v2_struct_0 > v1_zfmisc_1 > v1_xboole_0 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k6_domain_1 > k1_tex_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 3.14/1.48  
% 3.14/1.48  %Foreground sorts:
% 3.14/1.48  
% 3.14/1.48  
% 3.14/1.48  %Background operators:
% 3.14/1.48  
% 3.14/1.48  
% 3.14/1.48  %Foreground operators:
% 3.14/1.48  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.14/1.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.14/1.48  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 3.14/1.48  tff(v1_tex_2, type, v1_tex_2: ($i * $i) > $o).
% 3.14/1.48  tff(v7_struct_0, type, v7_struct_0: $i > $o).
% 3.14/1.48  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.14/1.48  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 3.14/1.48  tff('#skF_2', type, '#skF_2': $i).
% 3.14/1.48  tff('#skF_3', type, '#skF_3': $i).
% 3.14/1.48  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 3.14/1.48  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.14/1.48  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.14/1.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.14/1.48  tff(k1_tex_2, type, k1_tex_2: ($i * $i) > $i).
% 3.14/1.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.14/1.48  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 3.14/1.48  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.14/1.48  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.14/1.48  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.14/1.48  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.14/1.48  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.14/1.48  
% 3.14/1.50  tff(f_168, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (v1_tex_2(k1_tex_2(A, B), A) <=> v1_subset_1(k6_domain_1(u1_struct_0(A), B), u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_tex_2)).
% 3.14/1.50  tff(f_106, axiom, (![A, B]: (((~v2_struct_0(A) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => ((~v2_struct_0(k1_tex_2(A, B)) & v1_pre_topc(k1_tex_2(A, B))) & m1_pre_topc(k1_tex_2(A, B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tex_2)).
% 3.14/1.50  tff(f_36, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 3.14/1.50  tff(f_29, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.14/1.50  tff(f_120, axiom, (![A, B]: (((~v2_struct_0(A) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => ((~v2_struct_0(k1_tex_2(A, B)) & v7_struct_0(k1_tex_2(A, B))) & v1_pre_topc(k1_tex_2(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_tex_2)).
% 3.14/1.50  tff(f_131, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, A) => ~(v1_subset_1(k6_domain_1(A, B), A) & v1_zfmisc_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_tex_2)).
% 3.14/1.50  tff(f_85, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (v1_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => v1_subset_1(C, u1_struct_0(A)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tex_2)).
% 3.14/1.50  tff(f_92, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (v1_subset_1(B, A) <=> ~(B = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_subset_1)).
% 3.14/1.50  tff(f_50, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 3.14/1.50  tff(f_142, axiom, (![A]: ((~v1_xboole_0(A) & ~v1_zfmisc_1(A)) => (![B]: (m1_subset_1(B, A) => v1_subset_1(k6_domain_1(A, B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_tex_2)).
% 3.14/1.50  tff(f_155, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => ~(v1_subset_1(k6_domain_1(u1_struct_0(A), B), u1_struct_0(A)) & v7_struct_0(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_tex_2)).
% 3.14/1.50  tff(f_57, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 3.14/1.50  tff(f_71, axiom, (![A]: ((~v1_xboole_0(A) & v1_zfmisc_1(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (~v1_xboole_0(B) => ~v1_subset_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_tex_2)).
% 3.14/1.50  tff(c_46, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_168])).
% 3.14/1.50  tff(c_48, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_168])).
% 3.14/1.50  tff(c_44, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_168])).
% 3.14/1.50  tff(c_670, plain, (![A_132, B_133]: (m1_pre_topc(k1_tex_2(A_132, B_133), A_132) | ~m1_subset_1(B_133, u1_struct_0(A_132)) | ~l1_pre_topc(A_132) | v2_struct_0(A_132))), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.14/1.50  tff(c_672, plain, (m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2') | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_44, c_670])).
% 3.14/1.50  tff(c_675, plain, (m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_672])).
% 3.14/1.50  tff(c_676, plain, (m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_48, c_675])).
% 3.14/1.50  tff(c_4, plain, (![B_4, A_2]: (l1_pre_topc(B_4) | ~m1_pre_topc(B_4, A_2) | ~l1_pre_topc(A_2))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.14/1.50  tff(c_679, plain, (l1_pre_topc(k1_tex_2('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_676, c_4])).
% 3.14/1.50  tff(c_682, plain, (l1_pre_topc(k1_tex_2('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_679])).
% 3.14/1.50  tff(c_2, plain, (![A_1]: (l1_struct_0(A_1) | ~l1_pre_topc(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.14/1.50  tff(c_652, plain, (![A_126, B_127]: (~v2_struct_0(k1_tex_2(A_126, B_127)) | ~m1_subset_1(B_127, u1_struct_0(A_126)) | ~l1_pre_topc(A_126) | v2_struct_0(A_126))), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.14/1.50  tff(c_655, plain, (~v2_struct_0(k1_tex_2('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_44, c_652])).
% 3.14/1.50  tff(c_658, plain, (~v2_struct_0(k1_tex_2('#skF_2', '#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_655])).
% 3.14/1.50  tff(c_659, plain, (~v2_struct_0(k1_tex_2('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_48, c_658])).
% 3.14/1.50  tff(c_50, plain, (~v1_subset_1(k6_domain_1(u1_struct_0('#skF_2'), '#skF_3'), u1_struct_0('#skF_2')) | ~v1_tex_2(k1_tex_2('#skF_2', '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_168])).
% 3.14/1.50  tff(c_67, plain, (~v1_tex_2(k1_tex_2('#skF_2', '#skF_3'), '#skF_2')), inference(splitLeft, [status(thm)], [c_50])).
% 3.14/1.50  tff(c_56, plain, (v1_tex_2(k1_tex_2('#skF_2', '#skF_3'), '#skF_2') | v1_subset_1(k6_domain_1(u1_struct_0('#skF_2'), '#skF_3'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_168])).
% 3.14/1.50  tff(c_95, plain, (v1_subset_1(k6_domain_1(u1_struct_0('#skF_2'), '#skF_3'), u1_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_67, c_56])).
% 3.14/1.50  tff(c_97, plain, (![A_56, B_57]: (~v1_zfmisc_1(A_56) | ~v1_subset_1(k6_domain_1(A_56, B_57), A_56) | ~m1_subset_1(B_57, A_56) | v1_xboole_0(A_56))), inference(cnfTransformation, [status(thm)], [f_131])).
% 3.14/1.50  tff(c_103, plain, (~v1_zfmisc_1(u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | v1_xboole_0(u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_95, c_97])).
% 3.14/1.50  tff(c_107, plain, (~v1_zfmisc_1(u1_struct_0('#skF_2')) | v1_xboole_0(u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_103])).
% 3.14/1.50  tff(c_108, plain, (~v1_zfmisc_1(u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_107])).
% 3.14/1.50  tff(c_122, plain, (![A_62, B_63]: (m1_pre_topc(k1_tex_2(A_62, B_63), A_62) | ~m1_subset_1(B_63, u1_struct_0(A_62)) | ~l1_pre_topc(A_62) | v2_struct_0(A_62))), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.14/1.50  tff(c_124, plain, (m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2') | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_44, c_122])).
% 3.14/1.50  tff(c_127, plain, (m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_124])).
% 3.14/1.50  tff(c_128, plain, (m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_48, c_127])).
% 3.14/1.50  tff(c_251, plain, (![A_76, B_77]: (m1_subset_1('#skF_1'(A_76, B_77), k1_zfmisc_1(u1_struct_0(A_76))) | v1_tex_2(B_77, A_76) | ~m1_pre_topc(B_77, A_76) | ~l1_pre_topc(A_76))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.14/1.50  tff(c_22, plain, (![B_24, A_23]: (v1_subset_1(B_24, A_23) | B_24=A_23 | ~m1_subset_1(B_24, k1_zfmisc_1(A_23)))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.14/1.50  tff(c_531, plain, (![A_113, B_114]: (v1_subset_1('#skF_1'(A_113, B_114), u1_struct_0(A_113)) | u1_struct_0(A_113)='#skF_1'(A_113, B_114) | v1_tex_2(B_114, A_113) | ~m1_pre_topc(B_114, A_113) | ~l1_pre_topc(A_113))), inference(resolution, [status(thm)], [c_251, c_22])).
% 3.14/1.50  tff(c_16, plain, (![A_13, B_19]: (~v1_subset_1('#skF_1'(A_13, B_19), u1_struct_0(A_13)) | v1_tex_2(B_19, A_13) | ~m1_pre_topc(B_19, A_13) | ~l1_pre_topc(A_13))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.14/1.50  tff(c_541, plain, (![A_115, B_116]: (u1_struct_0(A_115)='#skF_1'(A_115, B_116) | v1_tex_2(B_116, A_115) | ~m1_pre_topc(B_116, A_115) | ~l1_pre_topc(A_115))), inference(resolution, [status(thm)], [c_531, c_16])).
% 3.14/1.50  tff(c_552, plain, ('#skF_1'('#skF_2', k1_tex_2('#skF_2', '#skF_3'))=u1_struct_0('#skF_2') | ~m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_541, c_67])).
% 3.14/1.50  tff(c_559, plain, ('#skF_1'('#skF_2', k1_tex_2('#skF_2', '#skF_3'))=u1_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_128, c_552])).
% 3.14/1.50  tff(c_404, plain, (![A_97, B_98]: (v1_subset_1('#skF_1'(A_97, B_98), u1_struct_0(A_97)) | u1_struct_0(A_97)='#skF_1'(A_97, B_98) | v1_tex_2(B_98, A_97) | ~m1_pre_topc(B_98, A_97) | ~l1_pre_topc(A_97))), inference(resolution, [status(thm)], [c_251, c_22])).
% 3.14/1.50  tff(c_414, plain, (![A_99, B_100]: (u1_struct_0(A_99)='#skF_1'(A_99, B_100) | v1_tex_2(B_100, A_99) | ~m1_pre_topc(B_100, A_99) | ~l1_pre_topc(A_99))), inference(resolution, [status(thm)], [c_404, c_16])).
% 3.14/1.50  tff(c_421, plain, ('#skF_1'('#skF_2', k1_tex_2('#skF_2', '#skF_3'))=u1_struct_0('#skF_2') | ~m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_414, c_67])).
% 3.14/1.50  tff(c_425, plain, ('#skF_1'('#skF_2', k1_tex_2('#skF_2', '#skF_3'))=u1_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_128, c_421])).
% 3.14/1.50  tff(c_131, plain, (l1_pre_topc(k1_tex_2('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_128, c_4])).
% 3.14/1.50  tff(c_134, plain, (l1_pre_topc(k1_tex_2('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_131])).
% 3.14/1.50  tff(c_79, plain, (![A_50, B_51]: (~v2_struct_0(k1_tex_2(A_50, B_51)) | ~m1_subset_1(B_51, u1_struct_0(A_50)) | ~l1_pre_topc(A_50) | v2_struct_0(A_50))), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.14/1.50  tff(c_82, plain, (~v2_struct_0(k1_tex_2('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_44, c_79])).
% 3.14/1.50  tff(c_85, plain, (~v2_struct_0(k1_tex_2('#skF_2', '#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_82])).
% 3.14/1.50  tff(c_86, plain, (~v2_struct_0(k1_tex_2('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_48, c_85])).
% 3.14/1.50  tff(c_135, plain, (![B_64, A_65]: (u1_struct_0(B_64)='#skF_1'(A_65, B_64) | v1_tex_2(B_64, A_65) | ~m1_pre_topc(B_64, A_65) | ~l1_pre_topc(A_65))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.14/1.50  tff(c_138, plain, (u1_struct_0(k1_tex_2('#skF_2', '#skF_3'))='#skF_1'('#skF_2', k1_tex_2('#skF_2', '#skF_3')) | ~m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_135, c_67])).
% 3.14/1.50  tff(c_141, plain, (u1_struct_0(k1_tex_2('#skF_2', '#skF_3'))='#skF_1'('#skF_2', k1_tex_2('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_128, c_138])).
% 3.14/1.50  tff(c_8, plain, (![A_6]: (~v1_xboole_0(u1_struct_0(A_6)) | ~l1_struct_0(A_6) | v2_struct_0(A_6))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.14/1.50  tff(c_171, plain, (~v1_xboole_0('#skF_1'('#skF_2', k1_tex_2('#skF_2', '#skF_3'))) | ~l1_struct_0(k1_tex_2('#skF_2', '#skF_3')) | v2_struct_0(k1_tex_2('#skF_2', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_141, c_8])).
% 3.14/1.50  tff(c_192, plain, (~v1_xboole_0('#skF_1'('#skF_2', k1_tex_2('#skF_2', '#skF_3'))) | ~l1_struct_0(k1_tex_2('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_86, c_171])).
% 3.14/1.50  tff(c_194, plain, (~l1_struct_0(k1_tex_2('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_192])).
% 3.14/1.50  tff(c_197, plain, (~l1_pre_topc(k1_tex_2('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_2, c_194])).
% 3.14/1.50  tff(c_201, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_134, c_197])).
% 3.14/1.50  tff(c_202, plain, (~v1_xboole_0('#skF_1'('#skF_2', k1_tex_2('#skF_2', '#skF_3')))), inference(splitRight, [status(thm)], [c_192])).
% 3.14/1.50  tff(c_203, plain, (l1_struct_0(k1_tex_2('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_192])).
% 3.14/1.50  tff(c_109, plain, (![A_58, B_59]: (v7_struct_0(k1_tex_2(A_58, B_59)) | ~m1_subset_1(B_59, u1_struct_0(A_58)) | ~l1_pre_topc(A_58) | v2_struct_0(A_58))), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.14/1.50  tff(c_112, plain, (v7_struct_0(k1_tex_2('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_44, c_109])).
% 3.14/1.50  tff(c_115, plain, (v7_struct_0(k1_tex_2('#skF_2', '#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_112])).
% 3.14/1.50  tff(c_116, plain, (v7_struct_0(k1_tex_2('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_48, c_115])).
% 3.14/1.50  tff(c_40, plain, (![A_32, B_34]: (v1_subset_1(k6_domain_1(A_32, B_34), A_32) | ~m1_subset_1(B_34, A_32) | v1_zfmisc_1(A_32) | v1_xboole_0(A_32))), inference(cnfTransformation, [status(thm)], [f_142])).
% 3.14/1.50  tff(c_281, plain, (![A_79, B_80]: (~v7_struct_0(A_79) | ~v1_subset_1(k6_domain_1(u1_struct_0(A_79), B_80), u1_struct_0(A_79)) | ~m1_subset_1(B_80, u1_struct_0(A_79)) | ~l1_struct_0(A_79) | v2_struct_0(A_79))), inference(cnfTransformation, [status(thm)], [f_155])).
% 3.14/1.50  tff(c_351, plain, (![A_87, B_88]: (~v7_struct_0(A_87) | ~l1_struct_0(A_87) | v2_struct_0(A_87) | ~m1_subset_1(B_88, u1_struct_0(A_87)) | v1_zfmisc_1(u1_struct_0(A_87)) | v1_xboole_0(u1_struct_0(A_87)))), inference(resolution, [status(thm)], [c_40, c_281])).
% 3.14/1.50  tff(c_354, plain, (![B_88]: (~v7_struct_0(k1_tex_2('#skF_2', '#skF_3')) | ~l1_struct_0(k1_tex_2('#skF_2', '#skF_3')) | v2_struct_0(k1_tex_2('#skF_2', '#skF_3')) | ~m1_subset_1(B_88, '#skF_1'('#skF_2', k1_tex_2('#skF_2', '#skF_3'))) | v1_zfmisc_1(u1_struct_0(k1_tex_2('#skF_2', '#skF_3'))) | v1_xboole_0(u1_struct_0(k1_tex_2('#skF_2', '#skF_3'))))), inference(superposition, [status(thm), theory('equality')], [c_141, c_351])).
% 3.14/1.50  tff(c_359, plain, (![B_88]: (v2_struct_0(k1_tex_2('#skF_2', '#skF_3')) | ~m1_subset_1(B_88, '#skF_1'('#skF_2', k1_tex_2('#skF_2', '#skF_3'))) | v1_zfmisc_1('#skF_1'('#skF_2', k1_tex_2('#skF_2', '#skF_3'))) | v1_xboole_0('#skF_1'('#skF_2', k1_tex_2('#skF_2', '#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_141, c_141, c_203, c_116, c_354])).
% 3.14/1.50  tff(c_360, plain, (![B_88]: (~m1_subset_1(B_88, '#skF_1'('#skF_2', k1_tex_2('#skF_2', '#skF_3'))) | v1_zfmisc_1('#skF_1'('#skF_2', k1_tex_2('#skF_2', '#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_202, c_86, c_359])).
% 3.14/1.50  tff(c_365, plain, (![B_88]: (~m1_subset_1(B_88, '#skF_1'('#skF_2', k1_tex_2('#skF_2', '#skF_3'))))), inference(splitLeft, [status(thm)], [c_360])).
% 3.14/1.50  tff(c_427, plain, (![B_88]: (~m1_subset_1(B_88, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_425, c_365])).
% 3.14/1.50  tff(c_455, plain, $false, inference(negUnitSimplification, [status(thm)], [c_427, c_44])).
% 3.14/1.50  tff(c_456, plain, (v1_zfmisc_1('#skF_1'('#skF_2', k1_tex_2('#skF_2', '#skF_3')))), inference(splitRight, [status(thm)], [c_360])).
% 3.14/1.50  tff(c_563, plain, (v1_zfmisc_1(u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_559, c_456])).
% 3.14/1.50  tff(c_575, plain, $false, inference(negUnitSimplification, [status(thm)], [c_108, c_563])).
% 3.14/1.50  tff(c_576, plain, (v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_107])).
% 3.14/1.50  tff(c_580, plain, (~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_576, c_8])).
% 3.14/1.50  tff(c_583, plain, (~l1_struct_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_48, c_580])).
% 3.14/1.50  tff(c_586, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_2, c_583])).
% 3.14/1.50  tff(c_590, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_586])).
% 3.14/1.50  tff(c_592, plain, (v1_tex_2(k1_tex_2('#skF_2', '#skF_3'), '#skF_2')), inference(splitRight, [status(thm)], [c_50])).
% 3.14/1.50  tff(c_609, plain, (![A_120, B_121]: (v1_subset_1(k6_domain_1(A_120, B_121), A_120) | ~m1_subset_1(B_121, A_120) | v1_zfmisc_1(A_120) | v1_xboole_0(A_120))), inference(cnfTransformation, [status(thm)], [f_142])).
% 3.14/1.50  tff(c_591, plain, (~v1_subset_1(k6_domain_1(u1_struct_0('#skF_2'), '#skF_3'), u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_50])).
% 3.14/1.50  tff(c_593, plain, (v1_subset_1(k6_domain_1(u1_struct_0('#skF_2'), '#skF_3'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_56])).
% 3.14/1.50  tff(c_594, plain, $false, inference(negUnitSimplification, [status(thm)], [c_591, c_593])).
% 3.14/1.50  tff(c_596, plain, (~v1_subset_1(k6_domain_1(u1_struct_0('#skF_2'), '#skF_3'), u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_56])).
% 3.14/1.50  tff(c_612, plain, (~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | v1_zfmisc_1(u1_struct_0('#skF_2')) | v1_xboole_0(u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_609, c_596])).
% 3.14/1.50  tff(c_615, plain, (v1_zfmisc_1(u1_struct_0('#skF_2')) | v1_xboole_0(u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_612])).
% 3.14/1.50  tff(c_616, plain, (v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_615])).
% 3.14/1.50  tff(c_619, plain, (~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_616, c_8])).
% 3.14/1.50  tff(c_622, plain, (~l1_struct_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_48, c_619])).
% 3.14/1.50  tff(c_625, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_2, c_622])).
% 3.14/1.50  tff(c_629, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_625])).
% 3.14/1.50  tff(c_631, plain, (~v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_615])).
% 3.14/1.50  tff(c_630, plain, (v1_zfmisc_1(u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_615])).
% 3.14/1.50  tff(c_10, plain, (![B_9, A_7]: (m1_subset_1(u1_struct_0(B_9), k1_zfmisc_1(u1_struct_0(A_7))) | ~m1_pre_topc(B_9, A_7) | ~l1_pre_topc(A_7))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.14/1.50  tff(c_714, plain, (![B_146, A_147]: (v1_subset_1(u1_struct_0(B_146), u1_struct_0(A_147)) | ~m1_subset_1(u1_struct_0(B_146), k1_zfmisc_1(u1_struct_0(A_147))) | ~v1_tex_2(B_146, A_147) | ~m1_pre_topc(B_146, A_147) | ~l1_pre_topc(A_147))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.14/1.50  tff(c_718, plain, (![B_9, A_7]: (v1_subset_1(u1_struct_0(B_9), u1_struct_0(A_7)) | ~v1_tex_2(B_9, A_7) | ~m1_pre_topc(B_9, A_7) | ~l1_pre_topc(A_7))), inference(resolution, [status(thm)], [c_10, c_714])).
% 3.14/1.50  tff(c_665, plain, (![B_130, A_131]: (~v1_subset_1(B_130, A_131) | v1_xboole_0(B_130) | ~m1_subset_1(B_130, k1_zfmisc_1(A_131)) | ~v1_zfmisc_1(A_131) | v1_xboole_0(A_131))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.14/1.50  tff(c_743, plain, (![B_156, A_157]: (~v1_subset_1(u1_struct_0(B_156), u1_struct_0(A_157)) | v1_xboole_0(u1_struct_0(B_156)) | ~v1_zfmisc_1(u1_struct_0(A_157)) | v1_xboole_0(u1_struct_0(A_157)) | ~m1_pre_topc(B_156, A_157) | ~l1_pre_topc(A_157))), inference(resolution, [status(thm)], [c_10, c_665])).
% 3.14/1.50  tff(c_752, plain, (![B_158, A_159]: (v1_xboole_0(u1_struct_0(B_158)) | ~v1_zfmisc_1(u1_struct_0(A_159)) | v1_xboole_0(u1_struct_0(A_159)) | ~v1_tex_2(B_158, A_159) | ~m1_pre_topc(B_158, A_159) | ~l1_pre_topc(A_159))), inference(resolution, [status(thm)], [c_718, c_743])).
% 3.14/1.50  tff(c_754, plain, (![B_158]: (v1_xboole_0(u1_struct_0(B_158)) | v1_xboole_0(u1_struct_0('#skF_2')) | ~v1_tex_2(B_158, '#skF_2') | ~m1_pre_topc(B_158, '#skF_2') | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_630, c_752])).
% 3.14/1.50  tff(c_757, plain, (![B_158]: (v1_xboole_0(u1_struct_0(B_158)) | v1_xboole_0(u1_struct_0('#skF_2')) | ~v1_tex_2(B_158, '#skF_2') | ~m1_pre_topc(B_158, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_754])).
% 3.14/1.50  tff(c_759, plain, (![B_160]: (v1_xboole_0(u1_struct_0(B_160)) | ~v1_tex_2(B_160, '#skF_2') | ~m1_pre_topc(B_160, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_631, c_757])).
% 3.14/1.50  tff(c_769, plain, (![B_161]: (~l1_struct_0(B_161) | v2_struct_0(B_161) | ~v1_tex_2(B_161, '#skF_2') | ~m1_pre_topc(B_161, '#skF_2'))), inference(resolution, [status(thm)], [c_759, c_8])).
% 3.14/1.50  tff(c_780, plain, (~l1_struct_0(k1_tex_2('#skF_2', '#skF_3')) | v2_struct_0(k1_tex_2('#skF_2', '#skF_3')) | ~m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2')), inference(resolution, [status(thm)], [c_592, c_769])).
% 3.14/1.50  tff(c_789, plain, (~l1_struct_0(k1_tex_2('#skF_2', '#skF_3')) | v2_struct_0(k1_tex_2('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_676, c_780])).
% 3.14/1.50  tff(c_790, plain, (~l1_struct_0(k1_tex_2('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_659, c_789])).
% 3.14/1.50  tff(c_793, plain, (~l1_pre_topc(k1_tex_2('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_2, c_790])).
% 3.14/1.50  tff(c_797, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_682, c_793])).
% 3.14/1.50  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.14/1.50  
% 3.14/1.50  Inference rules
% 3.14/1.50  ----------------------
% 3.14/1.50  #Ref     : 0
% 3.14/1.50  #Sup     : 121
% 3.14/1.50  #Fact    : 0
% 3.14/1.50  #Define  : 0
% 3.14/1.50  #Split   : 10
% 3.14/1.50  #Chain   : 0
% 3.14/1.50  #Close   : 0
% 3.14/1.50  
% 3.14/1.50  Ordering : KBO
% 3.14/1.50  
% 3.14/1.50  Simplification rules
% 3.14/1.50  ----------------------
% 3.14/1.50  #Subsume      : 30
% 3.14/1.50  #Demod        : 120
% 3.14/1.50  #Tautology    : 14
% 3.14/1.50  #SimpNegUnit  : 41
% 3.14/1.50  #BackRed      : 21
% 3.14/1.50  
% 3.14/1.50  #Partial instantiations: 0
% 3.14/1.50  #Strategies tried      : 1
% 3.14/1.50  
% 3.14/1.50  Timing (in seconds)
% 3.14/1.50  ----------------------
% 3.14/1.50  Preprocessing        : 0.33
% 3.14/1.50  Parsing              : 0.17
% 3.14/1.50  CNF conversion       : 0.02
% 3.14/1.50  Main loop            : 0.36
% 3.14/1.50  Inferencing          : 0.14
% 3.14/1.50  Reduction            : 0.11
% 3.14/1.50  Demodulation         : 0.07
% 3.14/1.50  BG Simplification    : 0.02
% 3.14/1.50  Subsumption          : 0.06
% 3.14/1.50  Abstraction          : 0.02
% 3.14/1.50  MUC search           : 0.00
% 3.14/1.50  Cooper               : 0.00
% 3.14/1.50  Total                : 0.74
% 3.14/1.50  Index Insertion      : 0.00
% 3.14/1.50  Index Deletion       : 0.00
% 3.14/1.50  Index Matching       : 0.00
% 3.14/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
