%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:03 EST 2020

% Result     : Theorem 2.78s
% Output     : CNFRefutation 2.78s
% Verified   : 
% Statistics : Number of formulae       :  124 ( 658 expanded)
%              Number of leaves         :   33 ( 230 expanded)
%              Depth                    :   14
%              Number of atoms          :  263 (1957 expanded)
%              Number of equality atoms :    7 (  77 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_tex_2 > v1_subset_1 > m1_subset_1 > m1_pre_topc > v7_struct_0 > v2_struct_0 > v1_zfmisc_1 > v1_xboole_0 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k6_domain_1 > k1_tex_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1

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

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_164,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ( v1_tex_2(k1_tex_2(A,B),A)
            <=> v1_subset_1(k6_domain_1(u1_struct_0(A),B),u1_struct_0(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_tex_2)).

tff(f_113,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ( ~ v2_struct_0(k1_tex_2(A,B))
        & v7_struct_0(k1_tex_2(A,B))
        & v1_pre_topc(k1_tex_2(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_tex_2)).

tff(f_29,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_138,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & ~ v1_zfmisc_1(A) )
     => ! [B] :
          ( m1_subset_1(B,A)
         => v1_subset_1(k6_domain_1(A,B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tex_2)).

tff(f_151,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ~ ( v1_subset_1(k6_domain_1(u1_struct_0(A),B),u1_struct_0(A))
              & v7_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_tex_2)).

tff(f_99,axiom,(
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

tff(f_59,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_85,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( v1_subset_1(B,A)
      <=> B != A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).

tff(f_127,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( C = u1_struct_0(B)
               => ( v1_subset_1(C,u1_struct_0(A))
                <=> v1_tex_2(B,A) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_tex_2)).

tff(f_44,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_52,axiom,(
    ! [A] :
      ( ( ~ v7_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_zfmisc_1(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_struct_0)).

tff(f_78,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v7_struct_0(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ( ~ v2_struct_0(B)
           => ( ~ v2_struct_0(B)
              & ~ v1_tex_2(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc10_tex_2)).

tff(c_44,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_42,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_40,plain,(
    m1_subset_1('#skF_2',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_450,plain,(
    ! [A_89,B_90] :
      ( ~ v2_struct_0(k1_tex_2(A_89,B_90))
      | ~ m1_subset_1(B_90,u1_struct_0(A_89))
      | ~ l1_pre_topc(A_89)
      | v2_struct_0(A_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_453,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_450])).

tff(c_456,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_453])).

tff(c_457,plain,(
    ~ v2_struct_0(k1_tex_2('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_456])).

tff(c_2,plain,(
    ! [A_1] :
      ( l1_struct_0(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_423,plain,(
    ! [A_87,B_88] :
      ( v1_subset_1(k6_domain_1(A_87,B_88),A_87)
      | ~ m1_subset_1(B_88,A_87)
      | v1_zfmisc_1(A_87)
      | v1_xboole_0(A_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_46,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0('#skF_1'),'#skF_2'),u1_struct_0('#skF_1'))
    | ~ v1_tex_2(k1_tex_2('#skF_1','#skF_2'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_59,plain,(
    ~ v1_tex_2(k1_tex_2('#skF_1','#skF_2'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_52,plain,
    ( v1_tex_2(k1_tex_2('#skF_1','#skF_2'),'#skF_1')
    | v1_subset_1(k6_domain_1(u1_struct_0('#skF_1'),'#skF_2'),u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_71,plain,(
    v1_subset_1(k6_domain_1(u1_struct_0('#skF_1'),'#skF_2'),u1_struct_0('#skF_1')) ),
    inference(negUnitSimplification,[status(thm)],[c_59,c_52])).

tff(c_111,plain,(
    ! [A_56,B_57] :
      ( ~ v7_struct_0(A_56)
      | ~ v1_subset_1(k6_domain_1(u1_struct_0(A_56),B_57),u1_struct_0(A_56))
      | ~ m1_subset_1(B_57,u1_struct_0(A_56))
      | ~ l1_struct_0(A_56)
      | v2_struct_0(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_118,plain,
    ( ~ v7_struct_0('#skF_1')
    | ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1'))
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_71,c_111])).

tff(c_122,plain,
    ( ~ v7_struct_0('#skF_1')
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_118])).

tff(c_123,plain,
    ( ~ v7_struct_0('#skF_1')
    | ~ l1_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_122])).

tff(c_124,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_123])).

tff(c_127,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_2,c_124])).

tff(c_131,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_127])).

tff(c_132,plain,(
    ~ v7_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_123])).

tff(c_133,plain,(
    l1_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_123])).

tff(c_97,plain,(
    ! [A_52,B_53] :
      ( m1_pre_topc(k1_tex_2(A_52,B_53),A_52)
      | ~ m1_subset_1(B_53,u1_struct_0(A_52))
      | ~ l1_pre_topc(A_52)
      | v2_struct_0(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_99,plain,
    ( m1_pre_topc(k1_tex_2('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_97])).

tff(c_102,plain,
    ( m1_pre_topc(k1_tex_2('#skF_1','#skF_2'),'#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_99])).

tff(c_103,plain,(
    m1_pre_topc(k1_tex_2('#skF_1','#skF_2'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_102])).

tff(c_4,plain,(
    ! [B_4,A_2] :
      ( l1_pre_topc(B_4)
      | ~ m1_pre_topc(B_4,A_2)
      | ~ l1_pre_topc(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_106,plain,
    ( l1_pre_topc(k1_tex_2('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_103,c_4])).

tff(c_109,plain,(
    l1_pre_topc(k1_tex_2('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_106])).

tff(c_80,plain,(
    ! [A_46,B_47] :
      ( ~ v2_struct_0(k1_tex_2(A_46,B_47))
      | ~ m1_subset_1(B_47,u1_struct_0(A_46))
      | ~ l1_pre_topc(A_46)
      | v2_struct_0(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_83,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_80])).

tff(c_86,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_83])).

tff(c_87,plain,(
    ~ v2_struct_0(k1_tex_2('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_86])).

tff(c_60,plain,(
    ! [B_41,A_42] :
      ( m1_subset_1(u1_struct_0(B_41),k1_zfmisc_1(u1_struct_0(A_42)))
      | ~ m1_pre_topc(B_41,A_42)
      | ~ l1_pre_topc(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_16,plain,(
    ! [B_14,A_13] :
      ( v1_subset_1(B_14,A_13)
      | B_14 = A_13
      | ~ m1_subset_1(B_14,k1_zfmisc_1(A_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_68,plain,(
    ! [B_41,A_42] :
      ( v1_subset_1(u1_struct_0(B_41),u1_struct_0(A_42))
      | u1_struct_0(B_41) = u1_struct_0(A_42)
      | ~ m1_pre_topc(B_41,A_42)
      | ~ l1_pre_topc(A_42) ) ),
    inference(resolution,[status(thm)],[c_60,c_16])).

tff(c_10,plain,(
    ! [B_9,A_7] :
      ( m1_subset_1(u1_struct_0(B_9),k1_zfmisc_1(u1_struct_0(A_7)))
      | ~ m1_pre_topc(B_9,A_7)
      | ~ l1_pre_topc(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_149,plain,(
    ! [B_62,A_63] :
      ( v1_tex_2(B_62,A_63)
      | ~ v1_subset_1(u1_struct_0(B_62),u1_struct_0(A_63))
      | ~ m1_subset_1(u1_struct_0(B_62),k1_zfmisc_1(u1_struct_0(A_63)))
      | ~ m1_pre_topc(B_62,A_63)
      | ~ l1_pre_topc(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_154,plain,(
    ! [B_64,A_65] :
      ( v1_tex_2(B_64,A_65)
      | ~ v1_subset_1(u1_struct_0(B_64),u1_struct_0(A_65))
      | ~ m1_pre_topc(B_64,A_65)
      | ~ l1_pre_topc(A_65) ) ),
    inference(resolution,[status(thm)],[c_10,c_149])).

tff(c_159,plain,(
    ! [B_66,A_67] :
      ( v1_tex_2(B_66,A_67)
      | u1_struct_0(B_66) = u1_struct_0(A_67)
      | ~ m1_pre_topc(B_66,A_67)
      | ~ l1_pre_topc(A_67) ) ),
    inference(resolution,[status(thm)],[c_68,c_154])).

tff(c_165,plain,
    ( u1_struct_0(k1_tex_2('#skF_1','#skF_2')) = u1_struct_0('#skF_1')
    | ~ m1_pre_topc(k1_tex_2('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_159,c_59])).

tff(c_169,plain,(
    u1_struct_0(k1_tex_2('#skF_1','#skF_2')) = u1_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_103,c_165])).

tff(c_6,plain,(
    ! [A_5] :
      ( ~ v1_xboole_0(u1_struct_0(A_5))
      | ~ l1_struct_0(A_5)
      | v2_struct_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_228,plain,
    ( ~ v1_xboole_0(u1_struct_0('#skF_1'))
    | ~ l1_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | v2_struct_0(k1_tex_2('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_169,c_6])).

tff(c_269,plain,
    ( ~ v1_xboole_0(u1_struct_0('#skF_1'))
    | ~ l1_struct_0(k1_tex_2('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_87,c_228])).

tff(c_272,plain,(
    ~ l1_struct_0(k1_tex_2('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_269])).

tff(c_275,plain,(
    ~ l1_pre_topc(k1_tex_2('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_2,c_272])).

tff(c_279,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_275])).

tff(c_280,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_269])).

tff(c_281,plain,(
    l1_struct_0(k1_tex_2('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_269])).

tff(c_72,plain,(
    ! [A_44,B_45] :
      ( v7_struct_0(k1_tex_2(A_44,B_45))
      | ~ m1_subset_1(B_45,u1_struct_0(A_44))
      | ~ l1_pre_topc(A_44)
      | v2_struct_0(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_75,plain,
    ( v7_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_72])).

tff(c_78,plain,
    ( v7_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_75])).

tff(c_79,plain,(
    v7_struct_0(k1_tex_2('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_78])).

tff(c_36,plain,(
    ! [A_26,B_28] :
      ( v1_subset_1(k6_domain_1(A_26,B_28),A_26)
      | ~ m1_subset_1(B_28,A_26)
      | v1_zfmisc_1(A_26)
      | v1_xboole_0(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_119,plain,(
    ! [A_56,B_28] :
      ( ~ v7_struct_0(A_56)
      | ~ l1_struct_0(A_56)
      | v2_struct_0(A_56)
      | ~ m1_subset_1(B_28,u1_struct_0(A_56))
      | v1_zfmisc_1(u1_struct_0(A_56))
      | v1_xboole_0(u1_struct_0(A_56)) ) ),
    inference(resolution,[status(thm)],[c_36,c_111])).

tff(c_190,plain,(
    ! [B_28] :
      ( ~ v7_struct_0(k1_tex_2('#skF_1','#skF_2'))
      | ~ l1_struct_0(k1_tex_2('#skF_1','#skF_2'))
      | v2_struct_0(k1_tex_2('#skF_1','#skF_2'))
      | ~ m1_subset_1(B_28,u1_struct_0('#skF_1'))
      | v1_zfmisc_1(u1_struct_0(k1_tex_2('#skF_1','#skF_2')))
      | v1_xboole_0(u1_struct_0(k1_tex_2('#skF_1','#skF_2'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_169,c_119])).

tff(c_240,plain,(
    ! [B_28] :
      ( ~ l1_struct_0(k1_tex_2('#skF_1','#skF_2'))
      | v2_struct_0(k1_tex_2('#skF_1','#skF_2'))
      | ~ m1_subset_1(B_28,u1_struct_0('#skF_1'))
      | v1_zfmisc_1(u1_struct_0('#skF_1'))
      | v1_xboole_0(u1_struct_0('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_169,c_169,c_79,c_190])).

tff(c_241,plain,(
    ! [B_28] :
      ( ~ l1_struct_0(k1_tex_2('#skF_1','#skF_2'))
      | ~ m1_subset_1(B_28,u1_struct_0('#skF_1'))
      | v1_zfmisc_1(u1_struct_0('#skF_1'))
      | v1_xboole_0(u1_struct_0('#skF_1')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_87,c_240])).

tff(c_386,plain,(
    ! [B_28] :
      ( ~ m1_subset_1(B_28,u1_struct_0('#skF_1'))
      | v1_zfmisc_1(u1_struct_0('#skF_1'))
      | v1_xboole_0(u1_struct_0('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_281,c_241])).

tff(c_387,plain,(
    ! [B_28] :
      ( ~ m1_subset_1(B_28,u1_struct_0('#skF_1'))
      | v1_zfmisc_1(u1_struct_0('#skF_1')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_280,c_386])).

tff(c_388,plain,(
    ! [B_28] : ~ m1_subset_1(B_28,u1_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_387])).

tff(c_390,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_388,c_40])).

tff(c_391,plain,(
    v1_zfmisc_1(u1_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_387])).

tff(c_8,plain,(
    ! [A_6] :
      ( ~ v1_zfmisc_1(u1_struct_0(A_6))
      | ~ l1_struct_0(A_6)
      | v7_struct_0(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_394,plain,
    ( ~ l1_struct_0('#skF_1')
    | v7_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_391,c_8])).

tff(c_397,plain,(
    v7_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_394])).

tff(c_399,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_132,c_397])).

tff(c_400,plain,(
    ~ v1_subset_1(k6_domain_1(u1_struct_0('#skF_1'),'#skF_2'),u1_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_426,plain,
    ( ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1'))
    | v1_zfmisc_1(u1_struct_0('#skF_1'))
    | v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_423,c_400])).

tff(c_429,plain,
    ( v1_zfmisc_1(u1_struct_0('#skF_1'))
    | v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_426])).

tff(c_430,plain,(
    v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_429])).

tff(c_433,plain,
    ( ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_430,c_6])).

tff(c_436,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_433])).

tff(c_439,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_2,c_436])).

tff(c_443,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_439])).

tff(c_444,plain,(
    v1_zfmisc_1(u1_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_429])).

tff(c_449,plain,
    ( ~ l1_struct_0('#skF_1')
    | v7_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_444,c_8])).

tff(c_458,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_449])).

tff(c_461,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_2,c_458])).

tff(c_465,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_461])).

tff(c_466,plain,(
    v7_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_449])).

tff(c_476,plain,(
    ! [A_93,B_94] :
      ( m1_pre_topc(k1_tex_2(A_93,B_94),A_93)
      | ~ m1_subset_1(B_94,u1_struct_0(A_93))
      | ~ l1_pre_topc(A_93)
      | v2_struct_0(A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_478,plain,
    ( m1_pre_topc(k1_tex_2('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_476])).

tff(c_481,plain,
    ( m1_pre_topc(k1_tex_2('#skF_1','#skF_2'),'#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_478])).

tff(c_482,plain,(
    m1_pre_topc(k1_tex_2('#skF_1','#skF_2'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_481])).

tff(c_401,plain,(
    v1_tex_2(k1_tex_2('#skF_1','#skF_2'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_489,plain,(
    ! [B_95,A_96] :
      ( ~ v1_tex_2(B_95,A_96)
      | v2_struct_0(B_95)
      | ~ m1_pre_topc(B_95,A_96)
      | ~ l1_pre_topc(A_96)
      | ~ v7_struct_0(A_96)
      | v2_struct_0(A_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_492,plain,
    ( v2_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | ~ m1_pre_topc(k1_tex_2('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v7_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_401,c_489])).

tff(c_495,plain,
    ( v2_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_466,c_42,c_482,c_492])).

tff(c_497,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_457,c_495])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:04:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.78/1.39  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.78/1.41  
% 2.78/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.78/1.41  %$ v1_tex_2 > v1_subset_1 > m1_subset_1 > m1_pre_topc > v7_struct_0 > v2_struct_0 > v1_zfmisc_1 > v1_xboole_0 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k6_domain_1 > k1_tex_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1
% 2.78/1.41  
% 2.78/1.41  %Foreground sorts:
% 2.78/1.41  
% 2.78/1.41  
% 2.78/1.41  %Background operators:
% 2.78/1.41  
% 2.78/1.41  
% 2.78/1.41  %Foreground operators:
% 2.78/1.41  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.78/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.78/1.41  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 2.78/1.41  tff(v1_tex_2, type, v1_tex_2: ($i * $i) > $o).
% 2.78/1.41  tff(v7_struct_0, type, v7_struct_0: $i > $o).
% 2.78/1.41  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.78/1.41  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.78/1.41  tff('#skF_2', type, '#skF_2': $i).
% 2.78/1.41  tff('#skF_1', type, '#skF_1': $i).
% 2.78/1.41  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 2.78/1.41  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.78/1.41  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.78/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.78/1.41  tff(k1_tex_2, type, k1_tex_2: ($i * $i) > $i).
% 2.78/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.78/1.41  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 2.78/1.41  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.78/1.41  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.78/1.41  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.78/1.41  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.78/1.41  
% 2.78/1.44  tff(f_164, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (v1_tex_2(k1_tex_2(A, B), A) <=> v1_subset_1(k6_domain_1(u1_struct_0(A), B), u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_tex_2)).
% 2.78/1.44  tff(f_113, axiom, (![A, B]: (((~v2_struct_0(A) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => ((~v2_struct_0(k1_tex_2(A, B)) & v7_struct_0(k1_tex_2(A, B))) & v1_pre_topc(k1_tex_2(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_tex_2)).
% 2.78/1.44  tff(f_29, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.78/1.44  tff(f_138, axiom, (![A]: ((~v1_xboole_0(A) & ~v1_zfmisc_1(A)) => (![B]: (m1_subset_1(B, A) => v1_subset_1(k6_domain_1(A, B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_tex_2)).
% 2.78/1.44  tff(f_151, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => ~(v1_subset_1(k6_domain_1(u1_struct_0(A), B), u1_struct_0(A)) & v7_struct_0(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_tex_2)).
% 2.78/1.44  tff(f_99, axiom, (![A, B]: (((~v2_struct_0(A) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => ((~v2_struct_0(k1_tex_2(A, B)) & v1_pre_topc(k1_tex_2(A, B))) & m1_pre_topc(k1_tex_2(A, B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tex_2)).
% 2.78/1.44  tff(f_36, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 2.78/1.44  tff(f_59, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 2.78/1.44  tff(f_85, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (v1_subset_1(B, A) <=> ~(B = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_subset_1)).
% 2.78/1.44  tff(f_127, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => (v1_subset_1(C, u1_struct_0(A)) <=> v1_tex_2(B, A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_tex_2)).
% 2.78/1.44  tff(f_44, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 2.78/1.44  tff(f_52, axiom, (![A]: ((~v7_struct_0(A) & l1_struct_0(A)) => ~v1_zfmisc_1(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_struct_0)).
% 2.78/1.44  tff(f_78, axiom, (![A]: (((~v2_struct_0(A) & v7_struct_0(A)) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (~v2_struct_0(B) => (~v2_struct_0(B) & ~v1_tex_2(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc10_tex_2)).
% 2.78/1.44  tff(c_44, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_164])).
% 2.78/1.44  tff(c_42, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_164])).
% 2.78/1.44  tff(c_40, plain, (m1_subset_1('#skF_2', u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_164])).
% 2.78/1.44  tff(c_450, plain, (![A_89, B_90]: (~v2_struct_0(k1_tex_2(A_89, B_90)) | ~m1_subset_1(B_90, u1_struct_0(A_89)) | ~l1_pre_topc(A_89) | v2_struct_0(A_89))), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.78/1.44  tff(c_453, plain, (~v2_struct_0(k1_tex_2('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_40, c_450])).
% 2.78/1.44  tff(c_456, plain, (~v2_struct_0(k1_tex_2('#skF_1', '#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_453])).
% 2.78/1.44  tff(c_457, plain, (~v2_struct_0(k1_tex_2('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_44, c_456])).
% 2.78/1.44  tff(c_2, plain, (![A_1]: (l1_struct_0(A_1) | ~l1_pre_topc(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.78/1.44  tff(c_423, plain, (![A_87, B_88]: (v1_subset_1(k6_domain_1(A_87, B_88), A_87) | ~m1_subset_1(B_88, A_87) | v1_zfmisc_1(A_87) | v1_xboole_0(A_87))), inference(cnfTransformation, [status(thm)], [f_138])).
% 2.78/1.44  tff(c_46, plain, (~v1_subset_1(k6_domain_1(u1_struct_0('#skF_1'), '#skF_2'), u1_struct_0('#skF_1')) | ~v1_tex_2(k1_tex_2('#skF_1', '#skF_2'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_164])).
% 2.78/1.44  tff(c_59, plain, (~v1_tex_2(k1_tex_2('#skF_1', '#skF_2'), '#skF_1')), inference(splitLeft, [status(thm)], [c_46])).
% 2.78/1.44  tff(c_52, plain, (v1_tex_2(k1_tex_2('#skF_1', '#skF_2'), '#skF_1') | v1_subset_1(k6_domain_1(u1_struct_0('#skF_1'), '#skF_2'), u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_164])).
% 2.78/1.44  tff(c_71, plain, (v1_subset_1(k6_domain_1(u1_struct_0('#skF_1'), '#skF_2'), u1_struct_0('#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_59, c_52])).
% 2.78/1.44  tff(c_111, plain, (![A_56, B_57]: (~v7_struct_0(A_56) | ~v1_subset_1(k6_domain_1(u1_struct_0(A_56), B_57), u1_struct_0(A_56)) | ~m1_subset_1(B_57, u1_struct_0(A_56)) | ~l1_struct_0(A_56) | v2_struct_0(A_56))), inference(cnfTransformation, [status(thm)], [f_151])).
% 2.78/1.44  tff(c_118, plain, (~v7_struct_0('#skF_1') | ~m1_subset_1('#skF_2', u1_struct_0('#skF_1')) | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_71, c_111])).
% 2.78/1.44  tff(c_122, plain, (~v7_struct_0('#skF_1') | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_118])).
% 2.78/1.44  tff(c_123, plain, (~v7_struct_0('#skF_1') | ~l1_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_44, c_122])).
% 2.78/1.44  tff(c_124, plain, (~l1_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_123])).
% 2.78/1.44  tff(c_127, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_2, c_124])).
% 2.78/1.44  tff(c_131, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_127])).
% 2.78/1.44  tff(c_132, plain, (~v7_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_123])).
% 2.78/1.44  tff(c_133, plain, (l1_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_123])).
% 2.78/1.44  tff(c_97, plain, (![A_52, B_53]: (m1_pre_topc(k1_tex_2(A_52, B_53), A_52) | ~m1_subset_1(B_53, u1_struct_0(A_52)) | ~l1_pre_topc(A_52) | v2_struct_0(A_52))), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.78/1.44  tff(c_99, plain, (m1_pre_topc(k1_tex_2('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_40, c_97])).
% 2.78/1.44  tff(c_102, plain, (m1_pre_topc(k1_tex_2('#skF_1', '#skF_2'), '#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_99])).
% 2.78/1.44  tff(c_103, plain, (m1_pre_topc(k1_tex_2('#skF_1', '#skF_2'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_44, c_102])).
% 2.78/1.44  tff(c_4, plain, (![B_4, A_2]: (l1_pre_topc(B_4) | ~m1_pre_topc(B_4, A_2) | ~l1_pre_topc(A_2))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.78/1.44  tff(c_106, plain, (l1_pre_topc(k1_tex_2('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_103, c_4])).
% 2.78/1.44  tff(c_109, plain, (l1_pre_topc(k1_tex_2('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_106])).
% 2.78/1.44  tff(c_80, plain, (![A_46, B_47]: (~v2_struct_0(k1_tex_2(A_46, B_47)) | ~m1_subset_1(B_47, u1_struct_0(A_46)) | ~l1_pre_topc(A_46) | v2_struct_0(A_46))), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.78/1.44  tff(c_83, plain, (~v2_struct_0(k1_tex_2('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_40, c_80])).
% 2.78/1.44  tff(c_86, plain, (~v2_struct_0(k1_tex_2('#skF_1', '#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_83])).
% 2.78/1.44  tff(c_87, plain, (~v2_struct_0(k1_tex_2('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_44, c_86])).
% 2.78/1.44  tff(c_60, plain, (![B_41, A_42]: (m1_subset_1(u1_struct_0(B_41), k1_zfmisc_1(u1_struct_0(A_42))) | ~m1_pre_topc(B_41, A_42) | ~l1_pre_topc(A_42))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.78/1.44  tff(c_16, plain, (![B_14, A_13]: (v1_subset_1(B_14, A_13) | B_14=A_13 | ~m1_subset_1(B_14, k1_zfmisc_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.78/1.44  tff(c_68, plain, (![B_41, A_42]: (v1_subset_1(u1_struct_0(B_41), u1_struct_0(A_42)) | u1_struct_0(B_41)=u1_struct_0(A_42) | ~m1_pre_topc(B_41, A_42) | ~l1_pre_topc(A_42))), inference(resolution, [status(thm)], [c_60, c_16])).
% 2.78/1.44  tff(c_10, plain, (![B_9, A_7]: (m1_subset_1(u1_struct_0(B_9), k1_zfmisc_1(u1_struct_0(A_7))) | ~m1_pre_topc(B_9, A_7) | ~l1_pre_topc(A_7))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.78/1.44  tff(c_149, plain, (![B_62, A_63]: (v1_tex_2(B_62, A_63) | ~v1_subset_1(u1_struct_0(B_62), u1_struct_0(A_63)) | ~m1_subset_1(u1_struct_0(B_62), k1_zfmisc_1(u1_struct_0(A_63))) | ~m1_pre_topc(B_62, A_63) | ~l1_pre_topc(A_63))), inference(cnfTransformation, [status(thm)], [f_127])).
% 2.78/1.44  tff(c_154, plain, (![B_64, A_65]: (v1_tex_2(B_64, A_65) | ~v1_subset_1(u1_struct_0(B_64), u1_struct_0(A_65)) | ~m1_pre_topc(B_64, A_65) | ~l1_pre_topc(A_65))), inference(resolution, [status(thm)], [c_10, c_149])).
% 2.78/1.44  tff(c_159, plain, (![B_66, A_67]: (v1_tex_2(B_66, A_67) | u1_struct_0(B_66)=u1_struct_0(A_67) | ~m1_pre_topc(B_66, A_67) | ~l1_pre_topc(A_67))), inference(resolution, [status(thm)], [c_68, c_154])).
% 2.78/1.44  tff(c_165, plain, (u1_struct_0(k1_tex_2('#skF_1', '#skF_2'))=u1_struct_0('#skF_1') | ~m1_pre_topc(k1_tex_2('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_159, c_59])).
% 2.78/1.44  tff(c_169, plain, (u1_struct_0(k1_tex_2('#skF_1', '#skF_2'))=u1_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_103, c_165])).
% 2.78/1.44  tff(c_6, plain, (![A_5]: (~v1_xboole_0(u1_struct_0(A_5)) | ~l1_struct_0(A_5) | v2_struct_0(A_5))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.78/1.44  tff(c_228, plain, (~v1_xboole_0(u1_struct_0('#skF_1')) | ~l1_struct_0(k1_tex_2('#skF_1', '#skF_2')) | v2_struct_0(k1_tex_2('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_169, c_6])).
% 2.78/1.44  tff(c_269, plain, (~v1_xboole_0(u1_struct_0('#skF_1')) | ~l1_struct_0(k1_tex_2('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_87, c_228])).
% 2.78/1.44  tff(c_272, plain, (~l1_struct_0(k1_tex_2('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_269])).
% 2.78/1.44  tff(c_275, plain, (~l1_pre_topc(k1_tex_2('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_2, c_272])).
% 2.78/1.44  tff(c_279, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_109, c_275])).
% 2.78/1.44  tff(c_280, plain, (~v1_xboole_0(u1_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_269])).
% 2.78/1.44  tff(c_281, plain, (l1_struct_0(k1_tex_2('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_269])).
% 2.78/1.44  tff(c_72, plain, (![A_44, B_45]: (v7_struct_0(k1_tex_2(A_44, B_45)) | ~m1_subset_1(B_45, u1_struct_0(A_44)) | ~l1_pre_topc(A_44) | v2_struct_0(A_44))), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.78/1.44  tff(c_75, plain, (v7_struct_0(k1_tex_2('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_40, c_72])).
% 2.78/1.44  tff(c_78, plain, (v7_struct_0(k1_tex_2('#skF_1', '#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_75])).
% 2.78/1.44  tff(c_79, plain, (v7_struct_0(k1_tex_2('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_44, c_78])).
% 2.78/1.44  tff(c_36, plain, (![A_26, B_28]: (v1_subset_1(k6_domain_1(A_26, B_28), A_26) | ~m1_subset_1(B_28, A_26) | v1_zfmisc_1(A_26) | v1_xboole_0(A_26))), inference(cnfTransformation, [status(thm)], [f_138])).
% 2.78/1.44  tff(c_119, plain, (![A_56, B_28]: (~v7_struct_0(A_56) | ~l1_struct_0(A_56) | v2_struct_0(A_56) | ~m1_subset_1(B_28, u1_struct_0(A_56)) | v1_zfmisc_1(u1_struct_0(A_56)) | v1_xboole_0(u1_struct_0(A_56)))), inference(resolution, [status(thm)], [c_36, c_111])).
% 2.78/1.44  tff(c_190, plain, (![B_28]: (~v7_struct_0(k1_tex_2('#skF_1', '#skF_2')) | ~l1_struct_0(k1_tex_2('#skF_1', '#skF_2')) | v2_struct_0(k1_tex_2('#skF_1', '#skF_2')) | ~m1_subset_1(B_28, u1_struct_0('#skF_1')) | v1_zfmisc_1(u1_struct_0(k1_tex_2('#skF_1', '#skF_2'))) | v1_xboole_0(u1_struct_0(k1_tex_2('#skF_1', '#skF_2'))))), inference(superposition, [status(thm), theory('equality')], [c_169, c_119])).
% 2.78/1.44  tff(c_240, plain, (![B_28]: (~l1_struct_0(k1_tex_2('#skF_1', '#skF_2')) | v2_struct_0(k1_tex_2('#skF_1', '#skF_2')) | ~m1_subset_1(B_28, u1_struct_0('#skF_1')) | v1_zfmisc_1(u1_struct_0('#skF_1')) | v1_xboole_0(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_169, c_169, c_79, c_190])).
% 2.78/1.44  tff(c_241, plain, (![B_28]: (~l1_struct_0(k1_tex_2('#skF_1', '#skF_2')) | ~m1_subset_1(B_28, u1_struct_0('#skF_1')) | v1_zfmisc_1(u1_struct_0('#skF_1')) | v1_xboole_0(u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_87, c_240])).
% 2.78/1.44  tff(c_386, plain, (![B_28]: (~m1_subset_1(B_28, u1_struct_0('#skF_1')) | v1_zfmisc_1(u1_struct_0('#skF_1')) | v1_xboole_0(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_281, c_241])).
% 2.78/1.44  tff(c_387, plain, (![B_28]: (~m1_subset_1(B_28, u1_struct_0('#skF_1')) | v1_zfmisc_1(u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_280, c_386])).
% 2.78/1.44  tff(c_388, plain, (![B_28]: (~m1_subset_1(B_28, u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_387])).
% 2.78/1.44  tff(c_390, plain, $false, inference(negUnitSimplification, [status(thm)], [c_388, c_40])).
% 2.78/1.44  tff(c_391, plain, (v1_zfmisc_1(u1_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_387])).
% 2.78/1.44  tff(c_8, plain, (![A_6]: (~v1_zfmisc_1(u1_struct_0(A_6)) | ~l1_struct_0(A_6) | v7_struct_0(A_6))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.78/1.44  tff(c_394, plain, (~l1_struct_0('#skF_1') | v7_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_391, c_8])).
% 2.78/1.44  tff(c_397, plain, (v7_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_133, c_394])).
% 2.78/1.44  tff(c_399, plain, $false, inference(negUnitSimplification, [status(thm)], [c_132, c_397])).
% 2.78/1.44  tff(c_400, plain, (~v1_subset_1(k6_domain_1(u1_struct_0('#skF_1'), '#skF_2'), u1_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_46])).
% 2.78/1.44  tff(c_426, plain, (~m1_subset_1('#skF_2', u1_struct_0('#skF_1')) | v1_zfmisc_1(u1_struct_0('#skF_1')) | v1_xboole_0(u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_423, c_400])).
% 2.78/1.44  tff(c_429, plain, (v1_zfmisc_1(u1_struct_0('#skF_1')) | v1_xboole_0(u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_426])).
% 2.78/1.44  tff(c_430, plain, (v1_xboole_0(u1_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_429])).
% 2.78/1.44  tff(c_433, plain, (~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_430, c_6])).
% 2.78/1.44  tff(c_436, plain, (~l1_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_44, c_433])).
% 2.78/1.44  tff(c_439, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_2, c_436])).
% 2.78/1.44  tff(c_443, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_439])).
% 2.78/1.44  tff(c_444, plain, (v1_zfmisc_1(u1_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_429])).
% 2.78/1.44  tff(c_449, plain, (~l1_struct_0('#skF_1') | v7_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_444, c_8])).
% 2.78/1.44  tff(c_458, plain, (~l1_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_449])).
% 2.78/1.44  tff(c_461, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_2, c_458])).
% 2.78/1.44  tff(c_465, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_461])).
% 2.78/1.44  tff(c_466, plain, (v7_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_449])).
% 2.78/1.44  tff(c_476, plain, (![A_93, B_94]: (m1_pre_topc(k1_tex_2(A_93, B_94), A_93) | ~m1_subset_1(B_94, u1_struct_0(A_93)) | ~l1_pre_topc(A_93) | v2_struct_0(A_93))), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.78/1.44  tff(c_478, plain, (m1_pre_topc(k1_tex_2('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_40, c_476])).
% 2.78/1.44  tff(c_481, plain, (m1_pre_topc(k1_tex_2('#skF_1', '#skF_2'), '#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_478])).
% 2.78/1.44  tff(c_482, plain, (m1_pre_topc(k1_tex_2('#skF_1', '#skF_2'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_44, c_481])).
% 2.78/1.44  tff(c_401, plain, (v1_tex_2(k1_tex_2('#skF_1', '#skF_2'), '#skF_1')), inference(splitRight, [status(thm)], [c_46])).
% 2.78/1.44  tff(c_489, plain, (![B_95, A_96]: (~v1_tex_2(B_95, A_96) | v2_struct_0(B_95) | ~m1_pre_topc(B_95, A_96) | ~l1_pre_topc(A_96) | ~v7_struct_0(A_96) | v2_struct_0(A_96))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.78/1.44  tff(c_492, plain, (v2_struct_0(k1_tex_2('#skF_1', '#skF_2')) | ~m1_pre_topc(k1_tex_2('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v7_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_401, c_489])).
% 2.78/1.44  tff(c_495, plain, (v2_struct_0(k1_tex_2('#skF_1', '#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_466, c_42, c_482, c_492])).
% 2.78/1.44  tff(c_497, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_457, c_495])).
% 2.78/1.44  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.78/1.44  
% 2.78/1.44  Inference rules
% 2.78/1.44  ----------------------
% 2.78/1.44  #Ref     : 0
% 2.78/1.44  #Sup     : 70
% 2.78/1.44  #Fact    : 0
% 2.78/1.44  #Define  : 0
% 2.78/1.44  #Split   : 9
% 2.78/1.44  #Chain   : 0
% 2.78/1.44  #Close   : 0
% 2.78/1.44  
% 2.78/1.44  Ordering : KBO
% 2.78/1.44  
% 2.78/1.44  Simplification rules
% 2.78/1.44  ----------------------
% 2.78/1.44  #Subsume      : 13
% 2.78/1.44  #Demod        : 64
% 2.78/1.44  #Tautology    : 11
% 2.78/1.44  #SimpNegUnit  : 27
% 2.78/1.44  #BackRed      : 1
% 2.78/1.44  
% 2.78/1.44  #Partial instantiations: 0
% 2.78/1.44  #Strategies tried      : 1
% 2.78/1.44  
% 2.78/1.44  Timing (in seconds)
% 2.78/1.44  ----------------------
% 2.78/1.45  Preprocessing        : 0.33
% 2.78/1.45  Parsing              : 0.18
% 2.78/1.45  CNF conversion       : 0.02
% 2.78/1.45  Main loop            : 0.31
% 2.78/1.45  Inferencing          : 0.12
% 2.78/1.45  Reduction            : 0.09
% 2.78/1.45  Demodulation         : 0.06
% 2.78/1.45  BG Simplification    : 0.02
% 2.78/1.45  Subsumption          : 0.06
% 2.78/1.45  Abstraction          : 0.01
% 2.78/1.45  MUC search           : 0.00
% 2.78/1.45  Cooper               : 0.00
% 2.78/1.45  Total                : 0.70
% 2.78/1.45  Index Insertion      : 0.00
% 2.78/1.45  Index Deletion       : 0.00
% 2.78/1.45  Index Matching       : 0.00
% 2.78/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
