%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:01 EST 2020

% Result     : Theorem 2.76s
% Output     : CNFRefutation 2.76s
% Verified   : 
% Statistics : Number of formulae       :  130 ( 767 expanded)
%              Number of leaves         :   33 ( 267 expanded)
%              Depth                    :   14
%              Number of atoms          :  293 (2295 expanded)
%              Number of equality atoms :   12 ( 126 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

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

tff(f_153,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ( v1_tex_2(k1_tex_2(A,B),A)
            <=> v1_subset_1(k6_domain_1(u1_struct_0(A),B),u1_struct_0(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_tex_2)).

tff(f_116,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ( ~ v2_struct_0(k1_tex_2(A,B))
        & v7_struct_0(k1_tex_2(A,B))
        & v1_pre_topc(k1_tex_2(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_tex_2)).

tff(f_33,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_127,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & ~ v1_zfmisc_1(A) )
     => ! [B] :
          ( m1_subset_1(B,A)
         => v1_subset_1(k6_domain_1(A,B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tex_2)).

tff(f_102,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ( ~ v2_struct_0(k1_tex_2(A,B))
        & v1_pre_topc(k1_tex_2(A,B))
        & m1_pre_topc(k1_tex_2(A,B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tex_2)).

tff(f_40,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_81,axiom,(
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

tff(f_88,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( v1_subset_1(B,A)
      <=> B != A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).

tff(f_140,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ~ ( v1_subset_1(k6_domain_1(u1_struct_0(A),B),u1_struct_0(A))
              & v7_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_tex_2)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_zfmisc_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_zfmisc_1)).

tff(f_48,axiom,(
    ! [A] :
      ( ( ~ v7_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_zfmisc_1(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_struct_0)).

tff(f_67,axiom,(
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

tff(c_46,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_44,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_42,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_565,plain,(
    ! [A_103,B_104] :
      ( ~ v2_struct_0(k1_tex_2(A_103,B_104))
      | ~ m1_subset_1(B_104,u1_struct_0(A_103))
      | ~ l1_pre_topc(A_103)
      | v2_struct_0(A_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_568,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_565])).

tff(c_571,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_568])).

tff(c_572,plain,(
    ~ v2_struct_0(k1_tex_2('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_571])).

tff(c_4,plain,(
    ! [A_2] :
      ( l1_struct_0(A_2)
      | ~ l1_pre_topc(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_506,plain,(
    ! [A_93,B_94] :
      ( ~ v2_struct_0(k1_tex_2(A_93,B_94))
      | ~ m1_subset_1(B_94,u1_struct_0(A_93))
      | ~ l1_pre_topc(A_93)
      | v2_struct_0(A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_509,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_506])).

tff(c_512,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_509])).

tff(c_513,plain,(
    ~ v2_struct_0(k1_tex_2('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_512])).

tff(c_476,plain,(
    ! [A_89,B_90] :
      ( v1_subset_1(k6_domain_1(A_89,B_90),A_89)
      | ~ m1_subset_1(B_90,A_89)
      | v1_zfmisc_1(A_89)
      | v1_xboole_0(A_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_54,plain,
    ( v1_tex_2(k1_tex_2('#skF_2','#skF_3'),'#skF_2')
    | v1_subset_1(k6_domain_1(u1_struct_0('#skF_2'),'#skF_3'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_65,plain,(
    v1_subset_1(k6_domain_1(u1_struct_0('#skF_2'),'#skF_3'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_101,plain,(
    ! [A_52,B_53] :
      ( m1_pre_topc(k1_tex_2(A_52,B_53),A_52)
      | ~ m1_subset_1(B_53,u1_struct_0(A_52))
      | ~ l1_pre_topc(A_52)
      | v2_struct_0(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_103,plain,
    ( m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_101])).

tff(c_106,plain,
    ( m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_103])).

tff(c_107,plain,(
    m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_106])).

tff(c_6,plain,(
    ! [B_5,A_3] :
      ( l1_pre_topc(B_5)
      | ~ m1_pre_topc(B_5,A_3)
      | ~ l1_pre_topc(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_110,plain,
    ( l1_pre_topc(k1_tex_2('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_107,c_6])).

tff(c_113,plain,(
    l1_pre_topc(k1_tex_2('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_110])).

tff(c_77,plain,(
    ! [A_44,B_45] :
      ( ~ v2_struct_0(k1_tex_2(A_44,B_45))
      | ~ m1_subset_1(B_45,u1_struct_0(A_44))
      | ~ l1_pre_topc(A_44)
      | v2_struct_0(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_80,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_77])).

tff(c_83,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_80])).

tff(c_84,plain,(
    ~ v2_struct_0(k1_tex_2('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_83])).

tff(c_165,plain,(
    ! [A_61,B_62] :
      ( m1_subset_1('#skF_1'(A_61,B_62),k1_zfmisc_1(u1_struct_0(A_61)))
      | v1_tex_2(B_62,A_61)
      | ~ m1_pre_topc(B_62,A_61)
      | ~ l1_pre_topc(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_22,plain,(
    ! [B_21,A_20] :
      ( v1_subset_1(B_21,A_20)
      | B_21 = A_20
      | ~ m1_subset_1(B_21,k1_zfmisc_1(A_20)) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_257,plain,(
    ! [A_73,B_74] :
      ( v1_subset_1('#skF_1'(A_73,B_74),u1_struct_0(A_73))
      | u1_struct_0(A_73) = '#skF_1'(A_73,B_74)
      | v1_tex_2(B_74,A_73)
      | ~ m1_pre_topc(B_74,A_73)
      | ~ l1_pre_topc(A_73) ) ),
    inference(resolution,[status(thm)],[c_165,c_22])).

tff(c_16,plain,(
    ! [A_10,B_16] :
      ( ~ v1_subset_1('#skF_1'(A_10,B_16),u1_struct_0(A_10))
      | v1_tex_2(B_16,A_10)
      | ~ m1_pre_topc(B_16,A_10)
      | ~ l1_pre_topc(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_267,plain,(
    ! [A_75,B_76] :
      ( u1_struct_0(A_75) = '#skF_1'(A_75,B_76)
      | v1_tex_2(B_76,A_75)
      | ~ m1_pre_topc(B_76,A_75)
      | ~ l1_pre_topc(A_75) ) ),
    inference(resolution,[status(thm)],[c_257,c_16])).

tff(c_48,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0('#skF_2'),'#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_tex_2(k1_tex_2('#skF_2','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_76,plain,(
    ~ v1_tex_2(k1_tex_2('#skF_2','#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_48])).

tff(c_273,plain,
    ( '#skF_1'('#skF_2',k1_tex_2('#skF_2','#skF_3')) = u1_struct_0('#skF_2')
    | ~ m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_267,c_76])).

tff(c_277,plain,(
    '#skF_1'('#skF_2',k1_tex_2('#skF_2','#skF_3')) = u1_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_107,c_273])).

tff(c_94,plain,(
    ! [B_50,A_51] :
      ( u1_struct_0(B_50) = '#skF_1'(A_51,B_50)
      | v1_tex_2(B_50,A_51)
      | ~ m1_pre_topc(B_50,A_51)
      | ~ l1_pre_topc(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_97,plain,
    ( u1_struct_0(k1_tex_2('#skF_2','#skF_3')) = '#skF_1'('#skF_2',k1_tex_2('#skF_2','#skF_3'))
    | ~ m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_94,c_76])).

tff(c_100,plain,
    ( u1_struct_0(k1_tex_2('#skF_2','#skF_3')) = '#skF_1'('#skF_2',k1_tex_2('#skF_2','#skF_3'))
    | ~ m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_97])).

tff(c_121,plain,(
    u1_struct_0(k1_tex_2('#skF_2','#skF_3')) = '#skF_1'('#skF_2',k1_tex_2('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_100])).

tff(c_283,plain,(
    u1_struct_0(k1_tex_2('#skF_2','#skF_3')) = u1_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_277,c_121])).

tff(c_67,plain,(
    ! [A_42,B_43] :
      ( v7_struct_0(k1_tex_2(A_42,B_43))
      | ~ m1_subset_1(B_43,u1_struct_0(A_42))
      | ~ l1_pre_topc(A_42)
      | v2_struct_0(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_70,plain,
    ( v7_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_67])).

tff(c_73,plain,
    ( v7_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_70])).

tff(c_74,plain,(
    v7_struct_0(k1_tex_2('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_73])).

tff(c_38,plain,(
    ! [A_26,B_28] :
      ( v1_subset_1(k6_domain_1(A_26,B_28),A_26)
      | ~ m1_subset_1(B_28,A_26)
      | v1_zfmisc_1(A_26)
      | v1_xboole_0(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_198,plain,(
    ! [A_67,B_68] :
      ( ~ v7_struct_0(A_67)
      | ~ v1_subset_1(k6_domain_1(u1_struct_0(A_67),B_68),u1_struct_0(A_67))
      | ~ m1_subset_1(B_68,u1_struct_0(A_67))
      | ~ l1_struct_0(A_67)
      | v2_struct_0(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_218,plain,(
    ! [A_67,B_28] :
      ( ~ v7_struct_0(A_67)
      | ~ l1_struct_0(A_67)
      | v2_struct_0(A_67)
      | ~ m1_subset_1(B_28,u1_struct_0(A_67))
      | v1_zfmisc_1(u1_struct_0(A_67))
      | v1_xboole_0(u1_struct_0(A_67)) ) ),
    inference(resolution,[status(thm)],[c_38,c_198])).

tff(c_305,plain,(
    ! [B_28] :
      ( ~ v7_struct_0(k1_tex_2('#skF_2','#skF_3'))
      | ~ l1_struct_0(k1_tex_2('#skF_2','#skF_3'))
      | v2_struct_0(k1_tex_2('#skF_2','#skF_3'))
      | ~ m1_subset_1(B_28,u1_struct_0('#skF_2'))
      | v1_zfmisc_1(u1_struct_0(k1_tex_2('#skF_2','#skF_3')))
      | v1_xboole_0(u1_struct_0(k1_tex_2('#skF_2','#skF_3'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_283,c_218])).

tff(c_344,plain,(
    ! [B_28] :
      ( ~ l1_struct_0(k1_tex_2('#skF_2','#skF_3'))
      | v2_struct_0(k1_tex_2('#skF_2','#skF_3'))
      | ~ m1_subset_1(B_28,u1_struct_0('#skF_2'))
      | v1_zfmisc_1(u1_struct_0('#skF_2'))
      | v1_xboole_0(u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_283,c_283,c_74,c_305])).

tff(c_345,plain,(
    ! [B_28] :
      ( ~ l1_struct_0(k1_tex_2('#skF_2','#skF_3'))
      | ~ m1_subset_1(B_28,u1_struct_0('#skF_2'))
      | v1_zfmisc_1(u1_struct_0('#skF_2'))
      | v1_xboole_0(u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_344])).

tff(c_417,plain,(
    ~ l1_struct_0(k1_tex_2('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_345])).

tff(c_420,plain,(
    ~ l1_pre_topc(k1_tex_2('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_4,c_417])).

tff(c_424,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_420])).

tff(c_426,plain,(
    l1_struct_0(k1_tex_2('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_345])).

tff(c_40,plain,(
    ! [A_29,B_31] :
      ( ~ v7_struct_0(A_29)
      | ~ v1_subset_1(k6_domain_1(u1_struct_0(A_29),B_31),u1_struct_0(A_29))
      | ~ m1_subset_1(B_31,u1_struct_0(A_29))
      | ~ l1_struct_0(A_29)
      | v2_struct_0(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_314,plain,(
    ! [B_31] :
      ( ~ v7_struct_0(k1_tex_2('#skF_2','#skF_3'))
      | ~ v1_subset_1(k6_domain_1(u1_struct_0('#skF_2'),B_31),u1_struct_0(k1_tex_2('#skF_2','#skF_3')))
      | ~ m1_subset_1(B_31,u1_struct_0(k1_tex_2('#skF_2','#skF_3')))
      | ~ l1_struct_0(k1_tex_2('#skF_2','#skF_3'))
      | v2_struct_0(k1_tex_2('#skF_2','#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_283,c_40])).

tff(c_350,plain,(
    ! [B_31] :
      ( ~ v1_subset_1(k6_domain_1(u1_struct_0('#skF_2'),B_31),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_31,u1_struct_0('#skF_2'))
      | ~ l1_struct_0(k1_tex_2('#skF_2','#skF_3'))
      | v2_struct_0(k1_tex_2('#skF_2','#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_283,c_283,c_74,c_314])).

tff(c_351,plain,(
    ! [B_31] :
      ( ~ v1_subset_1(k6_domain_1(u1_struct_0('#skF_2'),B_31),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_31,u1_struct_0('#skF_2'))
      | ~ l1_struct_0(k1_tex_2('#skF_2','#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_350])).

tff(c_450,plain,(
    ! [B_84] :
      ( ~ v1_subset_1(k6_domain_1(u1_struct_0('#skF_2'),B_84),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_84,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_426,c_351])).

tff(c_457,plain,(
    ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_65,c_450])).

tff(c_462,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_457])).

tff(c_464,plain,(
    ~ v1_subset_1(k6_domain_1(u1_struct_0('#skF_2'),'#skF_3'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_479,plain,
    ( ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | v1_zfmisc_1(u1_struct_0('#skF_2'))
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_476,c_464])).

tff(c_482,plain,
    ( v1_zfmisc_1(u1_struct_0('#skF_2'))
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_479])).

tff(c_483,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_482])).

tff(c_2,plain,(
    ! [A_1] :
      ( v1_zfmisc_1(A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_57,plain,(
    ! [A_35] :
      ( ~ v1_zfmisc_1(u1_struct_0(A_35))
      | ~ l1_struct_0(A_35)
      | v7_struct_0(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_61,plain,(
    ! [A_35] :
      ( ~ l1_struct_0(A_35)
      | v7_struct_0(A_35)
      | ~ v1_xboole_0(u1_struct_0(A_35)) ) ),
    inference(resolution,[status(thm)],[c_2,c_57])).

tff(c_487,plain,
    ( ~ l1_struct_0('#skF_2')
    | v7_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_483,c_61])).

tff(c_488,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_487])).

tff(c_491,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_4,c_488])).

tff(c_495,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_491])).

tff(c_496,plain,(
    v7_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_487])).

tff(c_514,plain,(
    ! [A_95,B_96] :
      ( m1_pre_topc(k1_tex_2(A_95,B_96),A_95)
      | ~ m1_subset_1(B_96,u1_struct_0(A_95))
      | ~ l1_pre_topc(A_95)
      | v2_struct_0(A_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_516,plain,
    ( m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_514])).

tff(c_519,plain,
    ( m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_516])).

tff(c_520,plain,(
    m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_519])).

tff(c_463,plain,(
    v1_tex_2(k1_tex_2('#skF_2','#skF_3'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_528,plain,(
    ! [B_99,A_100] :
      ( ~ v1_tex_2(B_99,A_100)
      | v2_struct_0(B_99)
      | ~ m1_pre_topc(B_99,A_100)
      | ~ l1_pre_topc(A_100)
      | ~ v7_struct_0(A_100)
      | v2_struct_0(A_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_534,plain,
    ( v2_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | ~ m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v7_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_463,c_528])).

tff(c_538,plain,
    ( v2_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_496,c_44,c_520,c_534])).

tff(c_540,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_513,c_538])).

tff(c_541,plain,(
    v1_zfmisc_1(u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_482])).

tff(c_8,plain,(
    ! [A_6] :
      ( ~ v1_zfmisc_1(u1_struct_0(A_6))
      | ~ l1_struct_0(A_6)
      | v7_struct_0(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_546,plain,
    ( ~ l1_struct_0('#skF_2')
    | v7_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_541,c_8])).

tff(c_547,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_546])).

tff(c_558,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_4,c_547])).

tff(c_562,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_558])).

tff(c_563,plain,(
    v7_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_546])).

tff(c_582,plain,(
    ! [A_109,B_110] :
      ( m1_pre_topc(k1_tex_2(A_109,B_110),A_109)
      | ~ m1_subset_1(B_110,u1_struct_0(A_109))
      | ~ l1_pre_topc(A_109)
      | v2_struct_0(A_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_584,plain,
    ( m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_582])).

tff(c_587,plain,
    ( m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_584])).

tff(c_588,plain,(
    m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_587])).

tff(c_596,plain,(
    ! [B_113,A_114] :
      ( ~ v1_tex_2(B_113,A_114)
      | v2_struct_0(B_113)
      | ~ m1_pre_topc(B_113,A_114)
      | ~ l1_pre_topc(A_114)
      | ~ v7_struct_0(A_114)
      | v2_struct_0(A_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_602,plain,
    ( v2_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | ~ m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v7_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_463,c_596])).

tff(c_606,plain,
    ( v2_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_563,c_44,c_588,c_602])).

tff(c_608,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_572,c_606])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:24:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.76/1.38  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.76/1.39  
% 2.76/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.76/1.39  %$ v1_tex_2 > v1_subset_1 > m1_subset_1 > m1_pre_topc > v7_struct_0 > v2_struct_0 > v1_zfmisc_1 > v1_xboole_0 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k6_domain_1 > k1_tex_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 2.76/1.39  
% 2.76/1.39  %Foreground sorts:
% 2.76/1.39  
% 2.76/1.39  
% 2.76/1.39  %Background operators:
% 2.76/1.39  
% 2.76/1.39  
% 2.76/1.39  %Foreground operators:
% 2.76/1.39  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.76/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.76/1.39  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 2.76/1.39  tff(v1_tex_2, type, v1_tex_2: ($i * $i) > $o).
% 2.76/1.39  tff(v7_struct_0, type, v7_struct_0: $i > $o).
% 2.76/1.39  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.76/1.39  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.76/1.39  tff('#skF_2', type, '#skF_2': $i).
% 2.76/1.39  tff('#skF_3', type, '#skF_3': $i).
% 2.76/1.39  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 2.76/1.39  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.76/1.39  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.76/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.76/1.39  tff(k1_tex_2, type, k1_tex_2: ($i * $i) > $i).
% 2.76/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.76/1.39  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 2.76/1.40  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.76/1.40  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.76/1.40  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.76/1.40  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.76/1.40  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.76/1.40  
% 2.76/1.42  tff(f_153, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (v1_tex_2(k1_tex_2(A, B), A) <=> v1_subset_1(k6_domain_1(u1_struct_0(A), B), u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_tex_2)).
% 2.76/1.42  tff(f_116, axiom, (![A, B]: (((~v2_struct_0(A) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => ((~v2_struct_0(k1_tex_2(A, B)) & v7_struct_0(k1_tex_2(A, B))) & v1_pre_topc(k1_tex_2(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_tex_2)).
% 2.76/1.42  tff(f_33, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.76/1.42  tff(f_127, axiom, (![A]: ((~v1_xboole_0(A) & ~v1_zfmisc_1(A)) => (![B]: (m1_subset_1(B, A) => v1_subset_1(k6_domain_1(A, B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_tex_2)).
% 2.76/1.42  tff(f_102, axiom, (![A, B]: (((~v2_struct_0(A) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => ((~v2_struct_0(k1_tex_2(A, B)) & v1_pre_topc(k1_tex_2(A, B))) & m1_pre_topc(k1_tex_2(A, B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tex_2)).
% 2.76/1.42  tff(f_40, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 2.76/1.42  tff(f_81, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (v1_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => v1_subset_1(C, u1_struct_0(A)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tex_2)).
% 2.76/1.42  tff(f_88, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (v1_subset_1(B, A) <=> ~(B = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_subset_1)).
% 2.76/1.42  tff(f_140, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => ~(v1_subset_1(k6_domain_1(u1_struct_0(A), B), u1_struct_0(A)) & v7_struct_0(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_tex_2)).
% 2.76/1.42  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => v1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_zfmisc_1)).
% 2.76/1.42  tff(f_48, axiom, (![A]: ((~v7_struct_0(A) & l1_struct_0(A)) => ~v1_zfmisc_1(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_struct_0)).
% 2.76/1.42  tff(f_67, axiom, (![A]: (((~v2_struct_0(A) & v7_struct_0(A)) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (~v2_struct_0(B) => (~v2_struct_0(B) & ~v1_tex_2(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc10_tex_2)).
% 2.76/1.42  tff(c_46, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_153])).
% 2.76/1.42  tff(c_44, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_153])).
% 2.76/1.42  tff(c_42, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_153])).
% 2.76/1.42  tff(c_565, plain, (![A_103, B_104]: (~v2_struct_0(k1_tex_2(A_103, B_104)) | ~m1_subset_1(B_104, u1_struct_0(A_103)) | ~l1_pre_topc(A_103) | v2_struct_0(A_103))), inference(cnfTransformation, [status(thm)], [f_116])).
% 2.76/1.42  tff(c_568, plain, (~v2_struct_0(k1_tex_2('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_42, c_565])).
% 2.76/1.42  tff(c_571, plain, (~v2_struct_0(k1_tex_2('#skF_2', '#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_568])).
% 2.76/1.42  tff(c_572, plain, (~v2_struct_0(k1_tex_2('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_46, c_571])).
% 2.76/1.42  tff(c_4, plain, (![A_2]: (l1_struct_0(A_2) | ~l1_pre_topc(A_2))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.76/1.42  tff(c_506, plain, (![A_93, B_94]: (~v2_struct_0(k1_tex_2(A_93, B_94)) | ~m1_subset_1(B_94, u1_struct_0(A_93)) | ~l1_pre_topc(A_93) | v2_struct_0(A_93))), inference(cnfTransformation, [status(thm)], [f_116])).
% 2.76/1.42  tff(c_509, plain, (~v2_struct_0(k1_tex_2('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_42, c_506])).
% 2.76/1.42  tff(c_512, plain, (~v2_struct_0(k1_tex_2('#skF_2', '#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_509])).
% 2.76/1.42  tff(c_513, plain, (~v2_struct_0(k1_tex_2('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_46, c_512])).
% 2.76/1.42  tff(c_476, plain, (![A_89, B_90]: (v1_subset_1(k6_domain_1(A_89, B_90), A_89) | ~m1_subset_1(B_90, A_89) | v1_zfmisc_1(A_89) | v1_xboole_0(A_89))), inference(cnfTransformation, [status(thm)], [f_127])).
% 2.76/1.42  tff(c_54, plain, (v1_tex_2(k1_tex_2('#skF_2', '#skF_3'), '#skF_2') | v1_subset_1(k6_domain_1(u1_struct_0('#skF_2'), '#skF_3'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_153])).
% 2.76/1.42  tff(c_65, plain, (v1_subset_1(k6_domain_1(u1_struct_0('#skF_2'), '#skF_3'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_54])).
% 2.76/1.42  tff(c_101, plain, (![A_52, B_53]: (m1_pre_topc(k1_tex_2(A_52, B_53), A_52) | ~m1_subset_1(B_53, u1_struct_0(A_52)) | ~l1_pre_topc(A_52) | v2_struct_0(A_52))), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.76/1.42  tff(c_103, plain, (m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2') | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_42, c_101])).
% 2.76/1.42  tff(c_106, plain, (m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_103])).
% 2.76/1.42  tff(c_107, plain, (m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_46, c_106])).
% 2.76/1.42  tff(c_6, plain, (![B_5, A_3]: (l1_pre_topc(B_5) | ~m1_pre_topc(B_5, A_3) | ~l1_pre_topc(A_3))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.76/1.42  tff(c_110, plain, (l1_pre_topc(k1_tex_2('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_107, c_6])).
% 2.76/1.42  tff(c_113, plain, (l1_pre_topc(k1_tex_2('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_110])).
% 2.76/1.42  tff(c_77, plain, (![A_44, B_45]: (~v2_struct_0(k1_tex_2(A_44, B_45)) | ~m1_subset_1(B_45, u1_struct_0(A_44)) | ~l1_pre_topc(A_44) | v2_struct_0(A_44))), inference(cnfTransformation, [status(thm)], [f_116])).
% 2.76/1.42  tff(c_80, plain, (~v2_struct_0(k1_tex_2('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_42, c_77])).
% 2.76/1.42  tff(c_83, plain, (~v2_struct_0(k1_tex_2('#skF_2', '#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_80])).
% 2.76/1.42  tff(c_84, plain, (~v2_struct_0(k1_tex_2('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_46, c_83])).
% 2.76/1.42  tff(c_165, plain, (![A_61, B_62]: (m1_subset_1('#skF_1'(A_61, B_62), k1_zfmisc_1(u1_struct_0(A_61))) | v1_tex_2(B_62, A_61) | ~m1_pre_topc(B_62, A_61) | ~l1_pre_topc(A_61))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.76/1.42  tff(c_22, plain, (![B_21, A_20]: (v1_subset_1(B_21, A_20) | B_21=A_20 | ~m1_subset_1(B_21, k1_zfmisc_1(A_20)))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.76/1.42  tff(c_257, plain, (![A_73, B_74]: (v1_subset_1('#skF_1'(A_73, B_74), u1_struct_0(A_73)) | u1_struct_0(A_73)='#skF_1'(A_73, B_74) | v1_tex_2(B_74, A_73) | ~m1_pre_topc(B_74, A_73) | ~l1_pre_topc(A_73))), inference(resolution, [status(thm)], [c_165, c_22])).
% 2.76/1.42  tff(c_16, plain, (![A_10, B_16]: (~v1_subset_1('#skF_1'(A_10, B_16), u1_struct_0(A_10)) | v1_tex_2(B_16, A_10) | ~m1_pre_topc(B_16, A_10) | ~l1_pre_topc(A_10))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.76/1.42  tff(c_267, plain, (![A_75, B_76]: (u1_struct_0(A_75)='#skF_1'(A_75, B_76) | v1_tex_2(B_76, A_75) | ~m1_pre_topc(B_76, A_75) | ~l1_pre_topc(A_75))), inference(resolution, [status(thm)], [c_257, c_16])).
% 2.76/1.42  tff(c_48, plain, (~v1_subset_1(k6_domain_1(u1_struct_0('#skF_2'), '#skF_3'), u1_struct_0('#skF_2')) | ~v1_tex_2(k1_tex_2('#skF_2', '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_153])).
% 2.76/1.42  tff(c_76, plain, (~v1_tex_2(k1_tex_2('#skF_2', '#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_65, c_48])).
% 2.76/1.42  tff(c_273, plain, ('#skF_1'('#skF_2', k1_tex_2('#skF_2', '#skF_3'))=u1_struct_0('#skF_2') | ~m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_267, c_76])).
% 2.76/1.42  tff(c_277, plain, ('#skF_1'('#skF_2', k1_tex_2('#skF_2', '#skF_3'))=u1_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_107, c_273])).
% 2.76/1.42  tff(c_94, plain, (![B_50, A_51]: (u1_struct_0(B_50)='#skF_1'(A_51, B_50) | v1_tex_2(B_50, A_51) | ~m1_pre_topc(B_50, A_51) | ~l1_pre_topc(A_51))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.76/1.42  tff(c_97, plain, (u1_struct_0(k1_tex_2('#skF_2', '#skF_3'))='#skF_1'('#skF_2', k1_tex_2('#skF_2', '#skF_3')) | ~m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_94, c_76])).
% 2.76/1.42  tff(c_100, plain, (u1_struct_0(k1_tex_2('#skF_2', '#skF_3'))='#skF_1'('#skF_2', k1_tex_2('#skF_2', '#skF_3')) | ~m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_97])).
% 2.76/1.42  tff(c_121, plain, (u1_struct_0(k1_tex_2('#skF_2', '#skF_3'))='#skF_1'('#skF_2', k1_tex_2('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_107, c_100])).
% 2.76/1.42  tff(c_283, plain, (u1_struct_0(k1_tex_2('#skF_2', '#skF_3'))=u1_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_277, c_121])).
% 2.76/1.42  tff(c_67, plain, (![A_42, B_43]: (v7_struct_0(k1_tex_2(A_42, B_43)) | ~m1_subset_1(B_43, u1_struct_0(A_42)) | ~l1_pre_topc(A_42) | v2_struct_0(A_42))), inference(cnfTransformation, [status(thm)], [f_116])).
% 2.76/1.42  tff(c_70, plain, (v7_struct_0(k1_tex_2('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_42, c_67])).
% 2.76/1.42  tff(c_73, plain, (v7_struct_0(k1_tex_2('#skF_2', '#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_70])).
% 2.76/1.42  tff(c_74, plain, (v7_struct_0(k1_tex_2('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_46, c_73])).
% 2.76/1.42  tff(c_38, plain, (![A_26, B_28]: (v1_subset_1(k6_domain_1(A_26, B_28), A_26) | ~m1_subset_1(B_28, A_26) | v1_zfmisc_1(A_26) | v1_xboole_0(A_26))), inference(cnfTransformation, [status(thm)], [f_127])).
% 2.76/1.42  tff(c_198, plain, (![A_67, B_68]: (~v7_struct_0(A_67) | ~v1_subset_1(k6_domain_1(u1_struct_0(A_67), B_68), u1_struct_0(A_67)) | ~m1_subset_1(B_68, u1_struct_0(A_67)) | ~l1_struct_0(A_67) | v2_struct_0(A_67))), inference(cnfTransformation, [status(thm)], [f_140])).
% 2.76/1.42  tff(c_218, plain, (![A_67, B_28]: (~v7_struct_0(A_67) | ~l1_struct_0(A_67) | v2_struct_0(A_67) | ~m1_subset_1(B_28, u1_struct_0(A_67)) | v1_zfmisc_1(u1_struct_0(A_67)) | v1_xboole_0(u1_struct_0(A_67)))), inference(resolution, [status(thm)], [c_38, c_198])).
% 2.76/1.42  tff(c_305, plain, (![B_28]: (~v7_struct_0(k1_tex_2('#skF_2', '#skF_3')) | ~l1_struct_0(k1_tex_2('#skF_2', '#skF_3')) | v2_struct_0(k1_tex_2('#skF_2', '#skF_3')) | ~m1_subset_1(B_28, u1_struct_0('#skF_2')) | v1_zfmisc_1(u1_struct_0(k1_tex_2('#skF_2', '#skF_3'))) | v1_xboole_0(u1_struct_0(k1_tex_2('#skF_2', '#skF_3'))))), inference(superposition, [status(thm), theory('equality')], [c_283, c_218])).
% 2.76/1.42  tff(c_344, plain, (![B_28]: (~l1_struct_0(k1_tex_2('#skF_2', '#skF_3')) | v2_struct_0(k1_tex_2('#skF_2', '#skF_3')) | ~m1_subset_1(B_28, u1_struct_0('#skF_2')) | v1_zfmisc_1(u1_struct_0('#skF_2')) | v1_xboole_0(u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_283, c_283, c_74, c_305])).
% 2.76/1.42  tff(c_345, plain, (![B_28]: (~l1_struct_0(k1_tex_2('#skF_2', '#skF_3')) | ~m1_subset_1(B_28, u1_struct_0('#skF_2')) | v1_zfmisc_1(u1_struct_0('#skF_2')) | v1_xboole_0(u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_84, c_344])).
% 2.76/1.42  tff(c_417, plain, (~l1_struct_0(k1_tex_2('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_345])).
% 2.76/1.42  tff(c_420, plain, (~l1_pre_topc(k1_tex_2('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_4, c_417])).
% 2.76/1.42  tff(c_424, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_113, c_420])).
% 2.76/1.42  tff(c_426, plain, (l1_struct_0(k1_tex_2('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_345])).
% 2.76/1.42  tff(c_40, plain, (![A_29, B_31]: (~v7_struct_0(A_29) | ~v1_subset_1(k6_domain_1(u1_struct_0(A_29), B_31), u1_struct_0(A_29)) | ~m1_subset_1(B_31, u1_struct_0(A_29)) | ~l1_struct_0(A_29) | v2_struct_0(A_29))), inference(cnfTransformation, [status(thm)], [f_140])).
% 2.76/1.42  tff(c_314, plain, (![B_31]: (~v7_struct_0(k1_tex_2('#skF_2', '#skF_3')) | ~v1_subset_1(k6_domain_1(u1_struct_0('#skF_2'), B_31), u1_struct_0(k1_tex_2('#skF_2', '#skF_3'))) | ~m1_subset_1(B_31, u1_struct_0(k1_tex_2('#skF_2', '#skF_3'))) | ~l1_struct_0(k1_tex_2('#skF_2', '#skF_3')) | v2_struct_0(k1_tex_2('#skF_2', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_283, c_40])).
% 2.76/1.42  tff(c_350, plain, (![B_31]: (~v1_subset_1(k6_domain_1(u1_struct_0('#skF_2'), B_31), u1_struct_0('#skF_2')) | ~m1_subset_1(B_31, u1_struct_0('#skF_2')) | ~l1_struct_0(k1_tex_2('#skF_2', '#skF_3')) | v2_struct_0(k1_tex_2('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_283, c_283, c_74, c_314])).
% 2.76/1.42  tff(c_351, plain, (![B_31]: (~v1_subset_1(k6_domain_1(u1_struct_0('#skF_2'), B_31), u1_struct_0('#skF_2')) | ~m1_subset_1(B_31, u1_struct_0('#skF_2')) | ~l1_struct_0(k1_tex_2('#skF_2', '#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_84, c_350])).
% 2.76/1.42  tff(c_450, plain, (![B_84]: (~v1_subset_1(k6_domain_1(u1_struct_0('#skF_2'), B_84), u1_struct_0('#skF_2')) | ~m1_subset_1(B_84, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_426, c_351])).
% 2.76/1.42  tff(c_457, plain, (~m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_65, c_450])).
% 2.76/1.42  tff(c_462, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_457])).
% 2.76/1.42  tff(c_464, plain, (~v1_subset_1(k6_domain_1(u1_struct_0('#skF_2'), '#skF_3'), u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_54])).
% 2.76/1.42  tff(c_479, plain, (~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | v1_zfmisc_1(u1_struct_0('#skF_2')) | v1_xboole_0(u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_476, c_464])).
% 2.76/1.42  tff(c_482, plain, (v1_zfmisc_1(u1_struct_0('#skF_2')) | v1_xboole_0(u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_479])).
% 2.76/1.42  tff(c_483, plain, (v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_482])).
% 2.76/1.42  tff(c_2, plain, (![A_1]: (v1_zfmisc_1(A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.76/1.42  tff(c_57, plain, (![A_35]: (~v1_zfmisc_1(u1_struct_0(A_35)) | ~l1_struct_0(A_35) | v7_struct_0(A_35))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.76/1.42  tff(c_61, plain, (![A_35]: (~l1_struct_0(A_35) | v7_struct_0(A_35) | ~v1_xboole_0(u1_struct_0(A_35)))), inference(resolution, [status(thm)], [c_2, c_57])).
% 2.76/1.42  tff(c_487, plain, (~l1_struct_0('#skF_2') | v7_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_483, c_61])).
% 2.76/1.42  tff(c_488, plain, (~l1_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_487])).
% 2.76/1.42  tff(c_491, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_4, c_488])).
% 2.76/1.42  tff(c_495, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_491])).
% 2.76/1.42  tff(c_496, plain, (v7_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_487])).
% 2.76/1.42  tff(c_514, plain, (![A_95, B_96]: (m1_pre_topc(k1_tex_2(A_95, B_96), A_95) | ~m1_subset_1(B_96, u1_struct_0(A_95)) | ~l1_pre_topc(A_95) | v2_struct_0(A_95))), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.76/1.42  tff(c_516, plain, (m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2') | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_42, c_514])).
% 2.76/1.42  tff(c_519, plain, (m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_516])).
% 2.76/1.42  tff(c_520, plain, (m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_46, c_519])).
% 2.76/1.42  tff(c_463, plain, (v1_tex_2(k1_tex_2('#skF_2', '#skF_3'), '#skF_2')), inference(splitRight, [status(thm)], [c_54])).
% 2.76/1.42  tff(c_528, plain, (![B_99, A_100]: (~v1_tex_2(B_99, A_100) | v2_struct_0(B_99) | ~m1_pre_topc(B_99, A_100) | ~l1_pre_topc(A_100) | ~v7_struct_0(A_100) | v2_struct_0(A_100))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.76/1.42  tff(c_534, plain, (v2_struct_0(k1_tex_2('#skF_2', '#skF_3')) | ~m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2') | ~l1_pre_topc('#skF_2') | ~v7_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_463, c_528])).
% 2.76/1.42  tff(c_538, plain, (v2_struct_0(k1_tex_2('#skF_2', '#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_496, c_44, c_520, c_534])).
% 2.76/1.42  tff(c_540, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_513, c_538])).
% 2.76/1.42  tff(c_541, plain, (v1_zfmisc_1(u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_482])).
% 2.76/1.42  tff(c_8, plain, (![A_6]: (~v1_zfmisc_1(u1_struct_0(A_6)) | ~l1_struct_0(A_6) | v7_struct_0(A_6))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.76/1.42  tff(c_546, plain, (~l1_struct_0('#skF_2') | v7_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_541, c_8])).
% 2.76/1.42  tff(c_547, plain, (~l1_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_546])).
% 2.76/1.42  tff(c_558, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_4, c_547])).
% 2.76/1.42  tff(c_562, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_558])).
% 2.76/1.42  tff(c_563, plain, (v7_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_546])).
% 2.76/1.42  tff(c_582, plain, (![A_109, B_110]: (m1_pre_topc(k1_tex_2(A_109, B_110), A_109) | ~m1_subset_1(B_110, u1_struct_0(A_109)) | ~l1_pre_topc(A_109) | v2_struct_0(A_109))), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.76/1.42  tff(c_584, plain, (m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2') | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_42, c_582])).
% 2.76/1.42  tff(c_587, plain, (m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_584])).
% 2.76/1.42  tff(c_588, plain, (m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_46, c_587])).
% 2.76/1.42  tff(c_596, plain, (![B_113, A_114]: (~v1_tex_2(B_113, A_114) | v2_struct_0(B_113) | ~m1_pre_topc(B_113, A_114) | ~l1_pre_topc(A_114) | ~v7_struct_0(A_114) | v2_struct_0(A_114))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.76/1.42  tff(c_602, plain, (v2_struct_0(k1_tex_2('#skF_2', '#skF_3')) | ~m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2') | ~l1_pre_topc('#skF_2') | ~v7_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_463, c_596])).
% 2.76/1.42  tff(c_606, plain, (v2_struct_0(k1_tex_2('#skF_2', '#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_563, c_44, c_588, c_602])).
% 2.76/1.42  tff(c_608, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_572, c_606])).
% 2.76/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.76/1.42  
% 2.76/1.42  Inference rules
% 2.76/1.42  ----------------------
% 2.76/1.42  #Ref     : 0
% 2.76/1.42  #Sup     : 83
% 2.76/1.42  #Fact    : 0
% 2.76/1.42  #Define  : 0
% 2.76/1.42  #Split   : 10
% 2.76/1.42  #Chain   : 0
% 2.76/1.42  #Close   : 0
% 2.76/1.42  
% 2.76/1.42  Ordering : KBO
% 2.76/1.42  
% 2.76/1.42  Simplification rules
% 2.76/1.42  ----------------------
% 2.76/1.42  #Subsume      : 22
% 2.76/1.42  #Demod        : 104
% 2.76/1.42  #Tautology    : 15
% 2.76/1.42  #SimpNegUnit  : 40
% 2.76/1.42  #BackRed      : 8
% 2.76/1.42  
% 2.76/1.42  #Partial instantiations: 0
% 2.76/1.42  #Strategies tried      : 1
% 2.76/1.42  
% 2.76/1.42  Timing (in seconds)
% 2.76/1.42  ----------------------
% 2.76/1.42  Preprocessing        : 0.33
% 2.76/1.42  Parsing              : 0.18
% 2.76/1.42  CNF conversion       : 0.02
% 2.76/1.42  Main loop            : 0.30
% 2.76/1.42  Inferencing          : 0.11
% 2.76/1.42  Reduction            : 0.10
% 2.76/1.42  Demodulation         : 0.06
% 2.76/1.42  BG Simplification    : 0.02
% 2.76/1.42  Subsumption          : 0.05
% 2.76/1.42  Abstraction          : 0.02
% 2.76/1.42  MUC search           : 0.00
% 2.76/1.42  Cooper               : 0.00
% 2.76/1.42  Total                : 0.67
% 2.76/1.42  Index Insertion      : 0.00
% 2.76/1.42  Index Deletion       : 0.00
% 2.76/1.42  Index Matching       : 0.00
% 2.76/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
