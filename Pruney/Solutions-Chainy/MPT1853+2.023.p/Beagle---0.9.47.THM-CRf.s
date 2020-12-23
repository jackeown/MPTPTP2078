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
% DateTime   : Thu Dec  3 10:29:03 EST 2020

% Result     : Theorem 2.49s
% Output     : CNFRefutation 2.49s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 277 expanded)
%              Number of leaves         :   33 ( 105 expanded)
%              Depth                    :   12
%              Number of atoms          :  225 ( 749 expanded)
%              Number of equality atoms :   11 (  23 expanded)
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

tff(f_155,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ( v1_tex_2(k1_tex_2(A,B),A)
            <=> v1_subset_1(k6_domain_1(u1_struct_0(A),B),u1_struct_0(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_tex_2)).

tff(f_29,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_118,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ( ~ v2_struct_0(k1_tex_2(A,B))
        & v7_struct_0(k1_tex_2(A,B))
        & v1_pre_topc(k1_tex_2(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_tex_2)).

tff(f_104,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ( ~ v2_struct_0(k1_tex_2(A,B))
        & v1_pre_topc(k1_tex_2(A,B))
        & m1_pre_topc(k1_tex_2(A,B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tex_2)).

tff(f_129,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,A)
         => ~ ( v1_subset_1(k6_domain_1(A,B),A)
              & v1_zfmisc_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_tex_2)).

tff(f_83,axiom,(
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

tff(f_90,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( v1_subset_1(B,A)
      <=> B != A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).

tff(f_36,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_44,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_50,axiom,(
    ! [A] :
      ( ( v7_struct_0(A)
        & l1_struct_0(A) )
     => v1_zfmisc_1(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_struct_0)).

tff(f_69,axiom,(
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

tff(f_142,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & ~ v7_struct_0(A)
        & l1_struct_0(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => v1_subset_1(k6_domain_1(u1_struct_0(A),B),u1_struct_0(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_tex_2)).

tff(c_44,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_2,plain,(
    ! [A_1] :
      ( l1_struct_0(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_46,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_42,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_315,plain,(
    ! [A_78,B_79] :
      ( ~ v2_struct_0(k1_tex_2(A_78,B_79))
      | ~ m1_subset_1(B_79,u1_struct_0(A_78))
      | ~ l1_pre_topc(A_78)
      | v2_struct_0(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_318,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_315])).

tff(c_321,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_318])).

tff(c_322,plain,(
    ~ v2_struct_0(k1_tex_2('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_321])).

tff(c_333,plain,(
    ! [A_86,B_87] :
      ( m1_pre_topc(k1_tex_2(A_86,B_87),A_86)
      | ~ m1_subset_1(B_87,u1_struct_0(A_86))
      | ~ l1_pre_topc(A_86)
      | v2_struct_0(A_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_335,plain,
    ( m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_333])).

tff(c_338,plain,
    ( m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_335])).

tff(c_339,plain,(
    m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_338])).

tff(c_54,plain,
    ( v1_tex_2(k1_tex_2('#skF_2','#skF_3'),'#skF_2')
    | v1_subset_1(k6_domain_1(u1_struct_0('#skF_2'),'#skF_3'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_61,plain,(
    v1_subset_1(k6_domain_1(u1_struct_0('#skF_2'),'#skF_3'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_80,plain,(
    ! [A_45,B_46] :
      ( ~ v1_zfmisc_1(A_45)
      | ~ v1_subset_1(k6_domain_1(A_45,B_46),A_45)
      | ~ m1_subset_1(B_46,A_45)
      | v1_xboole_0(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_83,plain,
    ( ~ v1_zfmisc_1(u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_61,c_80])).

tff(c_86,plain,
    ( ~ v1_zfmisc_1(u1_struct_0('#skF_2'))
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_83])).

tff(c_87,plain,(
    ~ v1_zfmisc_1(u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_86])).

tff(c_108,plain,(
    ! [A_51,B_52] :
      ( m1_pre_topc(k1_tex_2(A_51,B_52),A_51)
      | ~ m1_subset_1(B_52,u1_struct_0(A_51))
      | ~ l1_pre_topc(A_51)
      | v2_struct_0(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_110,plain,
    ( m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_108])).

tff(c_113,plain,
    ( m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_110])).

tff(c_114,plain,(
    m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_113])).

tff(c_182,plain,(
    ! [A_57,B_58] :
      ( m1_subset_1('#skF_1'(A_57,B_58),k1_zfmisc_1(u1_struct_0(A_57)))
      | v1_tex_2(B_58,A_57)
      | ~ m1_pre_topc(B_58,A_57)
      | ~ l1_pre_topc(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_22,plain,(
    ! [B_21,A_20] :
      ( v1_subset_1(B_21,A_20)
      | B_21 = A_20
      | ~ m1_subset_1(B_21,k1_zfmisc_1(A_20)) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_257,plain,(
    ! [A_72,B_73] :
      ( v1_subset_1('#skF_1'(A_72,B_73),u1_struct_0(A_72))
      | u1_struct_0(A_72) = '#skF_1'(A_72,B_73)
      | v1_tex_2(B_73,A_72)
      | ~ m1_pre_topc(B_73,A_72)
      | ~ l1_pre_topc(A_72) ) ),
    inference(resolution,[status(thm)],[c_182,c_22])).

tff(c_16,plain,(
    ! [A_10,B_16] :
      ( ~ v1_subset_1('#skF_1'(A_10,B_16),u1_struct_0(A_10))
      | v1_tex_2(B_16,A_10)
      | ~ m1_pre_topc(B_16,A_10)
      | ~ l1_pre_topc(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_267,plain,(
    ! [A_74,B_75] :
      ( u1_struct_0(A_74) = '#skF_1'(A_74,B_75)
      | v1_tex_2(B_75,A_74)
      | ~ m1_pre_topc(B_75,A_74)
      | ~ l1_pre_topc(A_74) ) ),
    inference(resolution,[status(thm)],[c_257,c_16])).

tff(c_48,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0('#skF_2'),'#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_tex_2(k1_tex_2('#skF_2','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_79,plain,(
    ~ v1_tex_2(k1_tex_2('#skF_2','#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_48])).

tff(c_273,plain,
    ( '#skF_1'('#skF_2',k1_tex_2('#skF_2','#skF_3')) = u1_struct_0('#skF_2')
    | ~ m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_267,c_79])).

tff(c_277,plain,(
    '#skF_1'('#skF_2',k1_tex_2('#skF_2','#skF_3')) = u1_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_114,c_273])).

tff(c_4,plain,(
    ! [B_4,A_2] :
      ( l1_pre_topc(B_4)
      | ~ m1_pre_topc(B_4,A_2)
      | ~ l1_pre_topc(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_122,plain,
    ( l1_pre_topc(k1_tex_2('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_114,c_4])).

tff(c_125,plain,(
    l1_pre_topc(k1_tex_2('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_122])).

tff(c_93,plain,(
    ! [A_47,B_48] :
      ( ~ v2_struct_0(k1_tex_2(A_47,B_48))
      | ~ m1_subset_1(B_48,u1_struct_0(A_47))
      | ~ l1_pre_topc(A_47)
      | v2_struct_0(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_96,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_93])).

tff(c_99,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_96])).

tff(c_100,plain,(
    ~ v2_struct_0(k1_tex_2('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_99])).

tff(c_101,plain,(
    ! [B_49,A_50] :
      ( u1_struct_0(B_49) = '#skF_1'(A_50,B_49)
      | v1_tex_2(B_49,A_50)
      | ~ m1_pre_topc(B_49,A_50)
      | ~ l1_pre_topc(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_104,plain,
    ( u1_struct_0(k1_tex_2('#skF_2','#skF_3')) = '#skF_1'('#skF_2',k1_tex_2('#skF_2','#skF_3'))
    | ~ m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_101,c_79])).

tff(c_107,plain,
    ( u1_struct_0(k1_tex_2('#skF_2','#skF_3')) = '#skF_1'('#skF_2',k1_tex_2('#skF_2','#skF_3'))
    | ~ m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_104])).

tff(c_128,plain,(
    u1_struct_0(k1_tex_2('#skF_2','#skF_3')) = '#skF_1'('#skF_2',k1_tex_2('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_107])).

tff(c_6,plain,(
    ! [A_5] :
      ( ~ v1_xboole_0(u1_struct_0(A_5))
      | ~ l1_struct_0(A_5)
      | v2_struct_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_146,plain,
    ( ~ v1_xboole_0('#skF_1'('#skF_2',k1_tex_2('#skF_2','#skF_3')))
    | ~ l1_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | v2_struct_0(k1_tex_2('#skF_2','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_128,c_6])).

tff(c_166,plain,
    ( ~ v1_xboole_0('#skF_1'('#skF_2',k1_tex_2('#skF_2','#skF_3')))
    | ~ l1_struct_0(k1_tex_2('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_146])).

tff(c_170,plain,(
    ~ l1_struct_0(k1_tex_2('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_166])).

tff(c_173,plain,(
    ~ l1_pre_topc(k1_tex_2('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_2,c_170])).

tff(c_177,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_173])).

tff(c_179,plain,(
    l1_struct_0(k1_tex_2('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_166])).

tff(c_70,plain,(
    ! [A_43,B_44] :
      ( v7_struct_0(k1_tex_2(A_43,B_44))
      | ~ m1_subset_1(B_44,u1_struct_0(A_43))
      | ~ l1_pre_topc(A_43)
      | v2_struct_0(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_73,plain,
    ( v7_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_70])).

tff(c_76,plain,
    ( v7_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_73])).

tff(c_77,plain,(
    v7_struct_0(k1_tex_2('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_76])).

tff(c_8,plain,(
    ! [A_6] :
      ( v1_zfmisc_1(u1_struct_0(A_6))
      | ~ l1_struct_0(A_6)
      | ~ v7_struct_0(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_149,plain,
    ( v1_zfmisc_1('#skF_1'('#skF_2',k1_tex_2('#skF_2','#skF_3')))
    | ~ l1_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | ~ v7_struct_0(k1_tex_2('#skF_2','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_128,c_8])).

tff(c_168,plain,
    ( v1_zfmisc_1('#skF_1'('#skF_2',k1_tex_2('#skF_2','#skF_3')))
    | ~ l1_struct_0(k1_tex_2('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_149])).

tff(c_181,plain,(
    v1_zfmisc_1('#skF_1'('#skF_2',k1_tex_2('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_179,c_168])).

tff(c_283,plain,(
    v1_zfmisc_1(u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_277,c_181])).

tff(c_287,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_87,c_283])).

tff(c_288,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_86])).

tff(c_292,plain,
    ( ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_288,c_6])).

tff(c_295,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_292])).

tff(c_298,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_2,c_295])).

tff(c_302,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_298])).

tff(c_303,plain,(
    v1_tex_2(k1_tex_2('#skF_2','#skF_3'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_346,plain,(
    ! [B_88,A_89] :
      ( ~ v1_tex_2(B_88,A_89)
      | v2_struct_0(B_88)
      | ~ m1_pre_topc(B_88,A_89)
      | ~ l1_pre_topc(A_89)
      | ~ v7_struct_0(A_89)
      | v2_struct_0(A_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_352,plain,
    ( v2_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | ~ m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v7_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_303,c_346])).

tff(c_356,plain,
    ( v2_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | ~ v7_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_339,c_352])).

tff(c_357,plain,(
    ~ v7_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_322,c_356])).

tff(c_372,plain,(
    ! [A_96,B_97] :
      ( v1_subset_1(k6_domain_1(u1_struct_0(A_96),B_97),u1_struct_0(A_96))
      | ~ m1_subset_1(B_97,u1_struct_0(A_96))
      | ~ l1_struct_0(A_96)
      | v7_struct_0(A_96)
      | v2_struct_0(A_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_304,plain,(
    ~ v1_subset_1(k6_domain_1(u1_struct_0('#skF_2'),'#skF_3'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_378,plain,
    ( ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_struct_0('#skF_2')
    | v7_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_372,c_304])).

tff(c_382,plain,
    ( ~ l1_struct_0('#skF_2')
    | v7_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_378])).

tff(c_383,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_357,c_382])).

tff(c_386,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_2,c_383])).

tff(c_390,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_386])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n023.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:51:36 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.49/1.42  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.49/1.43  
% 2.49/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.49/1.43  %$ v1_tex_2 > v1_subset_1 > m1_subset_1 > m1_pre_topc > v7_struct_0 > v2_struct_0 > v1_zfmisc_1 > v1_xboole_0 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k6_domain_1 > k1_tex_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 2.49/1.43  
% 2.49/1.43  %Foreground sorts:
% 2.49/1.43  
% 2.49/1.43  
% 2.49/1.43  %Background operators:
% 2.49/1.43  
% 2.49/1.43  
% 2.49/1.43  %Foreground operators:
% 2.49/1.43  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.49/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.49/1.43  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 2.49/1.43  tff(v1_tex_2, type, v1_tex_2: ($i * $i) > $o).
% 2.49/1.43  tff(v7_struct_0, type, v7_struct_0: $i > $o).
% 2.49/1.43  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.49/1.43  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.49/1.43  tff('#skF_2', type, '#skF_2': $i).
% 2.49/1.43  tff('#skF_3', type, '#skF_3': $i).
% 2.49/1.43  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 2.49/1.43  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.49/1.43  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.49/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.49/1.43  tff(k1_tex_2, type, k1_tex_2: ($i * $i) > $i).
% 2.49/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.49/1.43  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 2.49/1.43  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.49/1.43  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.49/1.43  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.49/1.43  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.49/1.43  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.49/1.43  
% 2.49/1.45  tff(f_155, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (v1_tex_2(k1_tex_2(A, B), A) <=> v1_subset_1(k6_domain_1(u1_struct_0(A), B), u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_tex_2)).
% 2.49/1.45  tff(f_29, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.49/1.45  tff(f_118, axiom, (![A, B]: (((~v2_struct_0(A) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => ((~v2_struct_0(k1_tex_2(A, B)) & v7_struct_0(k1_tex_2(A, B))) & v1_pre_topc(k1_tex_2(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_tex_2)).
% 2.49/1.45  tff(f_104, axiom, (![A, B]: (((~v2_struct_0(A) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => ((~v2_struct_0(k1_tex_2(A, B)) & v1_pre_topc(k1_tex_2(A, B))) & m1_pre_topc(k1_tex_2(A, B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tex_2)).
% 2.49/1.45  tff(f_129, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, A) => ~(v1_subset_1(k6_domain_1(A, B), A) & v1_zfmisc_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_tex_2)).
% 2.49/1.45  tff(f_83, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (v1_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => v1_subset_1(C, u1_struct_0(A)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tex_2)).
% 2.49/1.45  tff(f_90, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (v1_subset_1(B, A) <=> ~(B = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_subset_1)).
% 2.49/1.45  tff(f_36, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 2.49/1.45  tff(f_44, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 2.49/1.45  tff(f_50, axiom, (![A]: ((v7_struct_0(A) & l1_struct_0(A)) => v1_zfmisc_1(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc7_struct_0)).
% 2.49/1.45  tff(f_69, axiom, (![A]: (((~v2_struct_0(A) & v7_struct_0(A)) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (~v2_struct_0(B) => (~v2_struct_0(B) & ~v1_tex_2(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc10_tex_2)).
% 2.49/1.45  tff(f_142, axiom, (![A]: (((~v2_struct_0(A) & ~v7_struct_0(A)) & l1_struct_0(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => v1_subset_1(k6_domain_1(u1_struct_0(A), B), u1_struct_0(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_tex_2)).
% 2.49/1.45  tff(c_44, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_155])).
% 2.49/1.45  tff(c_2, plain, (![A_1]: (l1_struct_0(A_1) | ~l1_pre_topc(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.49/1.45  tff(c_46, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_155])).
% 2.49/1.45  tff(c_42, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_155])).
% 2.49/1.45  tff(c_315, plain, (![A_78, B_79]: (~v2_struct_0(k1_tex_2(A_78, B_79)) | ~m1_subset_1(B_79, u1_struct_0(A_78)) | ~l1_pre_topc(A_78) | v2_struct_0(A_78))), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.49/1.45  tff(c_318, plain, (~v2_struct_0(k1_tex_2('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_42, c_315])).
% 2.49/1.45  tff(c_321, plain, (~v2_struct_0(k1_tex_2('#skF_2', '#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_318])).
% 2.49/1.45  tff(c_322, plain, (~v2_struct_0(k1_tex_2('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_46, c_321])).
% 2.49/1.45  tff(c_333, plain, (![A_86, B_87]: (m1_pre_topc(k1_tex_2(A_86, B_87), A_86) | ~m1_subset_1(B_87, u1_struct_0(A_86)) | ~l1_pre_topc(A_86) | v2_struct_0(A_86))), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.49/1.45  tff(c_335, plain, (m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2') | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_42, c_333])).
% 2.49/1.45  tff(c_338, plain, (m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_335])).
% 2.49/1.45  tff(c_339, plain, (m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_46, c_338])).
% 2.49/1.45  tff(c_54, plain, (v1_tex_2(k1_tex_2('#skF_2', '#skF_3'), '#skF_2') | v1_subset_1(k6_domain_1(u1_struct_0('#skF_2'), '#skF_3'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_155])).
% 2.49/1.45  tff(c_61, plain, (v1_subset_1(k6_domain_1(u1_struct_0('#skF_2'), '#skF_3'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_54])).
% 2.49/1.45  tff(c_80, plain, (![A_45, B_46]: (~v1_zfmisc_1(A_45) | ~v1_subset_1(k6_domain_1(A_45, B_46), A_45) | ~m1_subset_1(B_46, A_45) | v1_xboole_0(A_45))), inference(cnfTransformation, [status(thm)], [f_129])).
% 2.49/1.45  tff(c_83, plain, (~v1_zfmisc_1(u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | v1_xboole_0(u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_61, c_80])).
% 2.49/1.45  tff(c_86, plain, (~v1_zfmisc_1(u1_struct_0('#skF_2')) | v1_xboole_0(u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_83])).
% 2.49/1.45  tff(c_87, plain, (~v1_zfmisc_1(u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_86])).
% 2.49/1.45  tff(c_108, plain, (![A_51, B_52]: (m1_pre_topc(k1_tex_2(A_51, B_52), A_51) | ~m1_subset_1(B_52, u1_struct_0(A_51)) | ~l1_pre_topc(A_51) | v2_struct_0(A_51))), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.49/1.45  tff(c_110, plain, (m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2') | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_42, c_108])).
% 2.49/1.45  tff(c_113, plain, (m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_110])).
% 2.49/1.45  tff(c_114, plain, (m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_46, c_113])).
% 2.49/1.45  tff(c_182, plain, (![A_57, B_58]: (m1_subset_1('#skF_1'(A_57, B_58), k1_zfmisc_1(u1_struct_0(A_57))) | v1_tex_2(B_58, A_57) | ~m1_pre_topc(B_58, A_57) | ~l1_pre_topc(A_57))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.49/1.45  tff(c_22, plain, (![B_21, A_20]: (v1_subset_1(B_21, A_20) | B_21=A_20 | ~m1_subset_1(B_21, k1_zfmisc_1(A_20)))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.49/1.45  tff(c_257, plain, (![A_72, B_73]: (v1_subset_1('#skF_1'(A_72, B_73), u1_struct_0(A_72)) | u1_struct_0(A_72)='#skF_1'(A_72, B_73) | v1_tex_2(B_73, A_72) | ~m1_pre_topc(B_73, A_72) | ~l1_pre_topc(A_72))), inference(resolution, [status(thm)], [c_182, c_22])).
% 2.49/1.45  tff(c_16, plain, (![A_10, B_16]: (~v1_subset_1('#skF_1'(A_10, B_16), u1_struct_0(A_10)) | v1_tex_2(B_16, A_10) | ~m1_pre_topc(B_16, A_10) | ~l1_pre_topc(A_10))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.49/1.45  tff(c_267, plain, (![A_74, B_75]: (u1_struct_0(A_74)='#skF_1'(A_74, B_75) | v1_tex_2(B_75, A_74) | ~m1_pre_topc(B_75, A_74) | ~l1_pre_topc(A_74))), inference(resolution, [status(thm)], [c_257, c_16])).
% 2.49/1.45  tff(c_48, plain, (~v1_subset_1(k6_domain_1(u1_struct_0('#skF_2'), '#skF_3'), u1_struct_0('#skF_2')) | ~v1_tex_2(k1_tex_2('#skF_2', '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_155])).
% 2.49/1.45  tff(c_79, plain, (~v1_tex_2(k1_tex_2('#skF_2', '#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_61, c_48])).
% 2.49/1.45  tff(c_273, plain, ('#skF_1'('#skF_2', k1_tex_2('#skF_2', '#skF_3'))=u1_struct_0('#skF_2') | ~m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_267, c_79])).
% 2.49/1.45  tff(c_277, plain, ('#skF_1'('#skF_2', k1_tex_2('#skF_2', '#skF_3'))=u1_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_114, c_273])).
% 2.49/1.45  tff(c_4, plain, (![B_4, A_2]: (l1_pre_topc(B_4) | ~m1_pre_topc(B_4, A_2) | ~l1_pre_topc(A_2))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.49/1.45  tff(c_122, plain, (l1_pre_topc(k1_tex_2('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_114, c_4])).
% 2.49/1.45  tff(c_125, plain, (l1_pre_topc(k1_tex_2('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_122])).
% 2.49/1.45  tff(c_93, plain, (![A_47, B_48]: (~v2_struct_0(k1_tex_2(A_47, B_48)) | ~m1_subset_1(B_48, u1_struct_0(A_47)) | ~l1_pre_topc(A_47) | v2_struct_0(A_47))), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.49/1.45  tff(c_96, plain, (~v2_struct_0(k1_tex_2('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_42, c_93])).
% 2.49/1.45  tff(c_99, plain, (~v2_struct_0(k1_tex_2('#skF_2', '#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_96])).
% 2.49/1.45  tff(c_100, plain, (~v2_struct_0(k1_tex_2('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_46, c_99])).
% 2.49/1.45  tff(c_101, plain, (![B_49, A_50]: (u1_struct_0(B_49)='#skF_1'(A_50, B_49) | v1_tex_2(B_49, A_50) | ~m1_pre_topc(B_49, A_50) | ~l1_pre_topc(A_50))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.49/1.45  tff(c_104, plain, (u1_struct_0(k1_tex_2('#skF_2', '#skF_3'))='#skF_1'('#skF_2', k1_tex_2('#skF_2', '#skF_3')) | ~m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_101, c_79])).
% 2.49/1.45  tff(c_107, plain, (u1_struct_0(k1_tex_2('#skF_2', '#skF_3'))='#skF_1'('#skF_2', k1_tex_2('#skF_2', '#skF_3')) | ~m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_104])).
% 2.49/1.45  tff(c_128, plain, (u1_struct_0(k1_tex_2('#skF_2', '#skF_3'))='#skF_1'('#skF_2', k1_tex_2('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_114, c_107])).
% 2.49/1.45  tff(c_6, plain, (![A_5]: (~v1_xboole_0(u1_struct_0(A_5)) | ~l1_struct_0(A_5) | v2_struct_0(A_5))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.49/1.45  tff(c_146, plain, (~v1_xboole_0('#skF_1'('#skF_2', k1_tex_2('#skF_2', '#skF_3'))) | ~l1_struct_0(k1_tex_2('#skF_2', '#skF_3')) | v2_struct_0(k1_tex_2('#skF_2', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_128, c_6])).
% 2.49/1.45  tff(c_166, plain, (~v1_xboole_0('#skF_1'('#skF_2', k1_tex_2('#skF_2', '#skF_3'))) | ~l1_struct_0(k1_tex_2('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_100, c_146])).
% 2.49/1.45  tff(c_170, plain, (~l1_struct_0(k1_tex_2('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_166])).
% 2.49/1.45  tff(c_173, plain, (~l1_pre_topc(k1_tex_2('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_2, c_170])).
% 2.49/1.45  tff(c_177, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_125, c_173])).
% 2.49/1.45  tff(c_179, plain, (l1_struct_0(k1_tex_2('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_166])).
% 2.49/1.45  tff(c_70, plain, (![A_43, B_44]: (v7_struct_0(k1_tex_2(A_43, B_44)) | ~m1_subset_1(B_44, u1_struct_0(A_43)) | ~l1_pre_topc(A_43) | v2_struct_0(A_43))), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.49/1.45  tff(c_73, plain, (v7_struct_0(k1_tex_2('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_42, c_70])).
% 2.49/1.45  tff(c_76, plain, (v7_struct_0(k1_tex_2('#skF_2', '#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_73])).
% 2.49/1.45  tff(c_77, plain, (v7_struct_0(k1_tex_2('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_46, c_76])).
% 2.49/1.45  tff(c_8, plain, (![A_6]: (v1_zfmisc_1(u1_struct_0(A_6)) | ~l1_struct_0(A_6) | ~v7_struct_0(A_6))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.49/1.45  tff(c_149, plain, (v1_zfmisc_1('#skF_1'('#skF_2', k1_tex_2('#skF_2', '#skF_3'))) | ~l1_struct_0(k1_tex_2('#skF_2', '#skF_3')) | ~v7_struct_0(k1_tex_2('#skF_2', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_128, c_8])).
% 2.49/1.45  tff(c_168, plain, (v1_zfmisc_1('#skF_1'('#skF_2', k1_tex_2('#skF_2', '#skF_3'))) | ~l1_struct_0(k1_tex_2('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_77, c_149])).
% 2.49/1.45  tff(c_181, plain, (v1_zfmisc_1('#skF_1'('#skF_2', k1_tex_2('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_179, c_168])).
% 2.49/1.45  tff(c_283, plain, (v1_zfmisc_1(u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_277, c_181])).
% 2.49/1.45  tff(c_287, plain, $false, inference(negUnitSimplification, [status(thm)], [c_87, c_283])).
% 2.49/1.45  tff(c_288, plain, (v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_86])).
% 2.49/1.45  tff(c_292, plain, (~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_288, c_6])).
% 2.49/1.45  tff(c_295, plain, (~l1_struct_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_46, c_292])).
% 2.49/1.45  tff(c_298, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_2, c_295])).
% 2.49/1.45  tff(c_302, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_298])).
% 2.49/1.45  tff(c_303, plain, (v1_tex_2(k1_tex_2('#skF_2', '#skF_3'), '#skF_2')), inference(splitRight, [status(thm)], [c_54])).
% 2.49/1.45  tff(c_346, plain, (![B_88, A_89]: (~v1_tex_2(B_88, A_89) | v2_struct_0(B_88) | ~m1_pre_topc(B_88, A_89) | ~l1_pre_topc(A_89) | ~v7_struct_0(A_89) | v2_struct_0(A_89))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.49/1.45  tff(c_352, plain, (v2_struct_0(k1_tex_2('#skF_2', '#skF_3')) | ~m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2') | ~l1_pre_topc('#skF_2') | ~v7_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_303, c_346])).
% 2.49/1.45  tff(c_356, plain, (v2_struct_0(k1_tex_2('#skF_2', '#skF_3')) | ~v7_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_339, c_352])).
% 2.49/1.45  tff(c_357, plain, (~v7_struct_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_46, c_322, c_356])).
% 2.49/1.45  tff(c_372, plain, (![A_96, B_97]: (v1_subset_1(k6_domain_1(u1_struct_0(A_96), B_97), u1_struct_0(A_96)) | ~m1_subset_1(B_97, u1_struct_0(A_96)) | ~l1_struct_0(A_96) | v7_struct_0(A_96) | v2_struct_0(A_96))), inference(cnfTransformation, [status(thm)], [f_142])).
% 2.49/1.45  tff(c_304, plain, (~v1_subset_1(k6_domain_1(u1_struct_0('#skF_2'), '#skF_3'), u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_54])).
% 2.49/1.45  tff(c_378, plain, (~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_struct_0('#skF_2') | v7_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_372, c_304])).
% 2.49/1.45  tff(c_382, plain, (~l1_struct_0('#skF_2') | v7_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_378])).
% 2.49/1.45  tff(c_383, plain, (~l1_struct_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_46, c_357, c_382])).
% 2.49/1.45  tff(c_386, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_2, c_383])).
% 2.49/1.45  tff(c_390, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_386])).
% 2.49/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.49/1.45  
% 2.49/1.45  Inference rules
% 2.49/1.45  ----------------------
% 2.49/1.45  #Ref     : 0
% 2.49/1.45  #Sup     : 49
% 2.49/1.45  #Fact    : 0
% 2.49/1.45  #Define  : 0
% 2.49/1.45  #Split   : 4
% 2.49/1.45  #Chain   : 0
% 2.49/1.45  #Close   : 0
% 2.49/1.45  
% 2.49/1.45  Ordering : KBO
% 2.49/1.45  
% 2.49/1.45  Simplification rules
% 2.49/1.45  ----------------------
% 2.49/1.45  #Subsume      : 7
% 2.49/1.45  #Demod        : 63
% 2.49/1.45  #Tautology    : 8
% 2.49/1.45  #SimpNegUnit  : 24
% 2.49/1.45  #BackRed      : 8
% 2.49/1.45  
% 2.49/1.45  #Partial instantiations: 0
% 2.49/1.45  #Strategies tried      : 1
% 2.49/1.45  
% 2.49/1.45  Timing (in seconds)
% 2.49/1.45  ----------------------
% 2.49/1.45  Preprocessing        : 0.37
% 2.49/1.45  Parsing              : 0.18
% 2.49/1.45  CNF conversion       : 0.03
% 2.49/1.45  Main loop            : 0.26
% 2.49/1.45  Inferencing          : 0.10
% 2.49/1.45  Reduction            : 0.08
% 2.49/1.46  Demodulation         : 0.05
% 2.49/1.46  BG Simplification    : 0.02
% 2.49/1.46  Subsumption          : 0.04
% 2.49/1.46  Abstraction          : 0.02
% 2.49/1.46  MUC search           : 0.00
% 2.49/1.46  Cooper               : 0.00
% 2.49/1.46  Total                : 0.67
% 2.49/1.46  Index Insertion      : 0.00
% 2.49/1.46  Index Deletion       : 0.00
% 2.49/1.46  Index Matching       : 0.00
% 2.49/1.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
