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

% Result     : Theorem 3.28s
% Output     : CNFRefutation 3.39s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 421 expanded)
%              Number of leaves         :   33 ( 154 expanded)
%              Depth                    :   14
%              Number of atoms          :  256 (1213 expanded)
%              Number of equality atoms :   10 (  45 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

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

tff(f_159,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ( v1_tex_2(k1_tex_2(A,B),A)
            <=> v1_subset_1(k6_domain_1(u1_struct_0(A),B),u1_struct_0(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_tex_2)).

tff(f_108,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ( ~ v2_struct_0(k1_tex_2(A,B))
        & v1_pre_topc(k1_tex_2(A,B))
        & m1_pre_topc(k1_tex_2(A,B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tex_2)).

tff(f_44,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_37,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_122,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ( ~ v2_struct_0(k1_tex_2(A,B))
        & v7_struct_0(k1_tex_2(A,B))
        & v1_pre_topc(k1_tex_2(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_tex_2)).

tff(f_87,axiom,(
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

tff(f_94,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( v1_subset_1(B,A)
      <=> B != A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).

tff(f_52,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_146,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ~ ( v1_subset_1(k6_domain_1(u1_struct_0(A),B),u1_struct_0(A))
              & v7_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_tex_2)).

tff(f_133,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & ~ v1_zfmisc_1(A) )
     => ! [B] :
          ( m1_subset_1(B,A)
         => v1_subset_1(k6_domain_1(A,B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tex_2)).

tff(f_59,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_73,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_zfmisc_1(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => ( ~ v1_xboole_0(B)
           => ~ v1_subset_1(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_tex_2)).

tff(c_44,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_46,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_42,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_862,plain,(
    ! [A_137,B_138] :
      ( m1_pre_topc(k1_tex_2(A_137,B_138),A_137)
      | ~ m1_subset_1(B_138,u1_struct_0(A_137))
      | ~ l1_pre_topc(A_137)
      | v2_struct_0(A_137) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_864,plain,
    ( m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_862])).

tff(c_867,plain,
    ( m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_864])).

tff(c_868,plain,(
    m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_867])).

tff(c_6,plain,(
    ! [B_7,A_5] :
      ( l1_pre_topc(B_7)
      | ~ m1_pre_topc(B_7,A_5)
      | ~ l1_pre_topc(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_871,plain,
    ( l1_pre_topc(k1_tex_2('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_868,c_6])).

tff(c_874,plain,(
    l1_pre_topc(k1_tex_2('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_871])).

tff(c_4,plain,(
    ! [A_4] :
      ( l1_struct_0(A_4)
      | ~ l1_pre_topc(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_815,plain,(
    ! [A_129,B_130] :
      ( ~ v2_struct_0(k1_tex_2(A_129,B_130))
      | ~ m1_subset_1(B_130,u1_struct_0(A_129))
      | ~ l1_pre_topc(A_129)
      | v2_struct_0(A_129) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_818,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_815])).

tff(c_821,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_818])).

tff(c_822,plain,(
    ~ v2_struct_0(k1_tex_2('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_821])).

tff(c_54,plain,
    ( v1_tex_2(k1_tex_2('#skF_2','#skF_3'),'#skF_2')
    | v1_subset_1(k6_domain_1(u1_struct_0('#skF_2'),'#skF_3'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_61,plain,(
    v1_subset_1(k6_domain_1(u1_struct_0('#skF_2'),'#skF_3'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_104,plain,(
    ! [A_58,B_59] :
      ( m1_pre_topc(k1_tex_2(A_58,B_59),A_58)
      | ~ m1_subset_1(B_59,u1_struct_0(A_58))
      | ~ l1_pre_topc(A_58)
      | v2_struct_0(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_106,plain,
    ( m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_104])).

tff(c_109,plain,
    ( m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_106])).

tff(c_110,plain,(
    m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_109])).

tff(c_257,plain,(
    ! [A_78,B_79] :
      ( m1_subset_1('#skF_1'(A_78,B_79),k1_zfmisc_1(u1_struct_0(A_78)))
      | v1_tex_2(B_79,A_78)
      | ~ m1_pre_topc(B_79,A_78)
      | ~ l1_pre_topc(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_22,plain,(
    ! [B_26,A_25] :
      ( v1_subset_1(B_26,A_25)
      | B_26 = A_25
      | ~ m1_subset_1(B_26,k1_zfmisc_1(A_25)) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_549,plain,(
    ! [A_115,B_116] :
      ( v1_subset_1('#skF_1'(A_115,B_116),u1_struct_0(A_115))
      | u1_struct_0(A_115) = '#skF_1'(A_115,B_116)
      | v1_tex_2(B_116,A_115)
      | ~ m1_pre_topc(B_116,A_115)
      | ~ l1_pre_topc(A_115) ) ),
    inference(resolution,[status(thm)],[c_257,c_22])).

tff(c_16,plain,(
    ! [A_15,B_21] :
      ( ~ v1_subset_1('#skF_1'(A_15,B_21),u1_struct_0(A_15))
      | v1_tex_2(B_21,A_15)
      | ~ m1_pre_topc(B_21,A_15)
      | ~ l1_pre_topc(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_568,plain,(
    ! [A_117,B_118] :
      ( u1_struct_0(A_117) = '#skF_1'(A_117,B_118)
      | v1_tex_2(B_118,A_117)
      | ~ m1_pre_topc(B_118,A_117)
      | ~ l1_pre_topc(A_117) ) ),
    inference(resolution,[status(thm)],[c_549,c_16])).

tff(c_48,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0('#skF_2'),'#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_tex_2(k1_tex_2('#skF_2','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_79,plain,(
    ~ v1_tex_2(k1_tex_2('#skF_2','#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_48])).

tff(c_575,plain,
    ( '#skF_1'('#skF_2',k1_tex_2('#skF_2','#skF_3')) = u1_struct_0('#skF_2')
    | ~ m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_568,c_79])).

tff(c_579,plain,(
    '#skF_1'('#skF_2',k1_tex_2('#skF_2','#skF_3')) = u1_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_110,c_575])).

tff(c_88,plain,(
    ! [A_54,B_55] :
      ( ~ v2_struct_0(k1_tex_2(A_54,B_55))
      | ~ m1_subset_1(B_55,u1_struct_0(A_54))
      | ~ l1_pre_topc(A_54)
      | v2_struct_0(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_91,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_88])).

tff(c_94,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_91])).

tff(c_95,plain,(
    ~ v2_struct_0(k1_tex_2('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_94])).

tff(c_113,plain,
    ( l1_pre_topc(k1_tex_2('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_110,c_6])).

tff(c_116,plain,(
    l1_pre_topc(k1_tex_2('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_113])).

tff(c_122,plain,(
    ! [B_62,A_63] :
      ( u1_struct_0(B_62) = '#skF_1'(A_63,B_62)
      | v1_tex_2(B_62,A_63)
      | ~ m1_pre_topc(B_62,A_63)
      | ~ l1_pre_topc(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_125,plain,
    ( u1_struct_0(k1_tex_2('#skF_2','#skF_3')) = '#skF_1'('#skF_2',k1_tex_2('#skF_2','#skF_3'))
    | ~ m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_122,c_79])).

tff(c_128,plain,(
    u1_struct_0(k1_tex_2('#skF_2','#skF_3')) = '#skF_1'('#skF_2',k1_tex_2('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_110,c_125])).

tff(c_8,plain,(
    ! [A_8] :
      ( ~ v1_xboole_0(u1_struct_0(A_8))
      | ~ l1_struct_0(A_8)
      | v2_struct_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_155,plain,
    ( ~ v1_xboole_0('#skF_1'('#skF_2',k1_tex_2('#skF_2','#skF_3')))
    | ~ l1_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | v2_struct_0(k1_tex_2('#skF_2','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_128,c_8])).

tff(c_176,plain,
    ( ~ v1_xboole_0('#skF_1'('#skF_2',k1_tex_2('#skF_2','#skF_3')))
    | ~ l1_struct_0(k1_tex_2('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_95,c_155])).

tff(c_178,plain,(
    ~ l1_struct_0(k1_tex_2('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_176])).

tff(c_181,plain,(
    ~ l1_pre_topc(k1_tex_2('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_4,c_178])).

tff(c_185,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_181])).

tff(c_187,plain,(
    l1_struct_0(k1_tex_2('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_176])).

tff(c_80,plain,(
    ! [A_52,B_53] :
      ( v7_struct_0(k1_tex_2(A_52,B_53))
      | ~ m1_subset_1(B_53,u1_struct_0(A_52))
      | ~ l1_pre_topc(A_52)
      | v2_struct_0(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_83,plain,
    ( v7_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_80])).

tff(c_86,plain,
    ( v7_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_83])).

tff(c_87,plain,(
    v7_struct_0(k1_tex_2('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_86])).

tff(c_295,plain,(
    ! [A_81,B_82] :
      ( ~ v7_struct_0(A_81)
      | ~ v1_subset_1(k6_domain_1(u1_struct_0(A_81),B_82),u1_struct_0(A_81))
      | ~ m1_subset_1(B_82,u1_struct_0(A_81))
      | ~ l1_struct_0(A_81)
      | v2_struct_0(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_301,plain,(
    ! [B_82] :
      ( ~ v7_struct_0(k1_tex_2('#skF_2','#skF_3'))
      | ~ v1_subset_1(k6_domain_1(u1_struct_0(k1_tex_2('#skF_2','#skF_3')),B_82),'#skF_1'('#skF_2',k1_tex_2('#skF_2','#skF_3')))
      | ~ m1_subset_1(B_82,u1_struct_0(k1_tex_2('#skF_2','#skF_3')))
      | ~ l1_struct_0(k1_tex_2('#skF_2','#skF_3'))
      | v2_struct_0(k1_tex_2('#skF_2','#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_128,c_295])).

tff(c_313,plain,(
    ! [B_82] :
      ( ~ v1_subset_1(k6_domain_1('#skF_1'('#skF_2',k1_tex_2('#skF_2','#skF_3')),B_82),'#skF_1'('#skF_2',k1_tex_2('#skF_2','#skF_3')))
      | ~ m1_subset_1(B_82,'#skF_1'('#skF_2',k1_tex_2('#skF_2','#skF_3')))
      | v2_struct_0(k1_tex_2('#skF_2','#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_187,c_128,c_128,c_87,c_301])).

tff(c_314,plain,(
    ! [B_82] :
      ( ~ v1_subset_1(k6_domain_1('#skF_1'('#skF_2',k1_tex_2('#skF_2','#skF_3')),B_82),'#skF_1'('#skF_2',k1_tex_2('#skF_2','#skF_3')))
      | ~ m1_subset_1(B_82,'#skF_1'('#skF_2',k1_tex_2('#skF_2','#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_95,c_313])).

tff(c_781,plain,(
    ! [B_125] :
      ( ~ v1_subset_1(k6_domain_1(u1_struct_0('#skF_2'),B_125),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_125,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_579,c_579,c_579,c_314])).

tff(c_788,plain,(
    ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_61,c_781])).

tff(c_795,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_788])).

tff(c_796,plain,(
    v1_tex_2(k1_tex_2('#skF_2','#skF_3'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_839,plain,(
    ! [A_135,B_136] :
      ( v1_subset_1(k6_domain_1(A_135,B_136),A_135)
      | ~ m1_subset_1(B_136,A_135)
      | v1_zfmisc_1(A_135)
      | v1_xboole_0(A_135) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_797,plain,(
    ~ v1_subset_1(k6_domain_1(u1_struct_0('#skF_2'),'#skF_3'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_842,plain,
    ( ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | v1_zfmisc_1(u1_struct_0('#skF_2'))
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_839,c_797])).

tff(c_845,plain,
    ( v1_zfmisc_1(u1_struct_0('#skF_2'))
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_842])).

tff(c_846,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_845])).

tff(c_849,plain,
    ( ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_846,c_8])).

tff(c_852,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_849])).

tff(c_855,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_4,c_852])).

tff(c_859,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_855])).

tff(c_861,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_845])).

tff(c_860,plain,(
    v1_zfmisc_1(u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_845])).

tff(c_10,plain,(
    ! [B_11,A_9] :
      ( m1_subset_1(u1_struct_0(B_11),k1_zfmisc_1(u1_struct_0(A_9)))
      | ~ m1_pre_topc(B_11,A_9)
      | ~ l1_pre_topc(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_921,plain,(
    ! [B_157,A_158] :
      ( v1_subset_1(u1_struct_0(B_157),u1_struct_0(A_158))
      | ~ m1_subset_1(u1_struct_0(B_157),k1_zfmisc_1(u1_struct_0(A_158)))
      | ~ v1_tex_2(B_157,A_158)
      | ~ m1_pre_topc(B_157,A_158)
      | ~ l1_pre_topc(A_158) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_925,plain,(
    ! [B_11,A_9] :
      ( v1_subset_1(u1_struct_0(B_11),u1_struct_0(A_9))
      | ~ v1_tex_2(B_11,A_9)
      | ~ m1_pre_topc(B_11,A_9)
      | ~ l1_pre_topc(A_9) ) ),
    inference(resolution,[status(thm)],[c_10,c_921])).

tff(c_876,plain,(
    ! [B_141,A_142] :
      ( ~ v1_subset_1(B_141,A_142)
      | v1_xboole_0(B_141)
      | ~ m1_subset_1(B_141,k1_zfmisc_1(A_142))
      | ~ v1_zfmisc_1(A_142)
      | v1_xboole_0(A_142) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_955,plain,(
    ! [B_169,A_170] :
      ( ~ v1_subset_1(u1_struct_0(B_169),u1_struct_0(A_170))
      | v1_xboole_0(u1_struct_0(B_169))
      | ~ v1_zfmisc_1(u1_struct_0(A_170))
      | v1_xboole_0(u1_struct_0(A_170))
      | ~ m1_pre_topc(B_169,A_170)
      | ~ l1_pre_topc(A_170) ) ),
    inference(resolution,[status(thm)],[c_10,c_876])).

tff(c_964,plain,(
    ! [B_171,A_172] :
      ( v1_xboole_0(u1_struct_0(B_171))
      | ~ v1_zfmisc_1(u1_struct_0(A_172))
      | v1_xboole_0(u1_struct_0(A_172))
      | ~ v1_tex_2(B_171,A_172)
      | ~ m1_pre_topc(B_171,A_172)
      | ~ l1_pre_topc(A_172) ) ),
    inference(resolution,[status(thm)],[c_925,c_955])).

tff(c_966,plain,(
    ! [B_171] :
      ( v1_xboole_0(u1_struct_0(B_171))
      | v1_xboole_0(u1_struct_0('#skF_2'))
      | ~ v1_tex_2(B_171,'#skF_2')
      | ~ m1_pre_topc(B_171,'#skF_2')
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_860,c_964])).

tff(c_969,plain,(
    ! [B_171] :
      ( v1_xboole_0(u1_struct_0(B_171))
      | v1_xboole_0(u1_struct_0('#skF_2'))
      | ~ v1_tex_2(B_171,'#skF_2')
      | ~ m1_pre_topc(B_171,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_966])).

tff(c_971,plain,(
    ! [B_173] :
      ( v1_xboole_0(u1_struct_0(B_173))
      | ~ v1_tex_2(B_173,'#skF_2')
      | ~ m1_pre_topc(B_173,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_861,c_969])).

tff(c_1009,plain,(
    ! [B_177] :
      ( ~ l1_struct_0(B_177)
      | v2_struct_0(B_177)
      | ~ v1_tex_2(B_177,'#skF_2')
      | ~ m1_pre_topc(B_177,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_971,c_8])).

tff(c_1020,plain,
    ( ~ l1_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | v2_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | ~ m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_796,c_1009])).

tff(c_1029,plain,
    ( ~ l1_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | v2_struct_0(k1_tex_2('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_868,c_1020])).

tff(c_1030,plain,(
    ~ l1_struct_0(k1_tex_2('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_822,c_1029])).

tff(c_1033,plain,(
    ~ l1_pre_topc(k1_tex_2('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_4,c_1030])).

tff(c_1037,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_874,c_1033])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:06:46 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.28/1.52  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.39/1.53  
% 3.39/1.53  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.39/1.53  %$ v1_tex_2 > v1_subset_1 > m1_subset_1 > m1_pre_topc > v7_struct_0 > v2_struct_0 > v1_zfmisc_1 > v1_xboole_0 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k6_domain_1 > k1_tex_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 3.39/1.53  
% 3.39/1.53  %Foreground sorts:
% 3.39/1.53  
% 3.39/1.53  
% 3.39/1.53  %Background operators:
% 3.39/1.53  
% 3.39/1.53  
% 3.39/1.53  %Foreground operators:
% 3.39/1.53  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.39/1.53  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.39/1.53  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 3.39/1.53  tff(v1_tex_2, type, v1_tex_2: ($i * $i) > $o).
% 3.39/1.53  tff(v7_struct_0, type, v7_struct_0: $i > $o).
% 3.39/1.53  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.39/1.53  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 3.39/1.53  tff('#skF_2', type, '#skF_2': $i).
% 3.39/1.53  tff('#skF_3', type, '#skF_3': $i).
% 3.39/1.53  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 3.39/1.53  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.39/1.53  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.39/1.53  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.39/1.53  tff(k1_tex_2, type, k1_tex_2: ($i * $i) > $i).
% 3.39/1.53  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.39/1.53  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 3.39/1.53  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.39/1.53  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.39/1.53  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.39/1.53  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.39/1.53  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.39/1.53  
% 3.39/1.55  tff(f_159, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (v1_tex_2(k1_tex_2(A, B), A) <=> v1_subset_1(k6_domain_1(u1_struct_0(A), B), u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_tex_2)).
% 3.39/1.55  tff(f_108, axiom, (![A, B]: (((~v2_struct_0(A) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => ((~v2_struct_0(k1_tex_2(A, B)) & v1_pre_topc(k1_tex_2(A, B))) & m1_pre_topc(k1_tex_2(A, B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tex_2)).
% 3.39/1.55  tff(f_44, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 3.39/1.55  tff(f_37, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.39/1.55  tff(f_122, axiom, (![A, B]: (((~v2_struct_0(A) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => ((~v2_struct_0(k1_tex_2(A, B)) & v7_struct_0(k1_tex_2(A, B))) & v1_pre_topc(k1_tex_2(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_tex_2)).
% 3.39/1.55  tff(f_87, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (v1_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => v1_subset_1(C, u1_struct_0(A)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tex_2)).
% 3.39/1.55  tff(f_94, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (v1_subset_1(B, A) <=> ~(B = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_subset_1)).
% 3.39/1.55  tff(f_52, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 3.39/1.55  tff(f_146, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => ~(v1_subset_1(k6_domain_1(u1_struct_0(A), B), u1_struct_0(A)) & v7_struct_0(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_tex_2)).
% 3.39/1.55  tff(f_133, axiom, (![A]: ((~v1_xboole_0(A) & ~v1_zfmisc_1(A)) => (![B]: (m1_subset_1(B, A) => v1_subset_1(k6_domain_1(A, B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_tex_2)).
% 3.39/1.55  tff(f_59, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 3.39/1.55  tff(f_73, axiom, (![A]: ((~v1_xboole_0(A) & v1_zfmisc_1(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (~v1_xboole_0(B) => ~v1_subset_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_tex_2)).
% 3.39/1.55  tff(c_44, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_159])).
% 3.39/1.55  tff(c_46, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_159])).
% 3.39/1.55  tff(c_42, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_159])).
% 3.39/1.55  tff(c_862, plain, (![A_137, B_138]: (m1_pre_topc(k1_tex_2(A_137, B_138), A_137) | ~m1_subset_1(B_138, u1_struct_0(A_137)) | ~l1_pre_topc(A_137) | v2_struct_0(A_137))), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.39/1.55  tff(c_864, plain, (m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2') | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_42, c_862])).
% 3.39/1.55  tff(c_867, plain, (m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_864])).
% 3.39/1.55  tff(c_868, plain, (m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_46, c_867])).
% 3.39/1.55  tff(c_6, plain, (![B_7, A_5]: (l1_pre_topc(B_7) | ~m1_pre_topc(B_7, A_5) | ~l1_pre_topc(A_5))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.39/1.55  tff(c_871, plain, (l1_pre_topc(k1_tex_2('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_868, c_6])).
% 3.39/1.55  tff(c_874, plain, (l1_pre_topc(k1_tex_2('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_871])).
% 3.39/1.55  tff(c_4, plain, (![A_4]: (l1_struct_0(A_4) | ~l1_pre_topc(A_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.39/1.55  tff(c_815, plain, (![A_129, B_130]: (~v2_struct_0(k1_tex_2(A_129, B_130)) | ~m1_subset_1(B_130, u1_struct_0(A_129)) | ~l1_pre_topc(A_129) | v2_struct_0(A_129))), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.39/1.55  tff(c_818, plain, (~v2_struct_0(k1_tex_2('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_42, c_815])).
% 3.39/1.55  tff(c_821, plain, (~v2_struct_0(k1_tex_2('#skF_2', '#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_818])).
% 3.39/1.55  tff(c_822, plain, (~v2_struct_0(k1_tex_2('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_46, c_821])).
% 3.39/1.55  tff(c_54, plain, (v1_tex_2(k1_tex_2('#skF_2', '#skF_3'), '#skF_2') | v1_subset_1(k6_domain_1(u1_struct_0('#skF_2'), '#skF_3'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_159])).
% 3.39/1.55  tff(c_61, plain, (v1_subset_1(k6_domain_1(u1_struct_0('#skF_2'), '#skF_3'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_54])).
% 3.39/1.55  tff(c_104, plain, (![A_58, B_59]: (m1_pre_topc(k1_tex_2(A_58, B_59), A_58) | ~m1_subset_1(B_59, u1_struct_0(A_58)) | ~l1_pre_topc(A_58) | v2_struct_0(A_58))), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.39/1.55  tff(c_106, plain, (m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2') | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_42, c_104])).
% 3.39/1.55  tff(c_109, plain, (m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_106])).
% 3.39/1.55  tff(c_110, plain, (m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_46, c_109])).
% 3.39/1.55  tff(c_257, plain, (![A_78, B_79]: (m1_subset_1('#skF_1'(A_78, B_79), k1_zfmisc_1(u1_struct_0(A_78))) | v1_tex_2(B_79, A_78) | ~m1_pre_topc(B_79, A_78) | ~l1_pre_topc(A_78))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.39/1.55  tff(c_22, plain, (![B_26, A_25]: (v1_subset_1(B_26, A_25) | B_26=A_25 | ~m1_subset_1(B_26, k1_zfmisc_1(A_25)))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.39/1.55  tff(c_549, plain, (![A_115, B_116]: (v1_subset_1('#skF_1'(A_115, B_116), u1_struct_0(A_115)) | u1_struct_0(A_115)='#skF_1'(A_115, B_116) | v1_tex_2(B_116, A_115) | ~m1_pre_topc(B_116, A_115) | ~l1_pre_topc(A_115))), inference(resolution, [status(thm)], [c_257, c_22])).
% 3.39/1.55  tff(c_16, plain, (![A_15, B_21]: (~v1_subset_1('#skF_1'(A_15, B_21), u1_struct_0(A_15)) | v1_tex_2(B_21, A_15) | ~m1_pre_topc(B_21, A_15) | ~l1_pre_topc(A_15))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.39/1.55  tff(c_568, plain, (![A_117, B_118]: (u1_struct_0(A_117)='#skF_1'(A_117, B_118) | v1_tex_2(B_118, A_117) | ~m1_pre_topc(B_118, A_117) | ~l1_pre_topc(A_117))), inference(resolution, [status(thm)], [c_549, c_16])).
% 3.39/1.55  tff(c_48, plain, (~v1_subset_1(k6_domain_1(u1_struct_0('#skF_2'), '#skF_3'), u1_struct_0('#skF_2')) | ~v1_tex_2(k1_tex_2('#skF_2', '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_159])).
% 3.39/1.55  tff(c_79, plain, (~v1_tex_2(k1_tex_2('#skF_2', '#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_61, c_48])).
% 3.39/1.55  tff(c_575, plain, ('#skF_1'('#skF_2', k1_tex_2('#skF_2', '#skF_3'))=u1_struct_0('#skF_2') | ~m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_568, c_79])).
% 3.39/1.55  tff(c_579, plain, ('#skF_1'('#skF_2', k1_tex_2('#skF_2', '#skF_3'))=u1_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_110, c_575])).
% 3.39/1.55  tff(c_88, plain, (![A_54, B_55]: (~v2_struct_0(k1_tex_2(A_54, B_55)) | ~m1_subset_1(B_55, u1_struct_0(A_54)) | ~l1_pre_topc(A_54) | v2_struct_0(A_54))), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.39/1.55  tff(c_91, plain, (~v2_struct_0(k1_tex_2('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_42, c_88])).
% 3.39/1.55  tff(c_94, plain, (~v2_struct_0(k1_tex_2('#skF_2', '#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_91])).
% 3.39/1.55  tff(c_95, plain, (~v2_struct_0(k1_tex_2('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_46, c_94])).
% 3.39/1.55  tff(c_113, plain, (l1_pre_topc(k1_tex_2('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_110, c_6])).
% 3.39/1.55  tff(c_116, plain, (l1_pre_topc(k1_tex_2('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_113])).
% 3.39/1.55  tff(c_122, plain, (![B_62, A_63]: (u1_struct_0(B_62)='#skF_1'(A_63, B_62) | v1_tex_2(B_62, A_63) | ~m1_pre_topc(B_62, A_63) | ~l1_pre_topc(A_63))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.39/1.55  tff(c_125, plain, (u1_struct_0(k1_tex_2('#skF_2', '#skF_3'))='#skF_1'('#skF_2', k1_tex_2('#skF_2', '#skF_3')) | ~m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_122, c_79])).
% 3.39/1.55  tff(c_128, plain, (u1_struct_0(k1_tex_2('#skF_2', '#skF_3'))='#skF_1'('#skF_2', k1_tex_2('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_110, c_125])).
% 3.39/1.55  tff(c_8, plain, (![A_8]: (~v1_xboole_0(u1_struct_0(A_8)) | ~l1_struct_0(A_8) | v2_struct_0(A_8))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.39/1.55  tff(c_155, plain, (~v1_xboole_0('#skF_1'('#skF_2', k1_tex_2('#skF_2', '#skF_3'))) | ~l1_struct_0(k1_tex_2('#skF_2', '#skF_3')) | v2_struct_0(k1_tex_2('#skF_2', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_128, c_8])).
% 3.39/1.55  tff(c_176, plain, (~v1_xboole_0('#skF_1'('#skF_2', k1_tex_2('#skF_2', '#skF_3'))) | ~l1_struct_0(k1_tex_2('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_95, c_155])).
% 3.39/1.55  tff(c_178, plain, (~l1_struct_0(k1_tex_2('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_176])).
% 3.39/1.55  tff(c_181, plain, (~l1_pre_topc(k1_tex_2('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_4, c_178])).
% 3.39/1.55  tff(c_185, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_116, c_181])).
% 3.39/1.55  tff(c_187, plain, (l1_struct_0(k1_tex_2('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_176])).
% 3.39/1.55  tff(c_80, plain, (![A_52, B_53]: (v7_struct_0(k1_tex_2(A_52, B_53)) | ~m1_subset_1(B_53, u1_struct_0(A_52)) | ~l1_pre_topc(A_52) | v2_struct_0(A_52))), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.39/1.55  tff(c_83, plain, (v7_struct_0(k1_tex_2('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_42, c_80])).
% 3.39/1.55  tff(c_86, plain, (v7_struct_0(k1_tex_2('#skF_2', '#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_83])).
% 3.39/1.55  tff(c_87, plain, (v7_struct_0(k1_tex_2('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_46, c_86])).
% 3.39/1.55  tff(c_295, plain, (![A_81, B_82]: (~v7_struct_0(A_81) | ~v1_subset_1(k6_domain_1(u1_struct_0(A_81), B_82), u1_struct_0(A_81)) | ~m1_subset_1(B_82, u1_struct_0(A_81)) | ~l1_struct_0(A_81) | v2_struct_0(A_81))), inference(cnfTransformation, [status(thm)], [f_146])).
% 3.39/1.55  tff(c_301, plain, (![B_82]: (~v7_struct_0(k1_tex_2('#skF_2', '#skF_3')) | ~v1_subset_1(k6_domain_1(u1_struct_0(k1_tex_2('#skF_2', '#skF_3')), B_82), '#skF_1'('#skF_2', k1_tex_2('#skF_2', '#skF_3'))) | ~m1_subset_1(B_82, u1_struct_0(k1_tex_2('#skF_2', '#skF_3'))) | ~l1_struct_0(k1_tex_2('#skF_2', '#skF_3')) | v2_struct_0(k1_tex_2('#skF_2', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_128, c_295])).
% 3.39/1.55  tff(c_313, plain, (![B_82]: (~v1_subset_1(k6_domain_1('#skF_1'('#skF_2', k1_tex_2('#skF_2', '#skF_3')), B_82), '#skF_1'('#skF_2', k1_tex_2('#skF_2', '#skF_3'))) | ~m1_subset_1(B_82, '#skF_1'('#skF_2', k1_tex_2('#skF_2', '#skF_3'))) | v2_struct_0(k1_tex_2('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_187, c_128, c_128, c_87, c_301])).
% 3.39/1.55  tff(c_314, plain, (![B_82]: (~v1_subset_1(k6_domain_1('#skF_1'('#skF_2', k1_tex_2('#skF_2', '#skF_3')), B_82), '#skF_1'('#skF_2', k1_tex_2('#skF_2', '#skF_3'))) | ~m1_subset_1(B_82, '#skF_1'('#skF_2', k1_tex_2('#skF_2', '#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_95, c_313])).
% 3.39/1.55  tff(c_781, plain, (![B_125]: (~v1_subset_1(k6_domain_1(u1_struct_0('#skF_2'), B_125), u1_struct_0('#skF_2')) | ~m1_subset_1(B_125, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_579, c_579, c_579, c_314])).
% 3.39/1.55  tff(c_788, plain, (~m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_61, c_781])).
% 3.39/1.55  tff(c_795, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_788])).
% 3.39/1.55  tff(c_796, plain, (v1_tex_2(k1_tex_2('#skF_2', '#skF_3'), '#skF_2')), inference(splitRight, [status(thm)], [c_54])).
% 3.39/1.55  tff(c_839, plain, (![A_135, B_136]: (v1_subset_1(k6_domain_1(A_135, B_136), A_135) | ~m1_subset_1(B_136, A_135) | v1_zfmisc_1(A_135) | v1_xboole_0(A_135))), inference(cnfTransformation, [status(thm)], [f_133])).
% 3.39/1.55  tff(c_797, plain, (~v1_subset_1(k6_domain_1(u1_struct_0('#skF_2'), '#skF_3'), u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_54])).
% 3.39/1.55  tff(c_842, plain, (~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | v1_zfmisc_1(u1_struct_0('#skF_2')) | v1_xboole_0(u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_839, c_797])).
% 3.39/1.55  tff(c_845, plain, (v1_zfmisc_1(u1_struct_0('#skF_2')) | v1_xboole_0(u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_842])).
% 3.39/1.55  tff(c_846, plain, (v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_845])).
% 3.39/1.55  tff(c_849, plain, (~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_846, c_8])).
% 3.39/1.55  tff(c_852, plain, (~l1_struct_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_46, c_849])).
% 3.39/1.55  tff(c_855, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_4, c_852])).
% 3.39/1.55  tff(c_859, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_855])).
% 3.39/1.55  tff(c_861, plain, (~v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_845])).
% 3.39/1.55  tff(c_860, plain, (v1_zfmisc_1(u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_845])).
% 3.39/1.55  tff(c_10, plain, (![B_11, A_9]: (m1_subset_1(u1_struct_0(B_11), k1_zfmisc_1(u1_struct_0(A_9))) | ~m1_pre_topc(B_11, A_9) | ~l1_pre_topc(A_9))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.39/1.55  tff(c_921, plain, (![B_157, A_158]: (v1_subset_1(u1_struct_0(B_157), u1_struct_0(A_158)) | ~m1_subset_1(u1_struct_0(B_157), k1_zfmisc_1(u1_struct_0(A_158))) | ~v1_tex_2(B_157, A_158) | ~m1_pre_topc(B_157, A_158) | ~l1_pre_topc(A_158))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.39/1.55  tff(c_925, plain, (![B_11, A_9]: (v1_subset_1(u1_struct_0(B_11), u1_struct_0(A_9)) | ~v1_tex_2(B_11, A_9) | ~m1_pre_topc(B_11, A_9) | ~l1_pre_topc(A_9))), inference(resolution, [status(thm)], [c_10, c_921])).
% 3.39/1.55  tff(c_876, plain, (![B_141, A_142]: (~v1_subset_1(B_141, A_142) | v1_xboole_0(B_141) | ~m1_subset_1(B_141, k1_zfmisc_1(A_142)) | ~v1_zfmisc_1(A_142) | v1_xboole_0(A_142))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.39/1.55  tff(c_955, plain, (![B_169, A_170]: (~v1_subset_1(u1_struct_0(B_169), u1_struct_0(A_170)) | v1_xboole_0(u1_struct_0(B_169)) | ~v1_zfmisc_1(u1_struct_0(A_170)) | v1_xboole_0(u1_struct_0(A_170)) | ~m1_pre_topc(B_169, A_170) | ~l1_pre_topc(A_170))), inference(resolution, [status(thm)], [c_10, c_876])).
% 3.39/1.55  tff(c_964, plain, (![B_171, A_172]: (v1_xboole_0(u1_struct_0(B_171)) | ~v1_zfmisc_1(u1_struct_0(A_172)) | v1_xboole_0(u1_struct_0(A_172)) | ~v1_tex_2(B_171, A_172) | ~m1_pre_topc(B_171, A_172) | ~l1_pre_topc(A_172))), inference(resolution, [status(thm)], [c_925, c_955])).
% 3.39/1.55  tff(c_966, plain, (![B_171]: (v1_xboole_0(u1_struct_0(B_171)) | v1_xboole_0(u1_struct_0('#skF_2')) | ~v1_tex_2(B_171, '#skF_2') | ~m1_pre_topc(B_171, '#skF_2') | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_860, c_964])).
% 3.39/1.55  tff(c_969, plain, (![B_171]: (v1_xboole_0(u1_struct_0(B_171)) | v1_xboole_0(u1_struct_0('#skF_2')) | ~v1_tex_2(B_171, '#skF_2') | ~m1_pre_topc(B_171, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_966])).
% 3.39/1.55  tff(c_971, plain, (![B_173]: (v1_xboole_0(u1_struct_0(B_173)) | ~v1_tex_2(B_173, '#skF_2') | ~m1_pre_topc(B_173, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_861, c_969])).
% 3.39/1.55  tff(c_1009, plain, (![B_177]: (~l1_struct_0(B_177) | v2_struct_0(B_177) | ~v1_tex_2(B_177, '#skF_2') | ~m1_pre_topc(B_177, '#skF_2'))), inference(resolution, [status(thm)], [c_971, c_8])).
% 3.39/1.55  tff(c_1020, plain, (~l1_struct_0(k1_tex_2('#skF_2', '#skF_3')) | v2_struct_0(k1_tex_2('#skF_2', '#skF_3')) | ~m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2')), inference(resolution, [status(thm)], [c_796, c_1009])).
% 3.39/1.55  tff(c_1029, plain, (~l1_struct_0(k1_tex_2('#skF_2', '#skF_3')) | v2_struct_0(k1_tex_2('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_868, c_1020])).
% 3.39/1.55  tff(c_1030, plain, (~l1_struct_0(k1_tex_2('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_822, c_1029])).
% 3.39/1.55  tff(c_1033, plain, (~l1_pre_topc(k1_tex_2('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_4, c_1030])).
% 3.39/1.55  tff(c_1037, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_874, c_1033])).
% 3.39/1.55  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.39/1.55  
% 3.39/1.55  Inference rules
% 3.39/1.55  ----------------------
% 3.39/1.55  #Ref     : 0
% 3.39/1.55  #Sup     : 173
% 3.39/1.55  #Fact    : 0
% 3.39/1.55  #Define  : 0
% 3.39/1.55  #Split   : 11
% 3.39/1.55  #Chain   : 0
% 3.39/1.55  #Close   : 0
% 3.39/1.55  
% 3.39/1.55  Ordering : KBO
% 3.39/1.55  
% 3.39/1.55  Simplification rules
% 3.39/1.55  ----------------------
% 3.39/1.55  #Subsume      : 55
% 3.39/1.55  #Demod        : 168
% 3.39/1.55  #Tautology    : 18
% 3.39/1.55  #SimpNegUnit  : 48
% 3.39/1.55  #BackRed      : 21
% 3.39/1.55  
% 3.39/1.55  #Partial instantiations: 0
% 3.39/1.55  #Strategies tried      : 1
% 3.39/1.55  
% 3.39/1.55  Timing (in seconds)
% 3.39/1.55  ----------------------
% 3.39/1.55  Preprocessing        : 0.34
% 3.39/1.55  Parsing              : 0.18
% 3.39/1.55  CNF conversion       : 0.02
% 3.39/1.55  Main loop            : 0.40
% 3.39/1.55  Inferencing          : 0.15
% 3.39/1.55  Reduction            : 0.12
% 3.39/1.55  Demodulation         : 0.08
% 3.39/1.55  BG Simplification    : 0.02
% 3.39/1.55  Subsumption          : 0.07
% 3.39/1.55  Abstraction          : 0.02
% 3.39/1.55  MUC search           : 0.00
% 3.39/1.56  Cooper               : 0.00
% 3.39/1.56  Total                : 0.77
% 3.39/1.56  Index Insertion      : 0.00
% 3.39/1.56  Index Deletion       : 0.00
% 3.39/1.56  Index Matching       : 0.00
% 3.39/1.56  BG Taut test         : 0.00
%------------------------------------------------------------------------------
