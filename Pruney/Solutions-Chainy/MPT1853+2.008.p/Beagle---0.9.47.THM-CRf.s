%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:00 EST 2020

% Result     : Theorem 3.06s
% Output     : CNFRefutation 3.14s
% Verified   : 
% Statistics : Number of formulae       :  141 ( 546 expanded)
%              Number of leaves         :   35 ( 190 expanded)
%              Depth                    :   18
%              Number of atoms          :  292 (1596 expanded)
%              Number of equality atoms :   20 (  62 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_tex_2 > v1_subset_1 > m1_subset_1 > m1_pre_topc > v7_struct_0 > v2_struct_0 > v1_zfmisc_1 > v1_xboole_0 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k6_domain_1 > k1_tex_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

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

tff(f_192,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ( v1_tex_2(k1_tex_2(A,B),A)
            <=> v1_subset_1(k6_domain_1(u1_struct_0(A),B),u1_struct_0(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_tex_2)).

tff(f_124,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ( ~ v2_struct_0(k1_tex_2(A,B))
        & v7_struct_0(k1_tex_2(A,B))
        & v1_pre_topc(k1_tex_2(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_tex_2)).

tff(f_110,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ( ~ v2_struct_0(k1_tex_2(A,B))
        & v1_pre_topc(k1_tex_2(A,B))
        & m1_pre_topc(k1_tex_2(A,B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tex_2)).

tff(f_35,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_144,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & ~ v7_struct_0(A)
        & l1_struct_0(A) )
     => ? [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
          & ~ v1_xboole_0(B)
          & ~ v1_zfmisc_1(B)
          & ~ v1_subset_1(B,u1_struct_0(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc5_tex_2)).

tff(f_96,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( v1_subset_1(B,A)
      <=> B != A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).

tff(f_56,axiom,(
    ! [A] :
      ( ( v7_struct_0(A)
        & l1_struct_0(A) )
     => v1_zfmisc_1(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_struct_0)).

tff(f_155,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,A)
         => ~ ( v1_subset_1(k6_domain_1(A,B),A)
              & v1_zfmisc_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tex_2)).

tff(f_89,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ( v1_tex_2(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( C = u1_struct_0(B)
                 => v1_subset_1(C,u1_struct_0(A)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tex_2)).

tff(f_42,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_50,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_75,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v7_struct_0(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ( ~ v2_struct_0(B)
           => ( ~ v2_struct_0(B)
              & ~ v1_tex_2(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc10_tex_2)).

tff(f_166,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & ~ v1_zfmisc_1(A) )
     => ! [B] :
          ( m1_subset_1(B,A)
         => v1_subset_1(k6_domain_1(A,B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tex_2)).

tff(c_58,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_56,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_54,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_544,plain,(
    ! [A_104,B_105] :
      ( ~ v2_struct_0(k1_tex_2(A_104,B_105))
      | ~ m1_subset_1(B_105,u1_struct_0(A_104))
      | ~ l1_pre_topc(A_104)
      | v2_struct_0(A_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_547,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_3','#skF_4'))
    | ~ l1_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_544])).

tff(c_550,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_3','#skF_4'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_547])).

tff(c_551,plain,(
    ~ v2_struct_0(k1_tex_2('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_550])).

tff(c_603,plain,(
    ! [A_115,B_116] :
      ( m1_pre_topc(k1_tex_2(A_115,B_116),A_115)
      | ~ m1_subset_1(B_116,u1_struct_0(A_115))
      | ~ l1_pre_topc(A_115)
      | v2_struct_0(A_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_605,plain,
    ( m1_pre_topc(k1_tex_2('#skF_3','#skF_4'),'#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_603])).

tff(c_608,plain,
    ( m1_pre_topc(k1_tex_2('#skF_3','#skF_4'),'#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_605])).

tff(c_609,plain,(
    m1_pre_topc(k1_tex_2('#skF_3','#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_608])).

tff(c_4,plain,(
    ! [A_2] :
      ( l1_struct_0(A_2)
      | ~ l1_pre_topc(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_97,plain,(
    ! [A_57] :
      ( m1_subset_1('#skF_2'(A_57),k1_zfmisc_1(u1_struct_0(A_57)))
      | ~ l1_struct_0(A_57)
      | v7_struct_0(A_57)
      | v2_struct_0(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_24,plain,(
    ! [B_22,A_21] :
      ( v1_subset_1(B_22,A_21)
      | B_22 = A_21
      | ~ m1_subset_1(B_22,k1_zfmisc_1(A_21)) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_238,plain,(
    ! [A_77] :
      ( v1_subset_1('#skF_2'(A_77),u1_struct_0(A_77))
      | u1_struct_0(A_77) = '#skF_2'(A_77)
      | ~ l1_struct_0(A_77)
      | v7_struct_0(A_77)
      | v2_struct_0(A_77) ) ),
    inference(resolution,[status(thm)],[c_97,c_24])).

tff(c_40,plain,(
    ! [A_27] :
      ( ~ v1_subset_1('#skF_2'(A_27),u1_struct_0(A_27))
      | ~ l1_struct_0(A_27)
      | v7_struct_0(A_27)
      | v2_struct_0(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_249,plain,(
    ! [A_78] :
      ( u1_struct_0(A_78) = '#skF_2'(A_78)
      | ~ l1_struct_0(A_78)
      | v7_struct_0(A_78)
      | v2_struct_0(A_78) ) ),
    inference(resolution,[status(thm)],[c_238,c_40])).

tff(c_10,plain,(
    ! [A_7] :
      ( v1_zfmisc_1(u1_struct_0(A_7))
      | ~ l1_struct_0(A_7)
      | ~ v7_struct_0(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_66,plain,
    ( v1_tex_2(k1_tex_2('#skF_3','#skF_4'),'#skF_3')
    | v1_subset_1(k6_domain_1(u1_struct_0('#skF_3'),'#skF_4'),u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_73,plain,(
    v1_subset_1(k6_domain_1(u1_struct_0('#skF_3'),'#skF_4'),u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_102,plain,(
    ! [A_58,B_59] :
      ( ~ v1_zfmisc_1(A_58)
      | ~ v1_subset_1(k6_domain_1(A_58,B_59),A_58)
      | ~ m1_subset_1(B_59,A_58)
      | v1_xboole_0(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_108,plain,
    ( ~ v1_zfmisc_1(u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_73,c_102])).

tff(c_112,plain,
    ( ~ v1_zfmisc_1(u1_struct_0('#skF_3'))
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_108])).

tff(c_113,plain,(
    ~ v1_zfmisc_1(u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_112])).

tff(c_117,plain,
    ( ~ l1_struct_0('#skF_3')
    | ~ v7_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_10,c_113])).

tff(c_126,plain,(
    ~ v7_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_117])).

tff(c_252,plain,
    ( u1_struct_0('#skF_3') = '#skF_2'('#skF_3')
    | ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_249,c_126])).

tff(c_255,plain,
    ( u1_struct_0('#skF_3') = '#skF_2'('#skF_3')
    | ~ l1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_252])).

tff(c_256,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_255])).

tff(c_259,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_4,c_256])).

tff(c_263,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_259])).

tff(c_264,plain,(
    u1_struct_0('#skF_3') = '#skF_2'('#skF_3') ),
    inference(splitRight,[status(thm)],[c_255])).

tff(c_266,plain,(
    ~ v1_zfmisc_1('#skF_2'('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_264,c_113])).

tff(c_131,plain,(
    ! [A_62,B_63] :
      ( m1_pre_topc(k1_tex_2(A_62,B_63),A_62)
      | ~ m1_subset_1(B_63,u1_struct_0(A_62))
      | ~ l1_pre_topc(A_62)
      | v2_struct_0(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_133,plain,
    ( m1_pre_topc(k1_tex_2('#skF_3','#skF_4'),'#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_131])).

tff(c_136,plain,
    ( m1_pre_topc(k1_tex_2('#skF_3','#skF_4'),'#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_133])).

tff(c_137,plain,(
    m1_pre_topc(k1_tex_2('#skF_3','#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_136])).

tff(c_22,plain,(
    ! [A_11,B_17] :
      ( m1_subset_1('#skF_1'(A_11,B_17),k1_zfmisc_1(u1_struct_0(A_11)))
      | v1_tex_2(B_17,A_11)
      | ~ m1_pre_topc(B_17,A_11)
      | ~ l1_pre_topc(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_272,plain,(
    ! [B_17] :
      ( m1_subset_1('#skF_1'('#skF_3',B_17),k1_zfmisc_1('#skF_2'('#skF_3')))
      | v1_tex_2(B_17,'#skF_3')
      | ~ m1_pre_topc(B_17,'#skF_3')
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_264,c_22])).

tff(c_401,plain,(
    ! [B_86] :
      ( m1_subset_1('#skF_1'('#skF_3',B_86),k1_zfmisc_1('#skF_2'('#skF_3')))
      | v1_tex_2(B_86,'#skF_3')
      | ~ m1_pre_topc(B_86,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_272])).

tff(c_469,plain,(
    ! [B_95] :
      ( v1_subset_1('#skF_1'('#skF_3',B_95),'#skF_2'('#skF_3'))
      | '#skF_2'('#skF_3') = '#skF_1'('#skF_3',B_95)
      | v1_tex_2(B_95,'#skF_3')
      | ~ m1_pre_topc(B_95,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_401,c_24])).

tff(c_18,plain,(
    ! [A_11,B_17] :
      ( ~ v1_subset_1('#skF_1'(A_11,B_17),u1_struct_0(A_11))
      | v1_tex_2(B_17,A_11)
      | ~ m1_pre_topc(B_17,A_11)
      | ~ l1_pre_topc(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_275,plain,(
    ! [B_17] :
      ( ~ v1_subset_1('#skF_1'('#skF_3',B_17),'#skF_2'('#skF_3'))
      | v1_tex_2(B_17,'#skF_3')
      | ~ m1_pre_topc(B_17,'#skF_3')
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_264,c_18])).

tff(c_304,plain,(
    ! [B_17] :
      ( ~ v1_subset_1('#skF_1'('#skF_3',B_17),'#skF_2'('#skF_3'))
      | v1_tex_2(B_17,'#skF_3')
      | ~ m1_pre_topc(B_17,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_275])).

tff(c_474,plain,(
    ! [B_96] :
      ( '#skF_2'('#skF_3') = '#skF_1'('#skF_3',B_96)
      | v1_tex_2(B_96,'#skF_3')
      | ~ m1_pre_topc(B_96,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_469,c_304])).

tff(c_60,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0('#skF_3'),'#skF_4'),u1_struct_0('#skF_3'))
    | ~ v1_tex_2(k1_tex_2('#skF_3','#skF_4'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_79,plain,(
    ~ v1_tex_2(k1_tex_2('#skF_3','#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_60])).

tff(c_480,plain,
    ( '#skF_1'('#skF_3',k1_tex_2('#skF_3','#skF_4')) = '#skF_2'('#skF_3')
    | ~ m1_pre_topc(k1_tex_2('#skF_3','#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_474,c_79])).

tff(c_487,plain,(
    '#skF_1'('#skF_3',k1_tex_2('#skF_3','#skF_4')) = '#skF_2'('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_480])).

tff(c_6,plain,(
    ! [B_5,A_3] :
      ( l1_pre_topc(B_5)
      | ~ m1_pre_topc(B_5,A_3)
      | ~ l1_pre_topc(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_140,plain,
    ( l1_pre_topc(k1_tex_2('#skF_3','#skF_4'))
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_137,c_6])).

tff(c_143,plain,(
    l1_pre_topc(k1_tex_2('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_140])).

tff(c_118,plain,(
    ! [A_60,B_61] :
      ( v7_struct_0(k1_tex_2(A_60,B_61))
      | ~ m1_subset_1(B_61,u1_struct_0(A_60))
      | ~ l1_pre_topc(A_60)
      | v2_struct_0(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_121,plain,
    ( v7_struct_0(k1_tex_2('#skF_3','#skF_4'))
    | ~ l1_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_118])).

tff(c_124,plain,
    ( v7_struct_0(k1_tex_2('#skF_3','#skF_4'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_121])).

tff(c_125,plain,(
    v7_struct_0(k1_tex_2('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_124])).

tff(c_144,plain,(
    ! [B_64,A_65] :
      ( u1_struct_0(B_64) = '#skF_1'(A_65,B_64)
      | v1_tex_2(B_64,A_65)
      | ~ m1_pre_topc(B_64,A_65)
      | ~ l1_pre_topc(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_147,plain,
    ( u1_struct_0(k1_tex_2('#skF_3','#skF_4')) = '#skF_1'('#skF_3',k1_tex_2('#skF_3','#skF_4'))
    | ~ m1_pre_topc(k1_tex_2('#skF_3','#skF_4'),'#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_144,c_79])).

tff(c_150,plain,(
    u1_struct_0(k1_tex_2('#skF_3','#skF_4')) = '#skF_1'('#skF_3',k1_tex_2('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_137,c_147])).

tff(c_171,plain,
    ( v1_zfmisc_1('#skF_1'('#skF_3',k1_tex_2('#skF_3','#skF_4')))
    | ~ l1_struct_0(k1_tex_2('#skF_3','#skF_4'))
    | ~ v7_struct_0(k1_tex_2('#skF_3','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_150,c_10])).

tff(c_194,plain,
    ( v1_zfmisc_1('#skF_1'('#skF_3',k1_tex_2('#skF_3','#skF_4')))
    | ~ l1_struct_0(k1_tex_2('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_171])).

tff(c_197,plain,(
    ~ l1_struct_0(k1_tex_2('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_194])).

tff(c_205,plain,(
    ~ l1_pre_topc(k1_tex_2('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_4,c_197])).

tff(c_209,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_143,c_205])).

tff(c_210,plain,(
    v1_zfmisc_1('#skF_1'('#skF_3',k1_tex_2('#skF_3','#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_194])).

tff(c_510,plain,(
    v1_zfmisc_1('#skF_2'('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_487,c_210])).

tff(c_513,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_266,c_510])).

tff(c_514,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_117])).

tff(c_518,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_4,c_514])).

tff(c_522,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_518])).

tff(c_523,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_112])).

tff(c_8,plain,(
    ! [A_6] :
      ( ~ v1_xboole_0(u1_struct_0(A_6))
      | ~ l1_struct_0(A_6)
      | v2_struct_0(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_527,plain,
    ( ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_523,c_8])).

tff(c_530,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_527])).

tff(c_533,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_4,c_530])).

tff(c_537,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_533])).

tff(c_538,plain,(
    v1_tex_2(k1_tex_2('#skF_3','#skF_4'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_618,plain,(
    ! [B_121,A_122] :
      ( ~ v1_tex_2(B_121,A_122)
      | v2_struct_0(B_121)
      | ~ m1_pre_topc(B_121,A_122)
      | ~ l1_pre_topc(A_122)
      | ~ v7_struct_0(A_122)
      | v2_struct_0(A_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_624,plain,
    ( v2_struct_0(k1_tex_2('#skF_3','#skF_4'))
    | ~ m1_pre_topc(k1_tex_2('#skF_3','#skF_4'),'#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v7_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_538,c_618])).

tff(c_628,plain,
    ( v2_struct_0(k1_tex_2('#skF_3','#skF_4'))
    | ~ v7_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_609,c_624])).

tff(c_629,plain,(
    ~ v7_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_551,c_628])).

tff(c_598,plain,(
    ! [A_114] :
      ( m1_subset_1('#skF_2'(A_114),k1_zfmisc_1(u1_struct_0(A_114)))
      | ~ l1_struct_0(A_114)
      | v7_struct_0(A_114)
      | v2_struct_0(A_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_645,plain,(
    ! [A_127] :
      ( v1_subset_1('#skF_2'(A_127),u1_struct_0(A_127))
      | u1_struct_0(A_127) = '#skF_2'(A_127)
      | ~ l1_struct_0(A_127)
      | v7_struct_0(A_127)
      | v2_struct_0(A_127) ) ),
    inference(resolution,[status(thm)],[c_598,c_24])).

tff(c_650,plain,(
    ! [A_128] :
      ( u1_struct_0(A_128) = '#skF_2'(A_128)
      | ~ l1_struct_0(A_128)
      | v7_struct_0(A_128)
      | v2_struct_0(A_128) ) ),
    inference(resolution,[status(thm)],[c_645,c_40])).

tff(c_653,plain,
    ( u1_struct_0('#skF_3') = '#skF_2'('#skF_3')
    | ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_650,c_629])).

tff(c_656,plain,
    ( u1_struct_0('#skF_3') = '#skF_2'('#skF_3')
    | ~ l1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_653])).

tff(c_657,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_656])).

tff(c_660,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_4,c_657])).

tff(c_664,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_660])).

tff(c_666,plain,(
    l1_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_656])).

tff(c_665,plain,(
    u1_struct_0('#skF_3') = '#skF_2'('#skF_3') ),
    inference(splitRight,[status(thm)],[c_656])).

tff(c_562,plain,(
    ! [A_108,B_109] :
      ( v1_subset_1(k6_domain_1(A_108,B_109),A_108)
      | ~ m1_subset_1(B_109,A_108)
      | v1_zfmisc_1(A_108)
      | v1_xboole_0(A_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_539,plain,(
    ~ v1_subset_1(k6_domain_1(u1_struct_0('#skF_3'),'#skF_4'),u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_565,plain,
    ( ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | v1_zfmisc_1(u1_struct_0('#skF_3'))
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_562,c_539])).

tff(c_568,plain,
    ( v1_zfmisc_1(u1_struct_0('#skF_3'))
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_565])).

tff(c_569,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_568])).

tff(c_572,plain,
    ( ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_569,c_8])).

tff(c_575,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_572])).

tff(c_578,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_4,c_575])).

tff(c_582,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_578])).

tff(c_583,plain,(
    v1_zfmisc_1(u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_568])).

tff(c_669,plain,(
    v1_zfmisc_1('#skF_2'('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_665,c_583])).

tff(c_42,plain,(
    ! [A_27] :
      ( ~ v1_zfmisc_1('#skF_2'(A_27))
      | ~ l1_struct_0(A_27)
      | v7_struct_0(A_27)
      | v2_struct_0(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_755,plain,
    ( ~ l1_struct_0('#skF_3')
    | v7_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_669,c_42])).

tff(c_758,plain,
    ( v7_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_666,c_755])).

tff(c_760,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_629,c_758])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:00:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.06/1.45  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.14/1.47  
% 3.14/1.47  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.14/1.47  %$ v1_tex_2 > v1_subset_1 > m1_subset_1 > m1_pre_topc > v7_struct_0 > v2_struct_0 > v1_zfmisc_1 > v1_xboole_0 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k6_domain_1 > k1_tex_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 3.14/1.47  
% 3.14/1.47  %Foreground sorts:
% 3.14/1.47  
% 3.14/1.47  
% 3.14/1.47  %Background operators:
% 3.14/1.47  
% 3.14/1.47  
% 3.14/1.47  %Foreground operators:
% 3.14/1.47  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.14/1.47  tff('#skF_2', type, '#skF_2': $i > $i).
% 3.14/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.14/1.47  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 3.14/1.47  tff(v1_tex_2, type, v1_tex_2: ($i * $i) > $o).
% 3.14/1.47  tff(v7_struct_0, type, v7_struct_0: $i > $o).
% 3.14/1.47  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.14/1.47  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 3.14/1.47  tff('#skF_3', type, '#skF_3': $i).
% 3.14/1.47  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 3.14/1.47  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.14/1.47  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.14/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.14/1.47  tff(k1_tex_2, type, k1_tex_2: ($i * $i) > $i).
% 3.14/1.47  tff('#skF_4', type, '#skF_4': $i).
% 3.14/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.14/1.47  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 3.14/1.47  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.14/1.47  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.14/1.47  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.14/1.47  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.14/1.47  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.14/1.47  
% 3.14/1.49  tff(f_192, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (v1_tex_2(k1_tex_2(A, B), A) <=> v1_subset_1(k6_domain_1(u1_struct_0(A), B), u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_tex_2)).
% 3.14/1.49  tff(f_124, axiom, (![A, B]: (((~v2_struct_0(A) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => ((~v2_struct_0(k1_tex_2(A, B)) & v7_struct_0(k1_tex_2(A, B))) & v1_pre_topc(k1_tex_2(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_tex_2)).
% 3.14/1.49  tff(f_110, axiom, (![A, B]: (((~v2_struct_0(A) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => ((~v2_struct_0(k1_tex_2(A, B)) & v1_pre_topc(k1_tex_2(A, B))) & m1_pre_topc(k1_tex_2(A, B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_tex_2)).
% 3.14/1.49  tff(f_35, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.14/1.49  tff(f_144, axiom, (![A]: (((~v2_struct_0(A) & ~v7_struct_0(A)) & l1_struct_0(A)) => (?[B]: (((m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) & ~v1_xboole_0(B)) & ~v1_zfmisc_1(B)) & ~v1_subset_1(B, u1_struct_0(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc5_tex_2)).
% 3.14/1.49  tff(f_96, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (v1_subset_1(B, A) <=> ~(B = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_subset_1)).
% 3.14/1.49  tff(f_56, axiom, (![A]: ((v7_struct_0(A) & l1_struct_0(A)) => v1_zfmisc_1(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc7_struct_0)).
% 3.14/1.49  tff(f_155, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, A) => ~(v1_subset_1(k6_domain_1(A, B), A) & v1_zfmisc_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_tex_2)).
% 3.14/1.49  tff(f_89, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (v1_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => v1_subset_1(C, u1_struct_0(A)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tex_2)).
% 3.14/1.49  tff(f_42, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 3.14/1.49  tff(f_50, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 3.14/1.49  tff(f_75, axiom, (![A]: (((~v2_struct_0(A) & v7_struct_0(A)) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (~v2_struct_0(B) => (~v2_struct_0(B) & ~v1_tex_2(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc10_tex_2)).
% 3.14/1.49  tff(f_166, axiom, (![A]: ((~v1_xboole_0(A) & ~v1_zfmisc_1(A)) => (![B]: (m1_subset_1(B, A) => v1_subset_1(k6_domain_1(A, B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_tex_2)).
% 3.14/1.49  tff(c_58, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_192])).
% 3.14/1.49  tff(c_56, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_192])).
% 3.14/1.49  tff(c_54, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_192])).
% 3.14/1.49  tff(c_544, plain, (![A_104, B_105]: (~v2_struct_0(k1_tex_2(A_104, B_105)) | ~m1_subset_1(B_105, u1_struct_0(A_104)) | ~l1_pre_topc(A_104) | v2_struct_0(A_104))), inference(cnfTransformation, [status(thm)], [f_124])).
% 3.14/1.49  tff(c_547, plain, (~v2_struct_0(k1_tex_2('#skF_3', '#skF_4')) | ~l1_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_54, c_544])).
% 3.14/1.49  tff(c_550, plain, (~v2_struct_0(k1_tex_2('#skF_3', '#skF_4')) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_547])).
% 3.14/1.49  tff(c_551, plain, (~v2_struct_0(k1_tex_2('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_58, c_550])).
% 3.14/1.49  tff(c_603, plain, (![A_115, B_116]: (m1_pre_topc(k1_tex_2(A_115, B_116), A_115) | ~m1_subset_1(B_116, u1_struct_0(A_115)) | ~l1_pre_topc(A_115) | v2_struct_0(A_115))), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.14/1.49  tff(c_605, plain, (m1_pre_topc(k1_tex_2('#skF_3', '#skF_4'), '#skF_3') | ~l1_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_54, c_603])).
% 3.14/1.49  tff(c_608, plain, (m1_pre_topc(k1_tex_2('#skF_3', '#skF_4'), '#skF_3') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_605])).
% 3.14/1.49  tff(c_609, plain, (m1_pre_topc(k1_tex_2('#skF_3', '#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_58, c_608])).
% 3.14/1.49  tff(c_4, plain, (![A_2]: (l1_struct_0(A_2) | ~l1_pre_topc(A_2))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.14/1.49  tff(c_97, plain, (![A_57]: (m1_subset_1('#skF_2'(A_57), k1_zfmisc_1(u1_struct_0(A_57))) | ~l1_struct_0(A_57) | v7_struct_0(A_57) | v2_struct_0(A_57))), inference(cnfTransformation, [status(thm)], [f_144])).
% 3.14/1.49  tff(c_24, plain, (![B_22, A_21]: (v1_subset_1(B_22, A_21) | B_22=A_21 | ~m1_subset_1(B_22, k1_zfmisc_1(A_21)))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.14/1.49  tff(c_238, plain, (![A_77]: (v1_subset_1('#skF_2'(A_77), u1_struct_0(A_77)) | u1_struct_0(A_77)='#skF_2'(A_77) | ~l1_struct_0(A_77) | v7_struct_0(A_77) | v2_struct_0(A_77))), inference(resolution, [status(thm)], [c_97, c_24])).
% 3.14/1.49  tff(c_40, plain, (![A_27]: (~v1_subset_1('#skF_2'(A_27), u1_struct_0(A_27)) | ~l1_struct_0(A_27) | v7_struct_0(A_27) | v2_struct_0(A_27))), inference(cnfTransformation, [status(thm)], [f_144])).
% 3.14/1.49  tff(c_249, plain, (![A_78]: (u1_struct_0(A_78)='#skF_2'(A_78) | ~l1_struct_0(A_78) | v7_struct_0(A_78) | v2_struct_0(A_78))), inference(resolution, [status(thm)], [c_238, c_40])).
% 3.14/1.49  tff(c_10, plain, (![A_7]: (v1_zfmisc_1(u1_struct_0(A_7)) | ~l1_struct_0(A_7) | ~v7_struct_0(A_7))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.14/1.49  tff(c_66, plain, (v1_tex_2(k1_tex_2('#skF_3', '#skF_4'), '#skF_3') | v1_subset_1(k6_domain_1(u1_struct_0('#skF_3'), '#skF_4'), u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_192])).
% 3.14/1.49  tff(c_73, plain, (v1_subset_1(k6_domain_1(u1_struct_0('#skF_3'), '#skF_4'), u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_66])).
% 3.14/1.49  tff(c_102, plain, (![A_58, B_59]: (~v1_zfmisc_1(A_58) | ~v1_subset_1(k6_domain_1(A_58, B_59), A_58) | ~m1_subset_1(B_59, A_58) | v1_xboole_0(A_58))), inference(cnfTransformation, [status(thm)], [f_155])).
% 3.14/1.49  tff(c_108, plain, (~v1_zfmisc_1(u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_73, c_102])).
% 3.14/1.49  tff(c_112, plain, (~v1_zfmisc_1(u1_struct_0('#skF_3')) | v1_xboole_0(u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_108])).
% 3.14/1.49  tff(c_113, plain, (~v1_zfmisc_1(u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_112])).
% 3.14/1.49  tff(c_117, plain, (~l1_struct_0('#skF_3') | ~v7_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_10, c_113])).
% 3.14/1.49  tff(c_126, plain, (~v7_struct_0('#skF_3')), inference(splitLeft, [status(thm)], [c_117])).
% 3.14/1.49  tff(c_252, plain, (u1_struct_0('#skF_3')='#skF_2'('#skF_3') | ~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_249, c_126])).
% 3.14/1.49  tff(c_255, plain, (u1_struct_0('#skF_3')='#skF_2'('#skF_3') | ~l1_struct_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_58, c_252])).
% 3.14/1.49  tff(c_256, plain, (~l1_struct_0('#skF_3')), inference(splitLeft, [status(thm)], [c_255])).
% 3.14/1.49  tff(c_259, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_4, c_256])).
% 3.14/1.49  tff(c_263, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_259])).
% 3.14/1.49  tff(c_264, plain, (u1_struct_0('#skF_3')='#skF_2'('#skF_3')), inference(splitRight, [status(thm)], [c_255])).
% 3.14/1.49  tff(c_266, plain, (~v1_zfmisc_1('#skF_2'('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_264, c_113])).
% 3.14/1.49  tff(c_131, plain, (![A_62, B_63]: (m1_pre_topc(k1_tex_2(A_62, B_63), A_62) | ~m1_subset_1(B_63, u1_struct_0(A_62)) | ~l1_pre_topc(A_62) | v2_struct_0(A_62))), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.14/1.49  tff(c_133, plain, (m1_pre_topc(k1_tex_2('#skF_3', '#skF_4'), '#skF_3') | ~l1_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_54, c_131])).
% 3.14/1.49  tff(c_136, plain, (m1_pre_topc(k1_tex_2('#skF_3', '#skF_4'), '#skF_3') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_133])).
% 3.14/1.49  tff(c_137, plain, (m1_pre_topc(k1_tex_2('#skF_3', '#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_58, c_136])).
% 3.14/1.49  tff(c_22, plain, (![A_11, B_17]: (m1_subset_1('#skF_1'(A_11, B_17), k1_zfmisc_1(u1_struct_0(A_11))) | v1_tex_2(B_17, A_11) | ~m1_pre_topc(B_17, A_11) | ~l1_pre_topc(A_11))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.14/1.49  tff(c_272, plain, (![B_17]: (m1_subset_1('#skF_1'('#skF_3', B_17), k1_zfmisc_1('#skF_2'('#skF_3'))) | v1_tex_2(B_17, '#skF_3') | ~m1_pre_topc(B_17, '#skF_3') | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_264, c_22])).
% 3.14/1.49  tff(c_401, plain, (![B_86]: (m1_subset_1('#skF_1'('#skF_3', B_86), k1_zfmisc_1('#skF_2'('#skF_3'))) | v1_tex_2(B_86, '#skF_3') | ~m1_pre_topc(B_86, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_272])).
% 3.14/1.49  tff(c_469, plain, (![B_95]: (v1_subset_1('#skF_1'('#skF_3', B_95), '#skF_2'('#skF_3')) | '#skF_2'('#skF_3')='#skF_1'('#skF_3', B_95) | v1_tex_2(B_95, '#skF_3') | ~m1_pre_topc(B_95, '#skF_3'))), inference(resolution, [status(thm)], [c_401, c_24])).
% 3.14/1.49  tff(c_18, plain, (![A_11, B_17]: (~v1_subset_1('#skF_1'(A_11, B_17), u1_struct_0(A_11)) | v1_tex_2(B_17, A_11) | ~m1_pre_topc(B_17, A_11) | ~l1_pre_topc(A_11))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.14/1.49  tff(c_275, plain, (![B_17]: (~v1_subset_1('#skF_1'('#skF_3', B_17), '#skF_2'('#skF_3')) | v1_tex_2(B_17, '#skF_3') | ~m1_pre_topc(B_17, '#skF_3') | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_264, c_18])).
% 3.14/1.49  tff(c_304, plain, (![B_17]: (~v1_subset_1('#skF_1'('#skF_3', B_17), '#skF_2'('#skF_3')) | v1_tex_2(B_17, '#skF_3') | ~m1_pre_topc(B_17, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_275])).
% 3.14/1.49  tff(c_474, plain, (![B_96]: ('#skF_2'('#skF_3')='#skF_1'('#skF_3', B_96) | v1_tex_2(B_96, '#skF_3') | ~m1_pre_topc(B_96, '#skF_3'))), inference(resolution, [status(thm)], [c_469, c_304])).
% 3.14/1.49  tff(c_60, plain, (~v1_subset_1(k6_domain_1(u1_struct_0('#skF_3'), '#skF_4'), u1_struct_0('#skF_3')) | ~v1_tex_2(k1_tex_2('#skF_3', '#skF_4'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_192])).
% 3.14/1.49  tff(c_79, plain, (~v1_tex_2(k1_tex_2('#skF_3', '#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_73, c_60])).
% 3.14/1.49  tff(c_480, plain, ('#skF_1'('#skF_3', k1_tex_2('#skF_3', '#skF_4'))='#skF_2'('#skF_3') | ~m1_pre_topc(k1_tex_2('#skF_3', '#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_474, c_79])).
% 3.14/1.49  tff(c_487, plain, ('#skF_1'('#skF_3', k1_tex_2('#skF_3', '#skF_4'))='#skF_2'('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_137, c_480])).
% 3.14/1.49  tff(c_6, plain, (![B_5, A_3]: (l1_pre_topc(B_5) | ~m1_pre_topc(B_5, A_3) | ~l1_pre_topc(A_3))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.14/1.49  tff(c_140, plain, (l1_pre_topc(k1_tex_2('#skF_3', '#skF_4')) | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_137, c_6])).
% 3.14/1.49  tff(c_143, plain, (l1_pre_topc(k1_tex_2('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_140])).
% 3.14/1.49  tff(c_118, plain, (![A_60, B_61]: (v7_struct_0(k1_tex_2(A_60, B_61)) | ~m1_subset_1(B_61, u1_struct_0(A_60)) | ~l1_pre_topc(A_60) | v2_struct_0(A_60))), inference(cnfTransformation, [status(thm)], [f_124])).
% 3.14/1.49  tff(c_121, plain, (v7_struct_0(k1_tex_2('#skF_3', '#skF_4')) | ~l1_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_54, c_118])).
% 3.14/1.49  tff(c_124, plain, (v7_struct_0(k1_tex_2('#skF_3', '#skF_4')) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_121])).
% 3.14/1.49  tff(c_125, plain, (v7_struct_0(k1_tex_2('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_58, c_124])).
% 3.14/1.49  tff(c_144, plain, (![B_64, A_65]: (u1_struct_0(B_64)='#skF_1'(A_65, B_64) | v1_tex_2(B_64, A_65) | ~m1_pre_topc(B_64, A_65) | ~l1_pre_topc(A_65))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.14/1.49  tff(c_147, plain, (u1_struct_0(k1_tex_2('#skF_3', '#skF_4'))='#skF_1'('#skF_3', k1_tex_2('#skF_3', '#skF_4')) | ~m1_pre_topc(k1_tex_2('#skF_3', '#skF_4'), '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_144, c_79])).
% 3.14/1.49  tff(c_150, plain, (u1_struct_0(k1_tex_2('#skF_3', '#skF_4'))='#skF_1'('#skF_3', k1_tex_2('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_137, c_147])).
% 3.14/1.49  tff(c_171, plain, (v1_zfmisc_1('#skF_1'('#skF_3', k1_tex_2('#skF_3', '#skF_4'))) | ~l1_struct_0(k1_tex_2('#skF_3', '#skF_4')) | ~v7_struct_0(k1_tex_2('#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_150, c_10])).
% 3.14/1.49  tff(c_194, plain, (v1_zfmisc_1('#skF_1'('#skF_3', k1_tex_2('#skF_3', '#skF_4'))) | ~l1_struct_0(k1_tex_2('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_125, c_171])).
% 3.14/1.49  tff(c_197, plain, (~l1_struct_0(k1_tex_2('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_194])).
% 3.14/1.49  tff(c_205, plain, (~l1_pre_topc(k1_tex_2('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_4, c_197])).
% 3.14/1.49  tff(c_209, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_143, c_205])).
% 3.14/1.49  tff(c_210, plain, (v1_zfmisc_1('#skF_1'('#skF_3', k1_tex_2('#skF_3', '#skF_4')))), inference(splitRight, [status(thm)], [c_194])).
% 3.14/1.49  tff(c_510, plain, (v1_zfmisc_1('#skF_2'('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_487, c_210])).
% 3.14/1.49  tff(c_513, plain, $false, inference(negUnitSimplification, [status(thm)], [c_266, c_510])).
% 3.14/1.49  tff(c_514, plain, (~l1_struct_0('#skF_3')), inference(splitRight, [status(thm)], [c_117])).
% 3.14/1.49  tff(c_518, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_4, c_514])).
% 3.14/1.49  tff(c_522, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_518])).
% 3.14/1.49  tff(c_523, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_112])).
% 3.14/1.49  tff(c_8, plain, (![A_6]: (~v1_xboole_0(u1_struct_0(A_6)) | ~l1_struct_0(A_6) | v2_struct_0(A_6))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.14/1.49  tff(c_527, plain, (~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_523, c_8])).
% 3.14/1.49  tff(c_530, plain, (~l1_struct_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_58, c_527])).
% 3.14/1.49  tff(c_533, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_4, c_530])).
% 3.14/1.49  tff(c_537, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_533])).
% 3.14/1.49  tff(c_538, plain, (v1_tex_2(k1_tex_2('#skF_3', '#skF_4'), '#skF_3')), inference(splitRight, [status(thm)], [c_66])).
% 3.14/1.49  tff(c_618, plain, (![B_121, A_122]: (~v1_tex_2(B_121, A_122) | v2_struct_0(B_121) | ~m1_pre_topc(B_121, A_122) | ~l1_pre_topc(A_122) | ~v7_struct_0(A_122) | v2_struct_0(A_122))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.14/1.49  tff(c_624, plain, (v2_struct_0(k1_tex_2('#skF_3', '#skF_4')) | ~m1_pre_topc(k1_tex_2('#skF_3', '#skF_4'), '#skF_3') | ~l1_pre_topc('#skF_3') | ~v7_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_538, c_618])).
% 3.14/1.49  tff(c_628, plain, (v2_struct_0(k1_tex_2('#skF_3', '#skF_4')) | ~v7_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_609, c_624])).
% 3.14/1.49  tff(c_629, plain, (~v7_struct_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_58, c_551, c_628])).
% 3.14/1.49  tff(c_598, plain, (![A_114]: (m1_subset_1('#skF_2'(A_114), k1_zfmisc_1(u1_struct_0(A_114))) | ~l1_struct_0(A_114) | v7_struct_0(A_114) | v2_struct_0(A_114))), inference(cnfTransformation, [status(thm)], [f_144])).
% 3.14/1.49  tff(c_645, plain, (![A_127]: (v1_subset_1('#skF_2'(A_127), u1_struct_0(A_127)) | u1_struct_0(A_127)='#skF_2'(A_127) | ~l1_struct_0(A_127) | v7_struct_0(A_127) | v2_struct_0(A_127))), inference(resolution, [status(thm)], [c_598, c_24])).
% 3.14/1.49  tff(c_650, plain, (![A_128]: (u1_struct_0(A_128)='#skF_2'(A_128) | ~l1_struct_0(A_128) | v7_struct_0(A_128) | v2_struct_0(A_128))), inference(resolution, [status(thm)], [c_645, c_40])).
% 3.14/1.49  tff(c_653, plain, (u1_struct_0('#skF_3')='#skF_2'('#skF_3') | ~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_650, c_629])).
% 3.14/1.49  tff(c_656, plain, (u1_struct_0('#skF_3')='#skF_2'('#skF_3') | ~l1_struct_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_58, c_653])).
% 3.14/1.49  tff(c_657, plain, (~l1_struct_0('#skF_3')), inference(splitLeft, [status(thm)], [c_656])).
% 3.14/1.49  tff(c_660, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_4, c_657])).
% 3.14/1.49  tff(c_664, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_660])).
% 3.14/1.49  tff(c_666, plain, (l1_struct_0('#skF_3')), inference(splitRight, [status(thm)], [c_656])).
% 3.14/1.49  tff(c_665, plain, (u1_struct_0('#skF_3')='#skF_2'('#skF_3')), inference(splitRight, [status(thm)], [c_656])).
% 3.14/1.49  tff(c_562, plain, (![A_108, B_109]: (v1_subset_1(k6_domain_1(A_108, B_109), A_108) | ~m1_subset_1(B_109, A_108) | v1_zfmisc_1(A_108) | v1_xboole_0(A_108))), inference(cnfTransformation, [status(thm)], [f_166])).
% 3.14/1.49  tff(c_539, plain, (~v1_subset_1(k6_domain_1(u1_struct_0('#skF_3'), '#skF_4'), u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_66])).
% 3.14/1.49  tff(c_565, plain, (~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | v1_zfmisc_1(u1_struct_0('#skF_3')) | v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_562, c_539])).
% 3.14/1.49  tff(c_568, plain, (v1_zfmisc_1(u1_struct_0('#skF_3')) | v1_xboole_0(u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_565])).
% 3.14/1.49  tff(c_569, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_568])).
% 3.14/1.49  tff(c_572, plain, (~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_569, c_8])).
% 3.14/1.49  tff(c_575, plain, (~l1_struct_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_58, c_572])).
% 3.14/1.49  tff(c_578, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_4, c_575])).
% 3.14/1.49  tff(c_582, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_578])).
% 3.14/1.49  tff(c_583, plain, (v1_zfmisc_1(u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_568])).
% 3.14/1.49  tff(c_669, plain, (v1_zfmisc_1('#skF_2'('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_665, c_583])).
% 3.14/1.49  tff(c_42, plain, (![A_27]: (~v1_zfmisc_1('#skF_2'(A_27)) | ~l1_struct_0(A_27) | v7_struct_0(A_27) | v2_struct_0(A_27))), inference(cnfTransformation, [status(thm)], [f_144])).
% 3.14/1.49  tff(c_755, plain, (~l1_struct_0('#skF_3') | v7_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_669, c_42])).
% 3.14/1.49  tff(c_758, plain, (v7_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_666, c_755])).
% 3.14/1.49  tff(c_760, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_629, c_758])).
% 3.14/1.49  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.14/1.49  
% 3.14/1.49  Inference rules
% 3.14/1.49  ----------------------
% 3.14/1.49  #Ref     : 0
% 3.14/1.49  #Sup     : 110
% 3.14/1.49  #Fact    : 0
% 3.14/1.49  #Define  : 0
% 3.14/1.49  #Split   : 8
% 3.14/1.49  #Chain   : 0
% 3.14/1.49  #Close   : 0
% 3.14/1.49  
% 3.14/1.49  Ordering : KBO
% 3.14/1.49  
% 3.14/1.49  Simplification rules
% 3.14/1.49  ----------------------
% 3.14/1.49  #Subsume      : 24
% 3.14/1.49  #Demod        : 127
% 3.14/1.49  #Tautology    : 19
% 3.14/1.49  #SimpNegUnit  : 50
% 3.14/1.49  #BackRed      : 16
% 3.14/1.49  
% 3.14/1.49  #Partial instantiations: 0
% 3.14/1.49  #Strategies tried      : 1
% 3.14/1.49  
% 3.14/1.49  Timing (in seconds)
% 3.14/1.49  ----------------------
% 3.14/1.49  Preprocessing        : 0.34
% 3.14/1.49  Parsing              : 0.18
% 3.14/1.49  CNF conversion       : 0.02
% 3.14/1.49  Main loop            : 0.38
% 3.14/1.50  Inferencing          : 0.13
% 3.14/1.50  Reduction            : 0.11
% 3.14/1.50  Demodulation         : 0.07
% 3.14/1.50  BG Simplification    : 0.02
% 3.14/1.50  Subsumption          : 0.06
% 3.14/1.50  Abstraction          : 0.02
% 3.14/1.50  MUC search           : 0.00
% 3.14/1.50  Cooper               : 0.00
% 3.14/1.50  Total                : 0.76
% 3.14/1.50  Index Insertion      : 0.00
% 3.14/1.50  Index Deletion       : 0.00
% 3.14/1.50  Index Matching       : 0.00
% 3.14/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
