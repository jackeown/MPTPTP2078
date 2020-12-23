%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:53 EST 2020

% Result     : Theorem 4.57s
% Output     : CNFRefutation 4.75s
% Verified   : 
% Statistics : Number of formulae       :  135 (19711 expanded)
%              Number of leaves         :   28 (6890 expanded)
%              Depth                    :   30
%              Number of atoms          :  312 (62561 expanded)
%              Number of equality atoms :   37 (9095 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_tex_2 > v1_subset_1 > r1_tarski > m1_subset_1 > m1_pre_topc > l1_pre_topc > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k2_subset_1 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(g1_pre_topc,type,(
    g1_pre_topc: ( $i * $i ) > $i )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff(v1_tex_2,type,(
    v1_tex_2: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_99,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_pre_topc(B,A)
           => ! [C] :
                ( m1_pre_topc(C,A)
               => ( ( g1_pre_topc(u1_struct_0(B),u1_pre_topc(B)) = g1_pre_topc(u1_struct_0(C),u1_pre_topc(C))
                    & v1_tex_2(B,A) )
                 => v1_tex_2(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_tex_2)).

tff(f_77,axiom,(
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

tff(f_84,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( v1_subset_1(B,A)
      <=> B != A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).

tff(f_33,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_36,axiom,(
    ! [A] : ~ v1_subset_1(k2_subset_1(A),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc14_subset_1)).

tff(f_43,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_56,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

tff(f_52,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( l1_pre_topc(B)
         => ( m1_pre_topc(A,B)
          <=> m1_pre_topc(A,g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_pre_topc)).

tff(f_63,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => r1_tarski(u1_struct_0(B),u1_struct_0(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_borsuk_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_34,plain,(
    ~ v1_tex_2('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_40,plain,(
    m1_pre_topc('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_44,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_280,plain,(
    ! [A_64,B_65] :
      ( m1_subset_1('#skF_1'(A_64,B_65),k1_zfmisc_1(u1_struct_0(A_64)))
      | v1_tex_2(B_65,A_64)
      | ~ m1_pre_topc(B_65,A_64)
      | ~ l1_pre_topc(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_30,plain,(
    ! [B_26,A_25] :
      ( v1_subset_1(B_26,A_25)
      | B_26 = A_25
      | ~ m1_subset_1(B_26,k1_zfmisc_1(A_25)) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_680,plain,(
    ! [A_81,B_82] :
      ( v1_subset_1('#skF_1'(A_81,B_82),u1_struct_0(A_81))
      | u1_struct_0(A_81) = '#skF_1'(A_81,B_82)
      | v1_tex_2(B_82,A_81)
      | ~ m1_pre_topc(B_82,A_81)
      | ~ l1_pre_topc(A_81) ) ),
    inference(resolution,[status(thm)],[c_280,c_30])).

tff(c_24,plain,(
    ! [A_15,B_21] :
      ( ~ v1_subset_1('#skF_1'(A_15,B_21),u1_struct_0(A_15))
      | v1_tex_2(B_21,A_15)
      | ~ m1_pre_topc(B_21,A_15)
      | ~ l1_pre_topc(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_695,plain,(
    ! [A_83,B_84] :
      ( u1_struct_0(A_83) = '#skF_1'(A_83,B_84)
      | v1_tex_2(B_84,A_83)
      | ~ m1_pre_topc(B_84,A_83)
      | ~ l1_pre_topc(A_83) ) ),
    inference(resolution,[status(thm)],[c_680,c_24])).

tff(c_698,plain,
    ( u1_struct_0('#skF_2') = '#skF_1'('#skF_2','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_695,c_34])).

tff(c_701,plain,(
    u1_struct_0('#skF_2') = '#skF_1'('#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_40,c_698])).

tff(c_28,plain,(
    ! [A_15,B_21] :
      ( m1_subset_1('#skF_1'(A_15,B_21),k1_zfmisc_1(u1_struct_0(A_15)))
      | v1_tex_2(B_21,A_15)
      | ~ m1_pre_topc(B_21,A_15)
      | ~ l1_pre_topc(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_726,plain,(
    ! [B_21] :
      ( m1_subset_1('#skF_1'('#skF_2',B_21),k1_zfmisc_1('#skF_1'('#skF_2','#skF_4')))
      | v1_tex_2(B_21,'#skF_2')
      | ~ m1_pre_topc(B_21,'#skF_2')
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_701,c_28])).

tff(c_772,plain,(
    ! [B_21] :
      ( m1_subset_1('#skF_1'('#skF_2',B_21),k1_zfmisc_1('#skF_1'('#skF_2','#skF_4')))
      | v1_tex_2(B_21,'#skF_2')
      | ~ m1_pre_topc(B_21,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_726])).

tff(c_8,plain,(
    ! [A_3] : k2_subset_1(A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_10,plain,(
    ! [A_4] : ~ v1_subset_1(k2_subset_1(A_4),A_4) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_45,plain,(
    ! [A_4] : ~ v1_subset_1(A_4,A_4) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_10])).

tff(c_42,plain,(
    m1_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_36,plain,(
    v1_tex_2('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_63,plain,(
    ! [B_35,A_36] :
      ( l1_pre_topc(B_35)
      | ~ m1_pre_topc(B_35,A_36)
      | ~ l1_pre_topc(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_69,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_63])).

tff(c_76,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_69])).

tff(c_18,plain,(
    ! [A_11] :
      ( m1_pre_topc(A_11,A_11)
      | ~ l1_pre_topc(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_92,plain,(
    ! [B_43,A_44] :
      ( u1_struct_0(B_43) = '#skF_1'(A_44,B_43)
      | v1_tex_2(B_43,A_44)
      | ~ m1_pre_topc(B_43,A_44)
      | ~ l1_pre_topc(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_95,plain,
    ( u1_struct_0('#skF_4') = '#skF_1'('#skF_2','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_92,c_34])).

tff(c_98,plain,(
    u1_struct_0('#skF_4') = '#skF_1'('#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_40,c_95])).

tff(c_133,plain,(
    ! [A_47,B_48] :
      ( m1_pre_topc(A_47,g1_pre_topc(u1_struct_0(B_48),u1_pre_topc(B_48)))
      | ~ m1_pre_topc(A_47,B_48)
      | ~ l1_pre_topc(B_48)
      | ~ l1_pre_topc(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_142,plain,(
    ! [A_47] :
      ( m1_pre_topc(A_47,g1_pre_topc('#skF_1'('#skF_2','#skF_4'),u1_pre_topc('#skF_4')))
      | ~ m1_pre_topc(A_47,'#skF_4')
      | ~ l1_pre_topc('#skF_4')
      | ~ l1_pre_topc(A_47) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_98,c_133])).

tff(c_147,plain,(
    ! [A_47] :
      ( m1_pre_topc(A_47,g1_pre_topc('#skF_1'('#skF_2','#skF_4'),u1_pre_topc('#skF_4')))
      | ~ m1_pre_topc(A_47,'#skF_4')
      | ~ l1_pre_topc(A_47) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_142])).

tff(c_72,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_63])).

tff(c_79,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_72])).

tff(c_38,plain,(
    g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_99,plain,(
    g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = g1_pre_topc('#skF_1'('#skF_2','#skF_4'),u1_pre_topc('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_38])).

tff(c_164,plain,(
    ! [A_53,B_54] :
      ( m1_pre_topc(A_53,B_54)
      | ~ m1_pre_topc(A_53,g1_pre_topc(u1_struct_0(B_54),u1_pre_topc(B_54)))
      | ~ l1_pre_topc(B_54)
      | ~ l1_pre_topc(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_170,plain,(
    ! [A_53] :
      ( m1_pre_topc(A_53,'#skF_3')
      | ~ m1_pre_topc(A_53,g1_pre_topc('#skF_1'('#skF_2','#skF_4'),u1_pre_topc('#skF_4')))
      | ~ l1_pre_topc('#skF_3')
      | ~ l1_pre_topc(A_53) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_99,c_164])).

tff(c_207,plain,(
    ! [A_58] :
      ( m1_pre_topc(A_58,'#skF_3')
      | ~ m1_pre_topc(A_58,g1_pre_topc('#skF_1'('#skF_2','#skF_4'),u1_pre_topc('#skF_4')))
      | ~ l1_pre_topc(A_58) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_170])).

tff(c_218,plain,(
    ! [A_47] :
      ( m1_pre_topc(A_47,'#skF_3')
      | ~ m1_pre_topc(A_47,'#skF_4')
      | ~ l1_pre_topc(A_47) ) ),
    inference(resolution,[status(thm)],[c_147,c_207])).

tff(c_139,plain,(
    ! [A_47] :
      ( m1_pre_topc(A_47,g1_pre_topc('#skF_1'('#skF_2','#skF_4'),u1_pre_topc('#skF_4')))
      | ~ m1_pre_topc(A_47,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ l1_pre_topc(A_47) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_99,c_133])).

tff(c_145,plain,(
    ! [A_47] :
      ( m1_pre_topc(A_47,g1_pre_topc('#skF_1'('#skF_2','#skF_4'),u1_pre_topc('#skF_4')))
      | ~ m1_pre_topc(A_47,'#skF_3')
      | ~ l1_pre_topc(A_47) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_139])).

tff(c_173,plain,(
    ! [A_53] :
      ( m1_pre_topc(A_53,'#skF_4')
      | ~ m1_pre_topc(A_53,g1_pre_topc('#skF_1'('#skF_2','#skF_4'),u1_pre_topc('#skF_4')))
      | ~ l1_pre_topc('#skF_4')
      | ~ l1_pre_topc(A_53) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_98,c_164])).

tff(c_185,plain,(
    ! [A_56] :
      ( m1_pre_topc(A_56,'#skF_4')
      | ~ m1_pre_topc(A_56,g1_pre_topc('#skF_1'('#skF_2','#skF_4'),u1_pre_topc('#skF_4')))
      | ~ l1_pre_topc(A_56) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_173])).

tff(c_199,plain,(
    ! [A_57] :
      ( m1_pre_topc(A_57,'#skF_4')
      | ~ m1_pre_topc(A_57,'#skF_3')
      | ~ l1_pre_topc(A_57) ) ),
    inference(resolution,[status(thm)],[c_145,c_185])).

tff(c_203,plain,
    ( m1_pre_topc('#skF_3','#skF_4')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_18,c_199])).

tff(c_206,plain,(
    m1_pre_topc('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_203])).

tff(c_20,plain,(
    ! [B_14,A_12] :
      ( r1_tarski(u1_struct_0(B_14),u1_struct_0(A_12))
      | ~ m1_pre_topc(B_14,A_12)
      | ~ l1_pre_topc(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_103,plain,(
    ! [A_12] :
      ( r1_tarski('#skF_1'('#skF_2','#skF_4'),u1_struct_0(A_12))
      | ~ m1_pre_topc('#skF_4',A_12)
      | ~ l1_pre_topc(A_12) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_98,c_20])).

tff(c_88,plain,(
    ! [B_41,A_42] :
      ( r1_tarski(u1_struct_0(B_41),u1_struct_0(A_42))
      | ~ m1_pre_topc(B_41,A_42)
      | ~ l1_pre_topc(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_238,plain,(
    ! [B_60,A_61] :
      ( u1_struct_0(B_60) = u1_struct_0(A_61)
      | ~ r1_tarski(u1_struct_0(A_61),u1_struct_0(B_60))
      | ~ m1_pre_topc(B_60,A_61)
      | ~ l1_pre_topc(A_61) ) ),
    inference(resolution,[status(thm)],[c_88,c_2])).

tff(c_241,plain,(
    ! [B_60] :
      ( u1_struct_0(B_60) = u1_struct_0('#skF_4')
      | ~ r1_tarski('#skF_1'('#skF_2','#skF_4'),u1_struct_0(B_60))
      | ~ m1_pre_topc(B_60,'#skF_4')
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_98,c_238])).

tff(c_258,plain,(
    ! [B_62] :
      ( u1_struct_0(B_62) = '#skF_1'('#skF_2','#skF_4')
      | ~ r1_tarski('#skF_1'('#skF_2','#skF_4'),u1_struct_0(B_62))
      | ~ m1_pre_topc(B_62,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_98,c_241])).

tff(c_268,plain,(
    ! [A_63] :
      ( u1_struct_0(A_63) = '#skF_1'('#skF_2','#skF_4')
      | ~ m1_pre_topc(A_63,'#skF_4')
      | ~ m1_pre_topc('#skF_4',A_63)
      | ~ l1_pre_topc(A_63) ) ),
    inference(resolution,[status(thm)],[c_103,c_258])).

tff(c_270,plain,
    ( u1_struct_0('#skF_3') = '#skF_1'('#skF_2','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_206,c_268])).

tff(c_276,plain,
    ( u1_struct_0('#skF_3') = '#skF_1'('#skF_2','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_270])).

tff(c_290,plain,(
    ~ m1_pre_topc('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_276])).

tff(c_293,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_218,c_290])).

tff(c_296,plain,(
    ~ m1_pre_topc('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_293])).

tff(c_299,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_18,c_296])).

tff(c_303,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_299])).

tff(c_305,plain,(
    m1_pre_topc('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_276])).

tff(c_197,plain,(
    ! [A_47] :
      ( m1_pre_topc(A_47,'#skF_4')
      | ~ m1_pre_topc(A_47,'#skF_3')
      | ~ l1_pre_topc(A_47) ) ),
    inference(resolution,[status(thm)],[c_145,c_185])).

tff(c_313,plain,
    ( m1_pre_topc('#skF_4','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_305,c_197])).

tff(c_319,plain,(
    m1_pre_topc('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_313])).

tff(c_689,plain,(
    ! [B_82] :
      ( v1_subset_1('#skF_1'('#skF_4',B_82),'#skF_1'('#skF_2','#skF_4'))
      | u1_struct_0('#skF_4') = '#skF_1'('#skF_4',B_82)
      | v1_tex_2(B_82,'#skF_4')
      | ~ m1_pre_topc(B_82,'#skF_4')
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_98,c_680])).

tff(c_944,plain,(
    ! [B_92] :
      ( v1_subset_1('#skF_1'('#skF_4',B_92),'#skF_1'('#skF_2','#skF_4'))
      | '#skF_1'('#skF_4',B_92) = '#skF_1'('#skF_2','#skF_4')
      | v1_tex_2(B_92,'#skF_4')
      | ~ m1_pre_topc(B_92,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_98,c_689])).

tff(c_158,plain,(
    ! [A_51,B_52] :
      ( ~ v1_subset_1('#skF_1'(A_51,B_52),u1_struct_0(A_51))
      | v1_tex_2(B_52,A_51)
      | ~ m1_pre_topc(B_52,A_51)
      | ~ l1_pre_topc(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_161,plain,(
    ! [B_52] :
      ( ~ v1_subset_1('#skF_1'('#skF_4',B_52),'#skF_1'('#skF_2','#skF_4'))
      | v1_tex_2(B_52,'#skF_4')
      | ~ m1_pre_topc(B_52,'#skF_4')
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_98,c_158])).

tff(c_163,plain,(
    ! [B_52] :
      ( ~ v1_subset_1('#skF_1'('#skF_4',B_52),'#skF_1'('#skF_2','#skF_4'))
      | v1_tex_2(B_52,'#skF_4')
      | ~ m1_pre_topc(B_52,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_161])).

tff(c_948,plain,(
    ! [B_92] :
      ( '#skF_1'('#skF_4',B_92) = '#skF_1'('#skF_2','#skF_4')
      | v1_tex_2(B_92,'#skF_4')
      | ~ m1_pre_topc(B_92,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_944,c_163])).

tff(c_304,plain,(
    u1_struct_0('#skF_3') = '#skF_1'('#skF_2','#skF_4') ),
    inference(splitRight,[status(thm)],[c_276])).

tff(c_422,plain,(
    ! [B_69,A_70] :
      ( v1_subset_1(u1_struct_0(B_69),u1_struct_0(A_70))
      | ~ m1_subset_1(u1_struct_0(B_69),k1_zfmisc_1(u1_struct_0(A_70)))
      | ~ v1_tex_2(B_69,A_70)
      | ~ m1_pre_topc(B_69,A_70)
      | ~ l1_pre_topc(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_434,plain,(
    ! [B_69] :
      ( v1_subset_1(u1_struct_0(B_69),u1_struct_0('#skF_4'))
      | ~ m1_subset_1(u1_struct_0(B_69),k1_zfmisc_1('#skF_1'('#skF_2','#skF_4')))
      | ~ v1_tex_2(B_69,'#skF_4')
      | ~ m1_pre_topc(B_69,'#skF_4')
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_98,c_422])).

tff(c_1050,plain,(
    ! [B_99] :
      ( v1_subset_1(u1_struct_0(B_99),'#skF_1'('#skF_2','#skF_4'))
      | ~ m1_subset_1(u1_struct_0(B_99),k1_zfmisc_1('#skF_1'('#skF_2','#skF_4')))
      | ~ v1_tex_2(B_99,'#skF_4')
      | ~ m1_pre_topc(B_99,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_98,c_434])).

tff(c_1056,plain,
    ( v1_subset_1(u1_struct_0('#skF_3'),'#skF_1'('#skF_2','#skF_4'))
    | ~ m1_subset_1('#skF_1'('#skF_2','#skF_4'),k1_zfmisc_1('#skF_1'('#skF_2','#skF_4')))
    | ~ v1_tex_2('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_304,c_1050])).

tff(c_1063,plain,
    ( v1_subset_1('#skF_1'('#skF_2','#skF_4'),'#skF_1'('#skF_2','#skF_4'))
    | ~ m1_subset_1('#skF_1'('#skF_2','#skF_4'),k1_zfmisc_1('#skF_1'('#skF_2','#skF_4')))
    | ~ v1_tex_2('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_206,c_304,c_1056])).

tff(c_1064,plain,
    ( ~ m1_subset_1('#skF_1'('#skF_2','#skF_4'),k1_zfmisc_1('#skF_1'('#skF_2','#skF_4')))
    | ~ v1_tex_2('#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_45,c_1063])).

tff(c_1068,plain,(
    ~ v1_tex_2('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1064])).

tff(c_1071,plain,
    ( '#skF_1'('#skF_2','#skF_4') = '#skF_1'('#skF_4','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_948,c_1068])).

tff(c_1080,plain,(
    '#skF_1'('#skF_2','#skF_4') = '#skF_1'('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_206,c_1071])).

tff(c_1124,plain,(
    u1_struct_0('#skF_4') = '#skF_1'('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1080,c_98])).

tff(c_690,plain,(
    ! [A_81,B_82] :
      ( u1_struct_0(A_81) = '#skF_1'(A_81,B_82)
      | v1_tex_2(B_82,A_81)
      | ~ m1_pre_topc(B_82,A_81)
      | ~ l1_pre_topc(A_81) ) ),
    inference(resolution,[status(thm)],[c_680,c_24])).

tff(c_431,plain,(
    ! [A_70] :
      ( v1_subset_1(u1_struct_0('#skF_4'),u1_struct_0(A_70))
      | ~ m1_subset_1('#skF_1'('#skF_2','#skF_4'),k1_zfmisc_1(u1_struct_0(A_70)))
      | ~ v1_tex_2('#skF_4',A_70)
      | ~ m1_pre_topc('#skF_4',A_70)
      | ~ l1_pre_topc(A_70) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_98,c_422])).

tff(c_438,plain,(
    ! [A_70] :
      ( v1_subset_1('#skF_1'('#skF_2','#skF_4'),u1_struct_0(A_70))
      | ~ m1_subset_1('#skF_1'('#skF_2','#skF_4'),k1_zfmisc_1(u1_struct_0(A_70)))
      | ~ v1_tex_2('#skF_4',A_70)
      | ~ m1_pre_topc('#skF_4',A_70)
      | ~ l1_pre_topc(A_70) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_431])).

tff(c_1310,plain,(
    ! [A_100] :
      ( v1_subset_1('#skF_1'('#skF_4','#skF_3'),u1_struct_0(A_100))
      | ~ m1_subset_1('#skF_1'('#skF_4','#skF_3'),k1_zfmisc_1(u1_struct_0(A_100)))
      | ~ v1_tex_2('#skF_4',A_100)
      | ~ m1_pre_topc('#skF_4',A_100)
      | ~ l1_pre_topc(A_100) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1080,c_1080,c_438])).

tff(c_1323,plain,
    ( v1_subset_1('#skF_1'('#skF_4','#skF_3'),u1_struct_0('#skF_4'))
    | ~ v1_tex_2('#skF_4','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_4')
    | v1_tex_2('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_1310])).

tff(c_1335,plain,
    ( v1_subset_1('#skF_1'('#skF_4','#skF_3'),'#skF_1'('#skF_4','#skF_3'))
    | ~ v1_tex_2('#skF_4','#skF_4')
    | v1_tex_2('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_206,c_319,c_1124,c_1323])).

tff(c_1336,plain,(
    ~ v1_tex_2('#skF_4','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_1068,c_45,c_1335])).

tff(c_1339,plain,
    ( u1_struct_0('#skF_4') = '#skF_1'('#skF_4','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_690,c_1336])).

tff(c_1345,plain,(
    '#skF_1'('#skF_4','#skF_3') = '#skF_1'('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_319,c_1124,c_1339])).

tff(c_1350,plain,(
    u1_struct_0('#skF_4') = '#skF_1'('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1345,c_1124])).

tff(c_1357,plain,
    ( m1_subset_1('#skF_1'('#skF_4','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | v1_tex_2('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1345,c_28])).

tff(c_1364,plain,
    ( m1_subset_1('#skF_1'('#skF_4','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | v1_tex_2('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_206,c_1357])).

tff(c_1365,plain,(
    m1_subset_1('#skF_1'('#skF_4','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_1068,c_1364])).

tff(c_1610,plain,(
    m1_subset_1('#skF_1'('#skF_4','#skF_4'),k1_zfmisc_1('#skF_1'('#skF_4','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1350,c_1365])).

tff(c_1113,plain,(
    u1_struct_0('#skF_3') = '#skF_1'('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1080,c_304])).

tff(c_1351,plain,(
    u1_struct_0('#skF_3') = '#skF_1'('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1345,c_1113])).

tff(c_1353,plain,(
    '#skF_1'('#skF_2','#skF_4') = '#skF_1'('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1345,c_1080])).

tff(c_22,plain,(
    ! [B_21,A_15] :
      ( v1_subset_1(u1_struct_0(B_21),u1_struct_0(A_15))
      | ~ m1_subset_1(u1_struct_0(B_21),k1_zfmisc_1(u1_struct_0(A_15)))
      | ~ v1_tex_2(B_21,A_15)
      | ~ m1_pre_topc(B_21,A_15)
      | ~ l1_pre_topc(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_717,plain,(
    ! [B_21] :
      ( v1_subset_1(u1_struct_0(B_21),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(u1_struct_0(B_21),k1_zfmisc_1('#skF_1'('#skF_2','#skF_4')))
      | ~ v1_tex_2(B_21,'#skF_2')
      | ~ m1_pre_topc(B_21,'#skF_2')
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_701,c_22])).

tff(c_767,plain,(
    ! [B_21] :
      ( v1_subset_1(u1_struct_0(B_21),'#skF_1'('#skF_2','#skF_4'))
      | ~ m1_subset_1(u1_struct_0(B_21),k1_zfmisc_1('#skF_1'('#skF_2','#skF_4')))
      | ~ v1_tex_2(B_21,'#skF_2')
      | ~ m1_pre_topc(B_21,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_701,c_717])).

tff(c_2593,plain,(
    ! [B_136] :
      ( v1_subset_1(u1_struct_0(B_136),'#skF_1'('#skF_4','#skF_4'))
      | ~ m1_subset_1(u1_struct_0(B_136),k1_zfmisc_1('#skF_1'('#skF_4','#skF_4')))
      | ~ v1_tex_2(B_136,'#skF_2')
      | ~ m1_pre_topc(B_136,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1353,c_1353,c_767])).

tff(c_2596,plain,
    ( v1_subset_1(u1_struct_0('#skF_3'),'#skF_1'('#skF_4','#skF_4'))
    | ~ m1_subset_1('#skF_1'('#skF_4','#skF_4'),k1_zfmisc_1('#skF_1'('#skF_4','#skF_4')))
    | ~ v1_tex_2('#skF_3','#skF_2')
    | ~ m1_pre_topc('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1351,c_2593])).

tff(c_2604,plain,(
    v1_subset_1('#skF_1'('#skF_4','#skF_4'),'#skF_1'('#skF_4','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_36,c_1610,c_1351,c_2596])).

tff(c_2606,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_45,c_2604])).

tff(c_2607,plain,(
    ~ m1_subset_1('#skF_1'('#skF_2','#skF_4'),k1_zfmisc_1('#skF_1'('#skF_2','#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_1064])).

tff(c_2611,plain,
    ( v1_tex_2('#skF_4','#skF_2')
    | ~ m1_pre_topc('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_772,c_2607])).

tff(c_2614,plain,(
    v1_tex_2('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_2611])).

tff(c_2616,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_2614])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:56:30 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.57/1.79  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.67/1.81  
% 4.67/1.81  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.67/1.81  %$ v1_tex_2 > v1_subset_1 > r1_tarski > m1_subset_1 > m1_pre_topc > l1_pre_topc > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k2_subset_1 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 4.67/1.81  
% 4.67/1.81  %Foreground sorts:
% 4.67/1.81  
% 4.67/1.81  
% 4.67/1.81  %Background operators:
% 4.67/1.81  
% 4.67/1.81  
% 4.67/1.81  %Foreground operators:
% 4.67/1.81  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 4.67/1.81  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.67/1.81  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 4.67/1.81  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 4.67/1.81  tff(v1_tex_2, type, v1_tex_2: ($i * $i) > $o).
% 4.67/1.81  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.67/1.81  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.67/1.81  tff('#skF_2', type, '#skF_2': $i).
% 4.67/1.81  tff('#skF_3', type, '#skF_3': $i).
% 4.67/1.81  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.67/1.81  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.67/1.81  tff('#skF_4', type, '#skF_4': $i).
% 4.67/1.81  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.67/1.81  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 4.67/1.81  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.67/1.81  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.67/1.81  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 4.67/1.81  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.67/1.81  
% 4.75/1.83  tff(f_99, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_pre_topc(C, A) => (((g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)) = g1_pre_topc(u1_struct_0(C), u1_pre_topc(C))) & v1_tex_2(B, A)) => v1_tex_2(C, A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_tex_2)).
% 4.75/1.83  tff(f_77, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (v1_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => v1_subset_1(C, u1_struct_0(A)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tex_2)).
% 4.75/1.83  tff(f_84, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (v1_subset_1(B, A) <=> ~(B = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_subset_1)).
% 4.75/1.83  tff(f_33, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 4.75/1.83  tff(f_36, axiom, (![A]: ~v1_subset_1(k2_subset_1(A), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc14_subset_1)).
% 4.75/1.83  tff(f_43, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 4.75/1.83  tff(f_56, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tsep_1)).
% 4.75/1.83  tff(f_52, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (m1_pre_topc(A, B) <=> m1_pre_topc(A, g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_pre_topc)).
% 4.75/1.83  tff(f_63, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => r1_tarski(u1_struct_0(B), u1_struct_0(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_borsuk_1)).
% 4.75/1.83  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.75/1.83  tff(c_34, plain, (~v1_tex_2('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_99])).
% 4.75/1.83  tff(c_40, plain, (m1_pre_topc('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_99])).
% 4.75/1.83  tff(c_44, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_99])).
% 4.75/1.83  tff(c_280, plain, (![A_64, B_65]: (m1_subset_1('#skF_1'(A_64, B_65), k1_zfmisc_1(u1_struct_0(A_64))) | v1_tex_2(B_65, A_64) | ~m1_pre_topc(B_65, A_64) | ~l1_pre_topc(A_64))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.75/1.83  tff(c_30, plain, (![B_26, A_25]: (v1_subset_1(B_26, A_25) | B_26=A_25 | ~m1_subset_1(B_26, k1_zfmisc_1(A_25)))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.75/1.83  tff(c_680, plain, (![A_81, B_82]: (v1_subset_1('#skF_1'(A_81, B_82), u1_struct_0(A_81)) | u1_struct_0(A_81)='#skF_1'(A_81, B_82) | v1_tex_2(B_82, A_81) | ~m1_pre_topc(B_82, A_81) | ~l1_pre_topc(A_81))), inference(resolution, [status(thm)], [c_280, c_30])).
% 4.75/1.83  tff(c_24, plain, (![A_15, B_21]: (~v1_subset_1('#skF_1'(A_15, B_21), u1_struct_0(A_15)) | v1_tex_2(B_21, A_15) | ~m1_pre_topc(B_21, A_15) | ~l1_pre_topc(A_15))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.75/1.83  tff(c_695, plain, (![A_83, B_84]: (u1_struct_0(A_83)='#skF_1'(A_83, B_84) | v1_tex_2(B_84, A_83) | ~m1_pre_topc(B_84, A_83) | ~l1_pre_topc(A_83))), inference(resolution, [status(thm)], [c_680, c_24])).
% 4.75/1.83  tff(c_698, plain, (u1_struct_0('#skF_2')='#skF_1'('#skF_2', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_695, c_34])).
% 4.75/1.83  tff(c_701, plain, (u1_struct_0('#skF_2')='#skF_1'('#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_40, c_698])).
% 4.75/1.83  tff(c_28, plain, (![A_15, B_21]: (m1_subset_1('#skF_1'(A_15, B_21), k1_zfmisc_1(u1_struct_0(A_15))) | v1_tex_2(B_21, A_15) | ~m1_pre_topc(B_21, A_15) | ~l1_pre_topc(A_15))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.75/1.83  tff(c_726, plain, (![B_21]: (m1_subset_1('#skF_1'('#skF_2', B_21), k1_zfmisc_1('#skF_1'('#skF_2', '#skF_4'))) | v1_tex_2(B_21, '#skF_2') | ~m1_pre_topc(B_21, '#skF_2') | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_701, c_28])).
% 4.75/1.83  tff(c_772, plain, (![B_21]: (m1_subset_1('#skF_1'('#skF_2', B_21), k1_zfmisc_1('#skF_1'('#skF_2', '#skF_4'))) | v1_tex_2(B_21, '#skF_2') | ~m1_pre_topc(B_21, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_726])).
% 4.75/1.83  tff(c_8, plain, (![A_3]: (k2_subset_1(A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.75/1.83  tff(c_10, plain, (![A_4]: (~v1_subset_1(k2_subset_1(A_4), A_4))), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.75/1.83  tff(c_45, plain, (![A_4]: (~v1_subset_1(A_4, A_4))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_10])).
% 4.75/1.83  tff(c_42, plain, (m1_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_99])).
% 4.75/1.83  tff(c_36, plain, (v1_tex_2('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_99])).
% 4.75/1.83  tff(c_63, plain, (![B_35, A_36]: (l1_pre_topc(B_35) | ~m1_pre_topc(B_35, A_36) | ~l1_pre_topc(A_36))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.75/1.83  tff(c_69, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_40, c_63])).
% 4.75/1.83  tff(c_76, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_69])).
% 4.75/1.83  tff(c_18, plain, (![A_11]: (m1_pre_topc(A_11, A_11) | ~l1_pre_topc(A_11))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.75/1.83  tff(c_92, plain, (![B_43, A_44]: (u1_struct_0(B_43)='#skF_1'(A_44, B_43) | v1_tex_2(B_43, A_44) | ~m1_pre_topc(B_43, A_44) | ~l1_pre_topc(A_44))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.75/1.83  tff(c_95, plain, (u1_struct_0('#skF_4')='#skF_1'('#skF_2', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_92, c_34])).
% 4.75/1.83  tff(c_98, plain, (u1_struct_0('#skF_4')='#skF_1'('#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_40, c_95])).
% 4.75/1.83  tff(c_133, plain, (![A_47, B_48]: (m1_pre_topc(A_47, g1_pre_topc(u1_struct_0(B_48), u1_pre_topc(B_48))) | ~m1_pre_topc(A_47, B_48) | ~l1_pre_topc(B_48) | ~l1_pre_topc(A_47))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.75/1.83  tff(c_142, plain, (![A_47]: (m1_pre_topc(A_47, g1_pre_topc('#skF_1'('#skF_2', '#skF_4'), u1_pre_topc('#skF_4'))) | ~m1_pre_topc(A_47, '#skF_4') | ~l1_pre_topc('#skF_4') | ~l1_pre_topc(A_47))), inference(superposition, [status(thm), theory('equality')], [c_98, c_133])).
% 4.75/1.83  tff(c_147, plain, (![A_47]: (m1_pre_topc(A_47, g1_pre_topc('#skF_1'('#skF_2', '#skF_4'), u1_pre_topc('#skF_4'))) | ~m1_pre_topc(A_47, '#skF_4') | ~l1_pre_topc(A_47))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_142])).
% 4.75/1.83  tff(c_72, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_42, c_63])).
% 4.75/1.83  tff(c_79, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_72])).
% 4.75/1.83  tff(c_38, plain, (g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))=g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_99])).
% 4.75/1.83  tff(c_99, plain, (g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))=g1_pre_topc('#skF_1'('#skF_2', '#skF_4'), u1_pre_topc('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_38])).
% 4.75/1.83  tff(c_164, plain, (![A_53, B_54]: (m1_pre_topc(A_53, B_54) | ~m1_pre_topc(A_53, g1_pre_topc(u1_struct_0(B_54), u1_pre_topc(B_54))) | ~l1_pre_topc(B_54) | ~l1_pre_topc(A_53))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.75/1.83  tff(c_170, plain, (![A_53]: (m1_pre_topc(A_53, '#skF_3') | ~m1_pre_topc(A_53, g1_pre_topc('#skF_1'('#skF_2', '#skF_4'), u1_pre_topc('#skF_4'))) | ~l1_pre_topc('#skF_3') | ~l1_pre_topc(A_53))), inference(superposition, [status(thm), theory('equality')], [c_99, c_164])).
% 4.75/1.83  tff(c_207, plain, (![A_58]: (m1_pre_topc(A_58, '#skF_3') | ~m1_pre_topc(A_58, g1_pre_topc('#skF_1'('#skF_2', '#skF_4'), u1_pre_topc('#skF_4'))) | ~l1_pre_topc(A_58))), inference(demodulation, [status(thm), theory('equality')], [c_79, c_170])).
% 4.75/1.83  tff(c_218, plain, (![A_47]: (m1_pre_topc(A_47, '#skF_3') | ~m1_pre_topc(A_47, '#skF_4') | ~l1_pre_topc(A_47))), inference(resolution, [status(thm)], [c_147, c_207])).
% 4.75/1.83  tff(c_139, plain, (![A_47]: (m1_pre_topc(A_47, g1_pre_topc('#skF_1'('#skF_2', '#skF_4'), u1_pre_topc('#skF_4'))) | ~m1_pre_topc(A_47, '#skF_3') | ~l1_pre_topc('#skF_3') | ~l1_pre_topc(A_47))), inference(superposition, [status(thm), theory('equality')], [c_99, c_133])).
% 4.75/1.83  tff(c_145, plain, (![A_47]: (m1_pre_topc(A_47, g1_pre_topc('#skF_1'('#skF_2', '#skF_4'), u1_pre_topc('#skF_4'))) | ~m1_pre_topc(A_47, '#skF_3') | ~l1_pre_topc(A_47))), inference(demodulation, [status(thm), theory('equality')], [c_79, c_139])).
% 4.75/1.83  tff(c_173, plain, (![A_53]: (m1_pre_topc(A_53, '#skF_4') | ~m1_pre_topc(A_53, g1_pre_topc('#skF_1'('#skF_2', '#skF_4'), u1_pre_topc('#skF_4'))) | ~l1_pre_topc('#skF_4') | ~l1_pre_topc(A_53))), inference(superposition, [status(thm), theory('equality')], [c_98, c_164])).
% 4.75/1.83  tff(c_185, plain, (![A_56]: (m1_pre_topc(A_56, '#skF_4') | ~m1_pre_topc(A_56, g1_pre_topc('#skF_1'('#skF_2', '#skF_4'), u1_pre_topc('#skF_4'))) | ~l1_pre_topc(A_56))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_173])).
% 4.75/1.83  tff(c_199, plain, (![A_57]: (m1_pre_topc(A_57, '#skF_4') | ~m1_pre_topc(A_57, '#skF_3') | ~l1_pre_topc(A_57))), inference(resolution, [status(thm)], [c_145, c_185])).
% 4.75/1.83  tff(c_203, plain, (m1_pre_topc('#skF_3', '#skF_4') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_18, c_199])).
% 4.75/1.83  tff(c_206, plain, (m1_pre_topc('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_79, c_203])).
% 4.75/1.83  tff(c_20, plain, (![B_14, A_12]: (r1_tarski(u1_struct_0(B_14), u1_struct_0(A_12)) | ~m1_pre_topc(B_14, A_12) | ~l1_pre_topc(A_12))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.75/1.83  tff(c_103, plain, (![A_12]: (r1_tarski('#skF_1'('#skF_2', '#skF_4'), u1_struct_0(A_12)) | ~m1_pre_topc('#skF_4', A_12) | ~l1_pre_topc(A_12))), inference(superposition, [status(thm), theory('equality')], [c_98, c_20])).
% 4.75/1.83  tff(c_88, plain, (![B_41, A_42]: (r1_tarski(u1_struct_0(B_41), u1_struct_0(A_42)) | ~m1_pre_topc(B_41, A_42) | ~l1_pre_topc(A_42))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.75/1.83  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.75/1.83  tff(c_238, plain, (![B_60, A_61]: (u1_struct_0(B_60)=u1_struct_0(A_61) | ~r1_tarski(u1_struct_0(A_61), u1_struct_0(B_60)) | ~m1_pre_topc(B_60, A_61) | ~l1_pre_topc(A_61))), inference(resolution, [status(thm)], [c_88, c_2])).
% 4.75/1.83  tff(c_241, plain, (![B_60]: (u1_struct_0(B_60)=u1_struct_0('#skF_4') | ~r1_tarski('#skF_1'('#skF_2', '#skF_4'), u1_struct_0(B_60)) | ~m1_pre_topc(B_60, '#skF_4') | ~l1_pre_topc('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_98, c_238])).
% 4.75/1.83  tff(c_258, plain, (![B_62]: (u1_struct_0(B_62)='#skF_1'('#skF_2', '#skF_4') | ~r1_tarski('#skF_1'('#skF_2', '#skF_4'), u1_struct_0(B_62)) | ~m1_pre_topc(B_62, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_98, c_241])).
% 4.75/1.83  tff(c_268, plain, (![A_63]: (u1_struct_0(A_63)='#skF_1'('#skF_2', '#skF_4') | ~m1_pre_topc(A_63, '#skF_4') | ~m1_pre_topc('#skF_4', A_63) | ~l1_pre_topc(A_63))), inference(resolution, [status(thm)], [c_103, c_258])).
% 4.75/1.83  tff(c_270, plain, (u1_struct_0('#skF_3')='#skF_1'('#skF_2', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_206, c_268])).
% 4.75/1.83  tff(c_276, plain, (u1_struct_0('#skF_3')='#skF_1'('#skF_2', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_79, c_270])).
% 4.75/1.83  tff(c_290, plain, (~m1_pre_topc('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_276])).
% 4.75/1.83  tff(c_293, plain, (~m1_pre_topc('#skF_4', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_218, c_290])).
% 4.75/1.83  tff(c_296, plain, (~m1_pre_topc('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_293])).
% 4.75/1.83  tff(c_299, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_18, c_296])).
% 4.75/1.83  tff(c_303, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_76, c_299])).
% 4.75/1.83  tff(c_305, plain, (m1_pre_topc('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_276])).
% 4.75/1.83  tff(c_197, plain, (![A_47]: (m1_pre_topc(A_47, '#skF_4') | ~m1_pre_topc(A_47, '#skF_3') | ~l1_pre_topc(A_47))), inference(resolution, [status(thm)], [c_145, c_185])).
% 4.75/1.83  tff(c_313, plain, (m1_pre_topc('#skF_4', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_305, c_197])).
% 4.75/1.83  tff(c_319, plain, (m1_pre_topc('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_313])).
% 4.75/1.83  tff(c_689, plain, (![B_82]: (v1_subset_1('#skF_1'('#skF_4', B_82), '#skF_1'('#skF_2', '#skF_4')) | u1_struct_0('#skF_4')='#skF_1'('#skF_4', B_82) | v1_tex_2(B_82, '#skF_4') | ~m1_pre_topc(B_82, '#skF_4') | ~l1_pre_topc('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_98, c_680])).
% 4.75/1.83  tff(c_944, plain, (![B_92]: (v1_subset_1('#skF_1'('#skF_4', B_92), '#skF_1'('#skF_2', '#skF_4')) | '#skF_1'('#skF_4', B_92)='#skF_1'('#skF_2', '#skF_4') | v1_tex_2(B_92, '#skF_4') | ~m1_pre_topc(B_92, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_98, c_689])).
% 4.75/1.83  tff(c_158, plain, (![A_51, B_52]: (~v1_subset_1('#skF_1'(A_51, B_52), u1_struct_0(A_51)) | v1_tex_2(B_52, A_51) | ~m1_pre_topc(B_52, A_51) | ~l1_pre_topc(A_51))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.75/1.83  tff(c_161, plain, (![B_52]: (~v1_subset_1('#skF_1'('#skF_4', B_52), '#skF_1'('#skF_2', '#skF_4')) | v1_tex_2(B_52, '#skF_4') | ~m1_pre_topc(B_52, '#skF_4') | ~l1_pre_topc('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_98, c_158])).
% 4.75/1.83  tff(c_163, plain, (![B_52]: (~v1_subset_1('#skF_1'('#skF_4', B_52), '#skF_1'('#skF_2', '#skF_4')) | v1_tex_2(B_52, '#skF_4') | ~m1_pre_topc(B_52, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_161])).
% 4.75/1.83  tff(c_948, plain, (![B_92]: ('#skF_1'('#skF_4', B_92)='#skF_1'('#skF_2', '#skF_4') | v1_tex_2(B_92, '#skF_4') | ~m1_pre_topc(B_92, '#skF_4'))), inference(resolution, [status(thm)], [c_944, c_163])).
% 4.75/1.83  tff(c_304, plain, (u1_struct_0('#skF_3')='#skF_1'('#skF_2', '#skF_4')), inference(splitRight, [status(thm)], [c_276])).
% 4.75/1.83  tff(c_422, plain, (![B_69, A_70]: (v1_subset_1(u1_struct_0(B_69), u1_struct_0(A_70)) | ~m1_subset_1(u1_struct_0(B_69), k1_zfmisc_1(u1_struct_0(A_70))) | ~v1_tex_2(B_69, A_70) | ~m1_pre_topc(B_69, A_70) | ~l1_pre_topc(A_70))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.75/1.83  tff(c_434, plain, (![B_69]: (v1_subset_1(u1_struct_0(B_69), u1_struct_0('#skF_4')) | ~m1_subset_1(u1_struct_0(B_69), k1_zfmisc_1('#skF_1'('#skF_2', '#skF_4'))) | ~v1_tex_2(B_69, '#skF_4') | ~m1_pre_topc(B_69, '#skF_4') | ~l1_pre_topc('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_98, c_422])).
% 4.75/1.83  tff(c_1050, plain, (![B_99]: (v1_subset_1(u1_struct_0(B_99), '#skF_1'('#skF_2', '#skF_4')) | ~m1_subset_1(u1_struct_0(B_99), k1_zfmisc_1('#skF_1'('#skF_2', '#skF_4'))) | ~v1_tex_2(B_99, '#skF_4') | ~m1_pre_topc(B_99, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_98, c_434])).
% 4.75/1.83  tff(c_1056, plain, (v1_subset_1(u1_struct_0('#skF_3'), '#skF_1'('#skF_2', '#skF_4')) | ~m1_subset_1('#skF_1'('#skF_2', '#skF_4'), k1_zfmisc_1('#skF_1'('#skF_2', '#skF_4'))) | ~v1_tex_2('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_304, c_1050])).
% 4.75/1.83  tff(c_1063, plain, (v1_subset_1('#skF_1'('#skF_2', '#skF_4'), '#skF_1'('#skF_2', '#skF_4')) | ~m1_subset_1('#skF_1'('#skF_2', '#skF_4'), k1_zfmisc_1('#skF_1'('#skF_2', '#skF_4'))) | ~v1_tex_2('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_206, c_304, c_1056])).
% 4.75/1.83  tff(c_1064, plain, (~m1_subset_1('#skF_1'('#skF_2', '#skF_4'), k1_zfmisc_1('#skF_1'('#skF_2', '#skF_4'))) | ~v1_tex_2('#skF_3', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_45, c_1063])).
% 4.75/1.83  tff(c_1068, plain, (~v1_tex_2('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_1064])).
% 4.75/1.83  tff(c_1071, plain, ('#skF_1'('#skF_2', '#skF_4')='#skF_1'('#skF_4', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_948, c_1068])).
% 4.75/1.83  tff(c_1080, plain, ('#skF_1'('#skF_2', '#skF_4')='#skF_1'('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_206, c_1071])).
% 4.75/1.83  tff(c_1124, plain, (u1_struct_0('#skF_4')='#skF_1'('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1080, c_98])).
% 4.75/1.83  tff(c_690, plain, (![A_81, B_82]: (u1_struct_0(A_81)='#skF_1'(A_81, B_82) | v1_tex_2(B_82, A_81) | ~m1_pre_topc(B_82, A_81) | ~l1_pre_topc(A_81))), inference(resolution, [status(thm)], [c_680, c_24])).
% 4.75/1.83  tff(c_431, plain, (![A_70]: (v1_subset_1(u1_struct_0('#skF_4'), u1_struct_0(A_70)) | ~m1_subset_1('#skF_1'('#skF_2', '#skF_4'), k1_zfmisc_1(u1_struct_0(A_70))) | ~v1_tex_2('#skF_4', A_70) | ~m1_pre_topc('#skF_4', A_70) | ~l1_pre_topc(A_70))), inference(superposition, [status(thm), theory('equality')], [c_98, c_422])).
% 4.75/1.83  tff(c_438, plain, (![A_70]: (v1_subset_1('#skF_1'('#skF_2', '#skF_4'), u1_struct_0(A_70)) | ~m1_subset_1('#skF_1'('#skF_2', '#skF_4'), k1_zfmisc_1(u1_struct_0(A_70))) | ~v1_tex_2('#skF_4', A_70) | ~m1_pre_topc('#skF_4', A_70) | ~l1_pre_topc(A_70))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_431])).
% 4.75/1.83  tff(c_1310, plain, (![A_100]: (v1_subset_1('#skF_1'('#skF_4', '#skF_3'), u1_struct_0(A_100)) | ~m1_subset_1('#skF_1'('#skF_4', '#skF_3'), k1_zfmisc_1(u1_struct_0(A_100))) | ~v1_tex_2('#skF_4', A_100) | ~m1_pre_topc('#skF_4', A_100) | ~l1_pre_topc(A_100))), inference(demodulation, [status(thm), theory('equality')], [c_1080, c_1080, c_438])).
% 4.75/1.83  tff(c_1323, plain, (v1_subset_1('#skF_1'('#skF_4', '#skF_3'), u1_struct_0('#skF_4')) | ~v1_tex_2('#skF_4', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_4') | v1_tex_2('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_3', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_28, c_1310])).
% 4.75/1.83  tff(c_1335, plain, (v1_subset_1('#skF_1'('#skF_4', '#skF_3'), '#skF_1'('#skF_4', '#skF_3')) | ~v1_tex_2('#skF_4', '#skF_4') | v1_tex_2('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_206, c_319, c_1124, c_1323])).
% 4.75/1.83  tff(c_1336, plain, (~v1_tex_2('#skF_4', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_1068, c_45, c_1335])).
% 4.75/1.83  tff(c_1339, plain, (u1_struct_0('#skF_4')='#skF_1'('#skF_4', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_690, c_1336])).
% 4.75/1.83  tff(c_1345, plain, ('#skF_1'('#skF_4', '#skF_3')='#skF_1'('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_319, c_1124, c_1339])).
% 4.75/1.83  tff(c_1350, plain, (u1_struct_0('#skF_4')='#skF_1'('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1345, c_1124])).
% 4.75/1.83  tff(c_1357, plain, (m1_subset_1('#skF_1'('#skF_4', '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | v1_tex_2('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_3', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1345, c_28])).
% 4.75/1.83  tff(c_1364, plain, (m1_subset_1('#skF_1'('#skF_4', '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | v1_tex_2('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_206, c_1357])).
% 4.75/1.83  tff(c_1365, plain, (m1_subset_1('#skF_1'('#skF_4', '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_1068, c_1364])).
% 4.75/1.83  tff(c_1610, plain, (m1_subset_1('#skF_1'('#skF_4', '#skF_4'), k1_zfmisc_1('#skF_1'('#skF_4', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_1350, c_1365])).
% 4.75/1.83  tff(c_1113, plain, (u1_struct_0('#skF_3')='#skF_1'('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1080, c_304])).
% 4.75/1.83  tff(c_1351, plain, (u1_struct_0('#skF_3')='#skF_1'('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1345, c_1113])).
% 4.75/1.83  tff(c_1353, plain, ('#skF_1'('#skF_2', '#skF_4')='#skF_1'('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1345, c_1080])).
% 4.75/1.83  tff(c_22, plain, (![B_21, A_15]: (v1_subset_1(u1_struct_0(B_21), u1_struct_0(A_15)) | ~m1_subset_1(u1_struct_0(B_21), k1_zfmisc_1(u1_struct_0(A_15))) | ~v1_tex_2(B_21, A_15) | ~m1_pre_topc(B_21, A_15) | ~l1_pre_topc(A_15))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.75/1.83  tff(c_717, plain, (![B_21]: (v1_subset_1(u1_struct_0(B_21), u1_struct_0('#skF_2')) | ~m1_subset_1(u1_struct_0(B_21), k1_zfmisc_1('#skF_1'('#skF_2', '#skF_4'))) | ~v1_tex_2(B_21, '#skF_2') | ~m1_pre_topc(B_21, '#skF_2') | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_701, c_22])).
% 4.75/1.83  tff(c_767, plain, (![B_21]: (v1_subset_1(u1_struct_0(B_21), '#skF_1'('#skF_2', '#skF_4')) | ~m1_subset_1(u1_struct_0(B_21), k1_zfmisc_1('#skF_1'('#skF_2', '#skF_4'))) | ~v1_tex_2(B_21, '#skF_2') | ~m1_pre_topc(B_21, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_701, c_717])).
% 4.75/1.83  tff(c_2593, plain, (![B_136]: (v1_subset_1(u1_struct_0(B_136), '#skF_1'('#skF_4', '#skF_4')) | ~m1_subset_1(u1_struct_0(B_136), k1_zfmisc_1('#skF_1'('#skF_4', '#skF_4'))) | ~v1_tex_2(B_136, '#skF_2') | ~m1_pre_topc(B_136, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_1353, c_1353, c_767])).
% 4.75/1.83  tff(c_2596, plain, (v1_subset_1(u1_struct_0('#skF_3'), '#skF_1'('#skF_4', '#skF_4')) | ~m1_subset_1('#skF_1'('#skF_4', '#skF_4'), k1_zfmisc_1('#skF_1'('#skF_4', '#skF_4'))) | ~v1_tex_2('#skF_3', '#skF_2') | ~m1_pre_topc('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1351, c_2593])).
% 4.75/1.83  tff(c_2604, plain, (v1_subset_1('#skF_1'('#skF_4', '#skF_4'), '#skF_1'('#skF_4', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_36, c_1610, c_1351, c_2596])).
% 4.75/1.83  tff(c_2606, plain, $false, inference(negUnitSimplification, [status(thm)], [c_45, c_2604])).
% 4.75/1.83  tff(c_2607, plain, (~m1_subset_1('#skF_1'('#skF_2', '#skF_4'), k1_zfmisc_1('#skF_1'('#skF_2', '#skF_4')))), inference(splitRight, [status(thm)], [c_1064])).
% 4.75/1.83  tff(c_2611, plain, (v1_tex_2('#skF_4', '#skF_2') | ~m1_pre_topc('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_772, c_2607])).
% 4.75/1.83  tff(c_2614, plain, (v1_tex_2('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_2611])).
% 4.75/1.83  tff(c_2616, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_2614])).
% 4.75/1.83  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.75/1.83  
% 4.75/1.83  Inference rules
% 4.75/1.83  ----------------------
% 4.75/1.83  #Ref     : 0
% 4.75/1.83  #Sup     : 496
% 4.75/1.83  #Fact    : 0
% 4.75/1.83  #Define  : 0
% 4.75/1.83  #Split   : 6
% 4.75/1.83  #Chain   : 0
% 4.75/1.83  #Close   : 0
% 4.75/1.83  
% 4.75/1.83  Ordering : KBO
% 4.75/1.83  
% 4.75/1.83  Simplification rules
% 4.75/1.83  ----------------------
% 4.75/1.83  #Subsume      : 175
% 4.75/1.83  #Demod        : 1302
% 4.75/1.83  #Tautology    : 159
% 4.75/1.83  #SimpNegUnit  : 24
% 4.75/1.83  #BackRed      : 47
% 4.75/1.83  
% 4.75/1.83  #Partial instantiations: 0
% 4.75/1.83  #Strategies tried      : 1
% 4.75/1.83  
% 4.75/1.83  Timing (in seconds)
% 4.75/1.83  ----------------------
% 4.75/1.84  Preprocessing        : 0.31
% 4.75/1.84  Parsing              : 0.17
% 4.75/1.84  CNF conversion       : 0.02
% 4.75/1.84  Main loop            : 0.75
% 4.75/1.84  Inferencing          : 0.21
% 4.75/1.84  Reduction            : 0.32
% 4.75/1.84  Demodulation         : 0.24
% 4.75/1.84  BG Simplification    : 0.02
% 4.75/1.84  Subsumption          : 0.15
% 4.75/1.84  Abstraction          : 0.03
% 4.75/1.84  MUC search           : 0.00
% 4.75/1.84  Cooper               : 0.00
% 4.75/1.84  Total                : 1.11
% 4.75/1.84  Index Insertion      : 0.00
% 4.75/1.84  Index Deletion       : 0.00
% 4.75/1.84  Index Matching       : 0.00
% 4.75/1.84  BG Taut test         : 0.00
%------------------------------------------------------------------------------
