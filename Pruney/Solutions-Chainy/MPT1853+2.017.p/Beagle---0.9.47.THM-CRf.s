%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:02 EST 2020

% Result     : Theorem 4.21s
% Output     : CNFRefutation 4.21s
% Verified   : 
% Statistics : Number of formulae       :  192 ( 564 expanded)
%              Number of leaves         :   43 ( 200 expanded)
%              Depth                    :   15
%              Number of atoms          :  395 (1534 expanded)
%              Number of equality atoms :   29 (  70 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_tex_2 > v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v7_struct_0 > v2_struct_0 > v1_zfmisc_1 > v1_xboole_0 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k6_domain_1 > k1_tex_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(v1_tex_2,type,(
    v1_tex_2: ( $i * $i ) > $o )).

tff(v7_struct_0,type,(
    v7_struct_0: $i > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_187,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ( v1_tex_2(k1_tex_2(A,B),A)
            <=> v1_subset_1(k6_domain_1(u1_struct_0(A),B),u1_struct_0(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_tex_2)).

tff(f_147,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ( ~ v2_struct_0(k1_tex_2(A,B))
        & v1_pre_topc(k1_tex_2(A,B))
        & m1_pre_topc(k1_tex_2(A,B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tex_2)).

tff(f_55,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_48,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_161,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ( ~ v2_struct_0(k1_tex_2(A,B))
        & v7_struct_0(k1_tex_2(A,B))
        & v1_pre_topc(k1_tex_2(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_tex_2)).

tff(f_174,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ~ ( v1_subset_1(k6_domain_1(u1_struct_0(A),B),u1_struct_0(A))
              & v7_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_tex_2)).

tff(f_126,axiom,(
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

tff(f_133,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( v1_subset_1(B,A)
      <=> B != A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).

tff(f_69,axiom,(
    ! [A] :
      ( ( v7_struct_0(A)
        & l1_struct_0(A) )
     => v1_zfmisc_1(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_struct_0)).

tff(f_63,axiom,(
    ! [A] :
      ( ( ~ v7_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_zfmisc_1(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_struct_0)).

tff(f_102,axiom,(
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

tff(f_112,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ( v1_zfmisc_1(A)
      <=> ? [B] :
            ( m1_subset_1(B,A)
            & A = k6_domain_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tex_2)).

tff(f_76,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_83,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => r1_tarski(u1_struct_0(B),u1_struct_0(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_borsuk_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_44,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_68,plain,(
    l1_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_70,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_66,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_1948,plain,(
    ! [A_330,B_331] :
      ( m1_pre_topc(k1_tex_2(A_330,B_331),A_330)
      | ~ m1_subset_1(B_331,u1_struct_0(A_330))
      | ~ l1_pre_topc(A_330)
      | v2_struct_0(A_330) ) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_1953,plain,
    ( m1_pre_topc(k1_tex_2('#skF_5','#skF_6'),'#skF_5')
    | ~ l1_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_66,c_1948])).

tff(c_1957,plain,
    ( m1_pre_topc(k1_tex_2('#skF_5','#skF_6'),'#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_1953])).

tff(c_1958,plain,(
    m1_pre_topc(k1_tex_2('#skF_5','#skF_6'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_1957])).

tff(c_20,plain,(
    ! [B_15,A_13] :
      ( l1_pre_topc(B_15)
      | ~ m1_pre_topc(B_15,A_13)
      | ~ l1_pre_topc(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1972,plain,
    ( l1_pre_topc(k1_tex_2('#skF_5','#skF_6'))
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_1958,c_20])).

tff(c_1986,plain,(
    l1_pre_topc(k1_tex_2('#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_1972])).

tff(c_18,plain,(
    ! [A_12] :
      ( l1_struct_0(A_12)
      | ~ l1_pre_topc(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_1439,plain,(
    ! [A_260,B_261] :
      ( ~ v2_struct_0(k1_tex_2(A_260,B_261))
      | ~ m1_subset_1(B_261,u1_struct_0(A_260))
      | ~ l1_pre_topc(A_260)
      | v2_struct_0(A_260) ) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_1446,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_5','#skF_6'))
    | ~ l1_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_66,c_1439])).

tff(c_1450,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_5','#skF_6'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_1446])).

tff(c_1451,plain,(
    ~ v2_struct_0(k1_tex_2('#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_1450])).

tff(c_998,plain,(
    ! [A_210,B_211] :
      ( ~ v2_struct_0(k1_tex_2(A_210,B_211))
      | ~ m1_subset_1(B_211,u1_struct_0(A_210))
      | ~ l1_pre_topc(A_210)
      | v2_struct_0(A_210) ) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_1005,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_5','#skF_6'))
    | ~ l1_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_66,c_998])).

tff(c_1009,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_5','#skF_6'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_1005])).

tff(c_1010,plain,(
    ~ v2_struct_0(k1_tex_2('#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_1009])).

tff(c_1037,plain,(
    ! [A_224,B_225] :
      ( m1_pre_topc(k1_tex_2(A_224,B_225),A_224)
      | ~ m1_subset_1(B_225,u1_struct_0(A_224))
      | ~ l1_pre_topc(A_224)
      | v2_struct_0(A_224) ) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_1042,plain,
    ( m1_pre_topc(k1_tex_2('#skF_5','#skF_6'),'#skF_5')
    | ~ l1_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_66,c_1037])).

tff(c_1046,plain,
    ( m1_pre_topc(k1_tex_2('#skF_5','#skF_6'),'#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_1042])).

tff(c_1047,plain,(
    m1_pre_topc(k1_tex_2('#skF_5','#skF_6'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_1046])).

tff(c_72,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0('#skF_5'),'#skF_6'),u1_struct_0('#skF_5'))
    | ~ v1_tex_2(k1_tex_2('#skF_5','#skF_6'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_90,plain,(
    ~ v1_tex_2(k1_tex_2('#skF_5','#skF_6'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_72])).

tff(c_78,plain,
    ( v1_tex_2(k1_tex_2('#skF_5','#skF_6'),'#skF_5')
    | v1_subset_1(k6_domain_1(u1_struct_0('#skF_5'),'#skF_6'),u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_131,plain,(
    v1_subset_1(k6_domain_1(u1_struct_0('#skF_5'),'#skF_6'),u1_struct_0('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_78])).

tff(c_538,plain,(
    ! [A_142,B_143] :
      ( ~ v7_struct_0(A_142)
      | ~ v1_subset_1(k6_domain_1(u1_struct_0(A_142),B_143),u1_struct_0(A_142))
      | ~ m1_subset_1(B_143,u1_struct_0(A_142))
      | ~ l1_struct_0(A_142)
      | v2_struct_0(A_142) ) ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_555,plain,
    ( ~ v7_struct_0('#skF_5')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_131,c_538])).

tff(c_565,plain,
    ( ~ v7_struct_0('#skF_5')
    | ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_555])).

tff(c_566,plain,
    ( ~ v7_struct_0('#skF_5')
    | ~ l1_struct_0('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_565])).

tff(c_567,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_566])).

tff(c_570,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_18,c_567])).

tff(c_574,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_570])).

tff(c_575,plain,(
    ~ v7_struct_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_566])).

tff(c_576,plain,(
    l1_struct_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_566])).

tff(c_281,plain,(
    ! [A_111,B_112] :
      ( m1_pre_topc(k1_tex_2(A_111,B_112),A_111)
      | ~ m1_subset_1(B_112,u1_struct_0(A_111))
      | ~ l1_pre_topc(A_111)
      | v2_struct_0(A_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_286,plain,
    ( m1_pre_topc(k1_tex_2('#skF_5','#skF_6'),'#skF_5')
    | ~ l1_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_66,c_281])).

tff(c_290,plain,
    ( m1_pre_topc(k1_tex_2('#skF_5','#skF_6'),'#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_286])).

tff(c_291,plain,(
    m1_pre_topc(k1_tex_2('#skF_5','#skF_6'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_290])).

tff(c_493,plain,(
    ! [A_131,B_132] :
      ( m1_subset_1('#skF_4'(A_131,B_132),k1_zfmisc_1(u1_struct_0(A_131)))
      | v1_tex_2(B_132,A_131)
      | ~ m1_pre_topc(B_132,A_131)
      | ~ l1_pre_topc(A_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_48,plain,(
    ! [B_41,A_40] :
      ( v1_subset_1(B_41,A_40)
      | B_41 = A_40
      | ~ m1_subset_1(B_41,k1_zfmisc_1(A_40)) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_772,plain,(
    ! [A_163,B_164] :
      ( v1_subset_1('#skF_4'(A_163,B_164),u1_struct_0(A_163))
      | u1_struct_0(A_163) = '#skF_4'(A_163,B_164)
      | v1_tex_2(B_164,A_163)
      | ~ m1_pre_topc(B_164,A_163)
      | ~ l1_pre_topc(A_163) ) ),
    inference(resolution,[status(thm)],[c_493,c_48])).

tff(c_42,plain,(
    ! [A_30,B_36] :
      ( ~ v1_subset_1('#skF_4'(A_30,B_36),u1_struct_0(A_30))
      | v1_tex_2(B_36,A_30)
      | ~ m1_pre_topc(B_36,A_30)
      | ~ l1_pre_topc(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_782,plain,(
    ! [A_165,B_166] :
      ( u1_struct_0(A_165) = '#skF_4'(A_165,B_166)
      | v1_tex_2(B_166,A_165)
      | ~ m1_pre_topc(B_166,A_165)
      | ~ l1_pre_topc(A_165) ) ),
    inference(resolution,[status(thm)],[c_772,c_42])).

tff(c_788,plain,
    ( '#skF_4'('#skF_5',k1_tex_2('#skF_5','#skF_6')) = u1_struct_0('#skF_5')
    | ~ m1_pre_topc(k1_tex_2('#skF_5','#skF_6'),'#skF_5')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_782,c_90])).

tff(c_792,plain,(
    '#skF_4'('#skF_5',k1_tex_2('#skF_5','#skF_6')) = u1_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_291,c_788])).

tff(c_294,plain,
    ( l1_pre_topc(k1_tex_2('#skF_5','#skF_6'))
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_291,c_20])).

tff(c_297,plain,(
    l1_pre_topc(k1_tex_2('#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_294])).

tff(c_256,plain,(
    ! [A_101,B_102] :
      ( v7_struct_0(k1_tex_2(A_101,B_102))
      | ~ m1_subset_1(B_102,u1_struct_0(A_101))
      | ~ l1_pre_topc(A_101)
      | v2_struct_0(A_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_263,plain,
    ( v7_struct_0(k1_tex_2('#skF_5','#skF_6'))
    | ~ l1_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_66,c_256])).

tff(c_267,plain,
    ( v7_struct_0(k1_tex_2('#skF_5','#skF_6'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_263])).

tff(c_268,plain,(
    v7_struct_0(k1_tex_2('#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_267])).

tff(c_298,plain,(
    ! [B_113,A_114] :
      ( u1_struct_0(B_113) = '#skF_4'(A_114,B_113)
      | v1_tex_2(B_113,A_114)
      | ~ m1_pre_topc(B_113,A_114)
      | ~ l1_pre_topc(A_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_301,plain,
    ( u1_struct_0(k1_tex_2('#skF_5','#skF_6')) = '#skF_4'('#skF_5',k1_tex_2('#skF_5','#skF_6'))
    | ~ m1_pre_topc(k1_tex_2('#skF_5','#skF_6'),'#skF_5')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_298,c_90])).

tff(c_304,plain,(
    u1_struct_0(k1_tex_2('#skF_5','#skF_6')) = '#skF_4'('#skF_5',k1_tex_2('#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_291,c_301])).

tff(c_24,plain,(
    ! [A_17] :
      ( v1_zfmisc_1(u1_struct_0(A_17))
      | ~ l1_struct_0(A_17)
      | ~ v7_struct_0(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_334,plain,
    ( v1_zfmisc_1('#skF_4'('#skF_5',k1_tex_2('#skF_5','#skF_6')))
    | ~ l1_struct_0(k1_tex_2('#skF_5','#skF_6'))
    | ~ v7_struct_0(k1_tex_2('#skF_5','#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_304,c_24])).

tff(c_359,plain,
    ( v1_zfmisc_1('#skF_4'('#skF_5',k1_tex_2('#skF_5','#skF_6')))
    | ~ l1_struct_0(k1_tex_2('#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_268,c_334])).

tff(c_361,plain,(
    ~ l1_struct_0(k1_tex_2('#skF_5','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_359])).

tff(c_370,plain,(
    ~ l1_pre_topc(k1_tex_2('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_18,c_361])).

tff(c_374,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_297,c_370])).

tff(c_375,plain,(
    v1_zfmisc_1('#skF_4'('#skF_5',k1_tex_2('#skF_5','#skF_6'))) ),
    inference(splitRight,[status(thm)],[c_359])).

tff(c_808,plain,(
    v1_zfmisc_1(u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_792,c_375])).

tff(c_22,plain,(
    ! [A_16] :
      ( ~ v1_zfmisc_1(u1_struct_0(A_16))
      | ~ l1_struct_0(A_16)
      | v7_struct_0(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_828,plain,
    ( ~ l1_struct_0('#skF_5')
    | v7_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_808,c_22])).

tff(c_831,plain,(
    v7_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_576,c_828])).

tff(c_833,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_575,c_831])).

tff(c_835,plain,(
    v1_tex_2(k1_tex_2('#skF_5','#skF_6'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_1054,plain,(
    ! [B_226,A_227] :
      ( ~ v1_tex_2(B_226,A_227)
      | v2_struct_0(B_226)
      | ~ m1_pre_topc(B_226,A_227)
      | ~ l1_pre_topc(A_227)
      | ~ v7_struct_0(A_227)
      | v2_struct_0(A_227) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_1060,plain,
    ( v2_struct_0(k1_tex_2('#skF_5','#skF_6'))
    | ~ m1_pre_topc(k1_tex_2('#skF_5','#skF_6'),'#skF_5')
    | ~ l1_pre_topc('#skF_5')
    | ~ v7_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_835,c_1054])).

tff(c_1064,plain,
    ( v2_struct_0(k1_tex_2('#skF_5','#skF_6'))
    | ~ v7_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_1047,c_1060])).

tff(c_1065,plain,(
    ~ v7_struct_0('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_1010,c_1064])).

tff(c_1050,plain,
    ( l1_pre_topc(k1_tex_2('#skF_5','#skF_6'))
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_1047,c_20])).

tff(c_1053,plain,(
    l1_pre_topc(k1_tex_2('#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_1050])).

tff(c_1011,plain,(
    ! [A_212,B_213] :
      ( v7_struct_0(k1_tex_2(A_212,B_213))
      | ~ m1_subset_1(B_213,u1_struct_0(A_212))
      | ~ l1_pre_topc(A_212)
      | v2_struct_0(A_212) ) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_1018,plain,
    ( v7_struct_0(k1_tex_2('#skF_5','#skF_6'))
    | ~ l1_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_66,c_1011])).

tff(c_1022,plain,
    ( v7_struct_0(k1_tex_2('#skF_5','#skF_6'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_1018])).

tff(c_1023,plain,(
    v7_struct_0(k1_tex_2('#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_1022])).

tff(c_939,plain,(
    ! [A_196,B_197] :
      ( v1_zfmisc_1(A_196)
      | k6_domain_1(A_196,B_197) != A_196
      | ~ m1_subset_1(B_197,A_196)
      | v1_xboole_0(A_196) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_947,plain,
    ( v1_zfmisc_1(u1_struct_0('#skF_5'))
    | k6_domain_1(u1_struct_0('#skF_5'),'#skF_6') != u1_struct_0('#skF_5')
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_66,c_939])).

tff(c_984,plain,(
    k6_domain_1(u1_struct_0('#skF_5'),'#skF_6') != u1_struct_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_947])).

tff(c_948,plain,(
    ! [A_198,B_199] :
      ( m1_subset_1(k6_domain_1(A_198,B_199),k1_zfmisc_1(A_198))
      | ~ m1_subset_1(B_199,A_198)
      | v1_xboole_0(A_198) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_1111,plain,(
    ! [A_237,B_238] :
      ( v1_subset_1(k6_domain_1(A_237,B_238),A_237)
      | k6_domain_1(A_237,B_238) = A_237
      | ~ m1_subset_1(B_238,A_237)
      | v1_xboole_0(A_237) ) ),
    inference(resolution,[status(thm)],[c_948,c_48])).

tff(c_834,plain,(
    ~ v1_subset_1(k6_domain_1(u1_struct_0('#skF_5'),'#skF_6'),u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_836,plain,(
    v1_subset_1(k6_domain_1(u1_struct_0('#skF_5'),'#skF_6'),u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_78])).

tff(c_843,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_834,c_836])).

tff(c_845,plain,(
    ~ v1_subset_1(k6_domain_1(u1_struct_0('#skF_5'),'#skF_6'),u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_1114,plain,
    ( k6_domain_1(u1_struct_0('#skF_5'),'#skF_6') = u1_struct_0('#skF_5')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_1111,c_845])).

tff(c_1120,plain,
    ( k6_domain_1(u1_struct_0('#skF_5'),'#skF_6') = u1_struct_0('#skF_5')
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_1114])).

tff(c_1121,plain,(
    v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_984,c_1120])).

tff(c_927,plain,(
    ! [B_194,A_195] :
      ( r1_tarski(u1_struct_0(B_194),u1_struct_0(A_195))
      | ~ m1_pre_topc(B_194,A_195)
      | ~ l1_pre_topc(A_195) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_854,plain,(
    ! [A_172,B_173] :
      ( r2_hidden('#skF_2'(A_172,B_173),A_172)
      | r1_tarski(A_172,B_173) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_858,plain,(
    ! [A_172,B_173] :
      ( ~ v1_xboole_0(A_172)
      | r1_tarski(A_172,B_173) ) ),
    inference(resolution,[status(thm)],[c_854,c_2])).

tff(c_867,plain,(
    ! [B_178,A_179] :
      ( B_178 = A_179
      | ~ r1_tarski(B_178,A_179)
      | ~ r1_tarski(A_179,B_178) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_872,plain,(
    ! [B_173,A_172] :
      ( B_173 = A_172
      | ~ r1_tarski(B_173,A_172)
      | ~ v1_xboole_0(A_172) ) ),
    inference(resolution,[status(thm)],[c_858,c_867])).

tff(c_937,plain,(
    ! [B_194,A_195] :
      ( u1_struct_0(B_194) = u1_struct_0(A_195)
      | ~ v1_xboole_0(u1_struct_0(A_195))
      | ~ m1_pre_topc(B_194,A_195)
      | ~ l1_pre_topc(A_195) ) ),
    inference(resolution,[status(thm)],[c_927,c_872])).

tff(c_1123,plain,(
    ! [B_194] :
      ( u1_struct_0(B_194) = u1_struct_0('#skF_5')
      | ~ m1_pre_topc(B_194,'#skF_5')
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_1121,c_937])).

tff(c_1196,plain,(
    ! [B_245] :
      ( u1_struct_0(B_245) = u1_struct_0('#skF_5')
      | ~ m1_pre_topc(B_245,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_1123])).

tff(c_1200,plain,(
    u1_struct_0(k1_tex_2('#skF_5','#skF_6')) = u1_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_1047,c_1196])).

tff(c_1254,plain,
    ( v1_zfmisc_1(u1_struct_0('#skF_5'))
    | ~ l1_struct_0(k1_tex_2('#skF_5','#skF_6'))
    | ~ v7_struct_0(k1_tex_2('#skF_5','#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1200,c_24])).

tff(c_1296,plain,
    ( v1_zfmisc_1(u1_struct_0('#skF_5'))
    | ~ l1_struct_0(k1_tex_2('#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1023,c_1254])).

tff(c_1325,plain,(
    ~ l1_struct_0(k1_tex_2('#skF_5','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_1296])).

tff(c_1328,plain,(
    ~ l1_pre_topc(k1_tex_2('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_18,c_1325])).

tff(c_1332,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1053,c_1328])).

tff(c_1333,plain,(
    v1_zfmisc_1(u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_1296])).

tff(c_1337,plain,
    ( ~ l1_struct_0('#skF_5')
    | v7_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_1333,c_22])).

tff(c_1340,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_1065,c_1337])).

tff(c_1358,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_18,c_1340])).

tff(c_1362,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_1358])).

tff(c_1363,plain,
    ( v1_xboole_0(u1_struct_0('#skF_5'))
    | v1_zfmisc_1(u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_947])).

tff(c_1365,plain,(
    v1_zfmisc_1(u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_1363])).

tff(c_1369,plain,
    ( ~ l1_struct_0('#skF_5')
    | v7_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_1365,c_22])).

tff(c_1380,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_1369])).

tff(c_1383,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_18,c_1380])).

tff(c_1387,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_1383])).

tff(c_1388,plain,(
    v7_struct_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_1369])).

tff(c_1465,plain,(
    ! [A_264,B_265] :
      ( m1_pre_topc(k1_tex_2(A_264,B_265),A_264)
      | ~ m1_subset_1(B_265,u1_struct_0(A_264))
      | ~ l1_pre_topc(A_264)
      | v2_struct_0(A_264) ) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_1470,plain,
    ( m1_pre_topc(k1_tex_2('#skF_5','#skF_6'),'#skF_5')
    | ~ l1_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_66,c_1465])).

tff(c_1474,plain,
    ( m1_pre_topc(k1_tex_2('#skF_5','#skF_6'),'#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_1470])).

tff(c_1475,plain,(
    m1_pre_topc(k1_tex_2('#skF_5','#skF_6'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_1474])).

tff(c_1774,plain,(
    ! [B_294,A_295] :
      ( ~ v1_tex_2(B_294,A_295)
      | v2_struct_0(B_294)
      | ~ m1_pre_topc(B_294,A_295)
      | ~ l1_pre_topc(A_295)
      | ~ v7_struct_0(A_295)
      | v2_struct_0(A_295) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_1780,plain,
    ( v2_struct_0(k1_tex_2('#skF_5','#skF_6'))
    | ~ m1_pre_topc(k1_tex_2('#skF_5','#skF_6'),'#skF_5')
    | ~ l1_pre_topc('#skF_5')
    | ~ v7_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_835,c_1774])).

tff(c_1784,plain,
    ( v2_struct_0(k1_tex_2('#skF_5','#skF_6'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1388,c_68,c_1475,c_1780])).

tff(c_1786,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_1451,c_1784])).

tff(c_1788,plain,(
    ~ v1_zfmisc_1(u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_1363])).

tff(c_1830,plain,(
    ! [A_299,B_300] :
      ( v7_struct_0(k1_tex_2(A_299,B_300))
      | ~ m1_subset_1(B_300,u1_struct_0(A_299))
      | ~ l1_pre_topc(A_299)
      | v2_struct_0(A_299) ) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_1837,plain,
    ( v7_struct_0(k1_tex_2('#skF_5','#skF_6'))
    | ~ l1_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_66,c_1830])).

tff(c_1841,plain,
    ( v7_struct_0(k1_tex_2('#skF_5','#skF_6'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_1837])).

tff(c_1842,plain,(
    v7_struct_0(k1_tex_2('#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_1841])).

tff(c_1787,plain,(
    v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_1363])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_888,plain,(
    ! [C_184,B_185,A_186] :
      ( r2_hidden(C_184,B_185)
      | ~ r2_hidden(C_184,A_186)
      | ~ r1_tarski(A_186,B_185) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_910,plain,(
    ! [A_190,B_191] :
      ( r2_hidden('#skF_1'(A_190),B_191)
      | ~ r1_tarski(A_190,B_191)
      | v1_xboole_0(A_190) ) ),
    inference(resolution,[status(thm)],[c_4,c_888])).

tff(c_917,plain,(
    ! [B_191,A_190] :
      ( ~ v1_xboole_0(B_191)
      | ~ r1_tarski(A_190,B_191)
      | v1_xboole_0(A_190) ) ),
    inference(resolution,[status(thm)],[c_910,c_2])).

tff(c_936,plain,(
    ! [A_195,B_194] :
      ( ~ v1_xboole_0(u1_struct_0(A_195))
      | v1_xboole_0(u1_struct_0(B_194))
      | ~ m1_pre_topc(B_194,A_195)
      | ~ l1_pre_topc(A_195) ) ),
    inference(resolution,[status(thm)],[c_927,c_917])).

tff(c_1790,plain,(
    ! [B_194] :
      ( v1_xboole_0(u1_struct_0(B_194))
      | ~ m1_pre_topc(B_194,'#skF_5')
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_1787,c_936])).

tff(c_1818,plain,(
    ! [B_297] :
      ( v1_xboole_0(u1_struct_0(B_297))
      | ~ m1_pre_topc(B_297,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_1790])).

tff(c_877,plain,(
    ! [B_180,A_181] :
      ( B_180 = A_181
      | ~ r1_tarski(B_180,A_181)
      | ~ v1_xboole_0(A_181) ) ),
    inference(resolution,[status(thm)],[c_858,c_867])).

tff(c_884,plain,(
    ! [B_173,A_172] :
      ( B_173 = A_172
      | ~ v1_xboole_0(B_173)
      | ~ v1_xboole_0(A_172) ) ),
    inference(resolution,[status(thm)],[c_858,c_877])).

tff(c_1796,plain,(
    ! [A_172] :
      ( u1_struct_0('#skF_5') = A_172
      | ~ v1_xboole_0(A_172) ) ),
    inference(resolution,[status(thm)],[c_1787,c_884])).

tff(c_1826,plain,(
    ! [B_297] :
      ( u1_struct_0(B_297) = u1_struct_0('#skF_5')
      | ~ m1_pre_topc(B_297,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_1818,c_1796])).

tff(c_1983,plain,(
    u1_struct_0(k1_tex_2('#skF_5','#skF_6')) = u1_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_1958,c_1826])).

tff(c_2037,plain,
    ( v1_zfmisc_1(u1_struct_0('#skF_5'))
    | ~ l1_struct_0(k1_tex_2('#skF_5','#skF_6'))
    | ~ v7_struct_0(k1_tex_2('#skF_5','#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1983,c_24])).

tff(c_2068,plain,
    ( v1_zfmisc_1(u1_struct_0('#skF_5'))
    | ~ l1_struct_0(k1_tex_2('#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1842,c_2037])).

tff(c_2069,plain,(
    ~ l1_struct_0(k1_tex_2('#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_1788,c_2068])).

tff(c_2099,plain,(
    ~ l1_pre_topc(k1_tex_2('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_18,c_2069])).

tff(c_2103,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1986,c_2099])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:05:00 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.21/1.68  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.21/1.70  
% 4.21/1.70  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.21/1.70  %$ v1_tex_2 > v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v7_struct_0 > v2_struct_0 > v1_zfmisc_1 > v1_xboole_0 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k6_domain_1 > k1_tex_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4
% 4.21/1.70  
% 4.21/1.70  %Foreground sorts:
% 4.21/1.70  
% 4.21/1.70  
% 4.21/1.70  %Background operators:
% 4.21/1.70  
% 4.21/1.70  
% 4.21/1.70  %Foreground operators:
% 4.21/1.70  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.21/1.70  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.21/1.70  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.21/1.70  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 4.21/1.70  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.21/1.70  tff(v1_tex_2, type, v1_tex_2: ($i * $i) > $o).
% 4.21/1.70  tff(v7_struct_0, type, v7_struct_0: $i > $o).
% 4.21/1.70  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.21/1.70  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 4.21/1.70  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.21/1.70  tff('#skF_5', type, '#skF_5': $i).
% 4.21/1.70  tff('#skF_6', type, '#skF_6': $i).
% 4.21/1.70  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 4.21/1.70  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.21/1.70  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 4.21/1.70  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.21/1.70  tff(k1_tex_2, type, k1_tex_2: ($i * $i) > $i).
% 4.21/1.70  tff('#skF_3', type, '#skF_3': $i > $i).
% 4.21/1.70  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.21/1.70  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.21/1.70  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 4.21/1.70  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 4.21/1.70  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.21/1.70  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.21/1.70  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 4.21/1.70  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.21/1.70  
% 4.21/1.73  tff(f_187, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (v1_tex_2(k1_tex_2(A, B), A) <=> v1_subset_1(k6_domain_1(u1_struct_0(A), B), u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_tex_2)).
% 4.21/1.73  tff(f_147, axiom, (![A, B]: (((~v2_struct_0(A) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => ((~v2_struct_0(k1_tex_2(A, B)) & v1_pre_topc(k1_tex_2(A, B))) & m1_pre_topc(k1_tex_2(A, B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_tex_2)).
% 4.21/1.73  tff(f_55, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 4.21/1.73  tff(f_48, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 4.21/1.73  tff(f_161, axiom, (![A, B]: (((~v2_struct_0(A) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => ((~v2_struct_0(k1_tex_2(A, B)) & v7_struct_0(k1_tex_2(A, B))) & v1_pre_topc(k1_tex_2(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_tex_2)).
% 4.21/1.73  tff(f_174, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => ~(v1_subset_1(k6_domain_1(u1_struct_0(A), B), u1_struct_0(A)) & v7_struct_0(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_tex_2)).
% 4.21/1.73  tff(f_126, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (v1_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => v1_subset_1(C, u1_struct_0(A)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tex_2)).
% 4.21/1.73  tff(f_133, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (v1_subset_1(B, A) <=> ~(B = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_subset_1)).
% 4.21/1.73  tff(f_69, axiom, (![A]: ((v7_struct_0(A) & l1_struct_0(A)) => v1_zfmisc_1(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc7_struct_0)).
% 4.21/1.73  tff(f_63, axiom, (![A]: ((~v7_struct_0(A) & l1_struct_0(A)) => ~v1_zfmisc_1(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_struct_0)).
% 4.21/1.73  tff(f_102, axiom, (![A]: (((~v2_struct_0(A) & v7_struct_0(A)) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (~v2_struct_0(B) => (~v2_struct_0(B) & ~v1_tex_2(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc10_tex_2)).
% 4.21/1.73  tff(f_112, axiom, (![A]: (~v1_xboole_0(A) => (v1_zfmisc_1(A) <=> (?[B]: (m1_subset_1(B, A) & (A = k6_domain_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tex_2)).
% 4.21/1.73  tff(f_76, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 4.21/1.73  tff(f_83, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => r1_tarski(u1_struct_0(B), u1_struct_0(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_borsuk_1)).
% 4.21/1.73  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 4.21/1.73  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 4.21/1.73  tff(f_44, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.21/1.73  tff(c_68, plain, (l1_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_187])).
% 4.21/1.73  tff(c_70, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_187])).
% 4.21/1.73  tff(c_66, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_187])).
% 4.21/1.73  tff(c_1948, plain, (![A_330, B_331]: (m1_pre_topc(k1_tex_2(A_330, B_331), A_330) | ~m1_subset_1(B_331, u1_struct_0(A_330)) | ~l1_pre_topc(A_330) | v2_struct_0(A_330))), inference(cnfTransformation, [status(thm)], [f_147])).
% 4.21/1.73  tff(c_1953, plain, (m1_pre_topc(k1_tex_2('#skF_5', '#skF_6'), '#skF_5') | ~l1_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_66, c_1948])).
% 4.21/1.73  tff(c_1957, plain, (m1_pre_topc(k1_tex_2('#skF_5', '#skF_6'), '#skF_5') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_1953])).
% 4.21/1.73  tff(c_1958, plain, (m1_pre_topc(k1_tex_2('#skF_5', '#skF_6'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_70, c_1957])).
% 4.21/1.73  tff(c_20, plain, (![B_15, A_13]: (l1_pre_topc(B_15) | ~m1_pre_topc(B_15, A_13) | ~l1_pre_topc(A_13))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.21/1.73  tff(c_1972, plain, (l1_pre_topc(k1_tex_2('#skF_5', '#skF_6')) | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_1958, c_20])).
% 4.21/1.73  tff(c_1986, plain, (l1_pre_topc(k1_tex_2('#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_1972])).
% 4.21/1.73  tff(c_18, plain, (![A_12]: (l1_struct_0(A_12) | ~l1_pre_topc(A_12))), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.21/1.73  tff(c_1439, plain, (![A_260, B_261]: (~v2_struct_0(k1_tex_2(A_260, B_261)) | ~m1_subset_1(B_261, u1_struct_0(A_260)) | ~l1_pre_topc(A_260) | v2_struct_0(A_260))), inference(cnfTransformation, [status(thm)], [f_161])).
% 4.21/1.73  tff(c_1446, plain, (~v2_struct_0(k1_tex_2('#skF_5', '#skF_6')) | ~l1_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_66, c_1439])).
% 4.21/1.73  tff(c_1450, plain, (~v2_struct_0(k1_tex_2('#skF_5', '#skF_6')) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_1446])).
% 4.21/1.73  tff(c_1451, plain, (~v2_struct_0(k1_tex_2('#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_70, c_1450])).
% 4.21/1.73  tff(c_998, plain, (![A_210, B_211]: (~v2_struct_0(k1_tex_2(A_210, B_211)) | ~m1_subset_1(B_211, u1_struct_0(A_210)) | ~l1_pre_topc(A_210) | v2_struct_0(A_210))), inference(cnfTransformation, [status(thm)], [f_161])).
% 4.21/1.73  tff(c_1005, plain, (~v2_struct_0(k1_tex_2('#skF_5', '#skF_6')) | ~l1_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_66, c_998])).
% 4.21/1.73  tff(c_1009, plain, (~v2_struct_0(k1_tex_2('#skF_5', '#skF_6')) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_1005])).
% 4.21/1.73  tff(c_1010, plain, (~v2_struct_0(k1_tex_2('#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_70, c_1009])).
% 4.21/1.73  tff(c_1037, plain, (![A_224, B_225]: (m1_pre_topc(k1_tex_2(A_224, B_225), A_224) | ~m1_subset_1(B_225, u1_struct_0(A_224)) | ~l1_pre_topc(A_224) | v2_struct_0(A_224))), inference(cnfTransformation, [status(thm)], [f_147])).
% 4.21/1.73  tff(c_1042, plain, (m1_pre_topc(k1_tex_2('#skF_5', '#skF_6'), '#skF_5') | ~l1_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_66, c_1037])).
% 4.21/1.73  tff(c_1046, plain, (m1_pre_topc(k1_tex_2('#skF_5', '#skF_6'), '#skF_5') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_1042])).
% 4.21/1.73  tff(c_1047, plain, (m1_pre_topc(k1_tex_2('#skF_5', '#skF_6'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_70, c_1046])).
% 4.21/1.73  tff(c_72, plain, (~v1_subset_1(k6_domain_1(u1_struct_0('#skF_5'), '#skF_6'), u1_struct_0('#skF_5')) | ~v1_tex_2(k1_tex_2('#skF_5', '#skF_6'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_187])).
% 4.21/1.73  tff(c_90, plain, (~v1_tex_2(k1_tex_2('#skF_5', '#skF_6'), '#skF_5')), inference(splitLeft, [status(thm)], [c_72])).
% 4.21/1.73  tff(c_78, plain, (v1_tex_2(k1_tex_2('#skF_5', '#skF_6'), '#skF_5') | v1_subset_1(k6_domain_1(u1_struct_0('#skF_5'), '#skF_6'), u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_187])).
% 4.21/1.73  tff(c_131, plain, (v1_subset_1(k6_domain_1(u1_struct_0('#skF_5'), '#skF_6'), u1_struct_0('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_90, c_78])).
% 4.21/1.73  tff(c_538, plain, (![A_142, B_143]: (~v7_struct_0(A_142) | ~v1_subset_1(k6_domain_1(u1_struct_0(A_142), B_143), u1_struct_0(A_142)) | ~m1_subset_1(B_143, u1_struct_0(A_142)) | ~l1_struct_0(A_142) | v2_struct_0(A_142))), inference(cnfTransformation, [status(thm)], [f_174])).
% 4.21/1.73  tff(c_555, plain, (~v7_struct_0('#skF_5') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~l1_struct_0('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_131, c_538])).
% 4.21/1.73  tff(c_565, plain, (~v7_struct_0('#skF_5') | ~l1_struct_0('#skF_5') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_555])).
% 4.21/1.73  tff(c_566, plain, (~v7_struct_0('#skF_5') | ~l1_struct_0('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_70, c_565])).
% 4.21/1.73  tff(c_567, plain, (~l1_struct_0('#skF_5')), inference(splitLeft, [status(thm)], [c_566])).
% 4.21/1.73  tff(c_570, plain, (~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_18, c_567])).
% 4.21/1.73  tff(c_574, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_68, c_570])).
% 4.21/1.73  tff(c_575, plain, (~v7_struct_0('#skF_5')), inference(splitRight, [status(thm)], [c_566])).
% 4.21/1.73  tff(c_576, plain, (l1_struct_0('#skF_5')), inference(splitRight, [status(thm)], [c_566])).
% 4.21/1.73  tff(c_281, plain, (![A_111, B_112]: (m1_pre_topc(k1_tex_2(A_111, B_112), A_111) | ~m1_subset_1(B_112, u1_struct_0(A_111)) | ~l1_pre_topc(A_111) | v2_struct_0(A_111))), inference(cnfTransformation, [status(thm)], [f_147])).
% 4.21/1.73  tff(c_286, plain, (m1_pre_topc(k1_tex_2('#skF_5', '#skF_6'), '#skF_5') | ~l1_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_66, c_281])).
% 4.21/1.73  tff(c_290, plain, (m1_pre_topc(k1_tex_2('#skF_5', '#skF_6'), '#skF_5') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_286])).
% 4.21/1.73  tff(c_291, plain, (m1_pre_topc(k1_tex_2('#skF_5', '#skF_6'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_70, c_290])).
% 4.21/1.73  tff(c_493, plain, (![A_131, B_132]: (m1_subset_1('#skF_4'(A_131, B_132), k1_zfmisc_1(u1_struct_0(A_131))) | v1_tex_2(B_132, A_131) | ~m1_pre_topc(B_132, A_131) | ~l1_pre_topc(A_131))), inference(cnfTransformation, [status(thm)], [f_126])).
% 4.21/1.73  tff(c_48, plain, (![B_41, A_40]: (v1_subset_1(B_41, A_40) | B_41=A_40 | ~m1_subset_1(B_41, k1_zfmisc_1(A_40)))), inference(cnfTransformation, [status(thm)], [f_133])).
% 4.21/1.73  tff(c_772, plain, (![A_163, B_164]: (v1_subset_1('#skF_4'(A_163, B_164), u1_struct_0(A_163)) | u1_struct_0(A_163)='#skF_4'(A_163, B_164) | v1_tex_2(B_164, A_163) | ~m1_pre_topc(B_164, A_163) | ~l1_pre_topc(A_163))), inference(resolution, [status(thm)], [c_493, c_48])).
% 4.21/1.73  tff(c_42, plain, (![A_30, B_36]: (~v1_subset_1('#skF_4'(A_30, B_36), u1_struct_0(A_30)) | v1_tex_2(B_36, A_30) | ~m1_pre_topc(B_36, A_30) | ~l1_pre_topc(A_30))), inference(cnfTransformation, [status(thm)], [f_126])).
% 4.21/1.73  tff(c_782, plain, (![A_165, B_166]: (u1_struct_0(A_165)='#skF_4'(A_165, B_166) | v1_tex_2(B_166, A_165) | ~m1_pre_topc(B_166, A_165) | ~l1_pre_topc(A_165))), inference(resolution, [status(thm)], [c_772, c_42])).
% 4.21/1.73  tff(c_788, plain, ('#skF_4'('#skF_5', k1_tex_2('#skF_5', '#skF_6'))=u1_struct_0('#skF_5') | ~m1_pre_topc(k1_tex_2('#skF_5', '#skF_6'), '#skF_5') | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_782, c_90])).
% 4.21/1.73  tff(c_792, plain, ('#skF_4'('#skF_5', k1_tex_2('#skF_5', '#skF_6'))=u1_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_291, c_788])).
% 4.21/1.73  tff(c_294, plain, (l1_pre_topc(k1_tex_2('#skF_5', '#skF_6')) | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_291, c_20])).
% 4.21/1.73  tff(c_297, plain, (l1_pre_topc(k1_tex_2('#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_294])).
% 4.21/1.73  tff(c_256, plain, (![A_101, B_102]: (v7_struct_0(k1_tex_2(A_101, B_102)) | ~m1_subset_1(B_102, u1_struct_0(A_101)) | ~l1_pre_topc(A_101) | v2_struct_0(A_101))), inference(cnfTransformation, [status(thm)], [f_161])).
% 4.21/1.73  tff(c_263, plain, (v7_struct_0(k1_tex_2('#skF_5', '#skF_6')) | ~l1_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_66, c_256])).
% 4.21/1.73  tff(c_267, plain, (v7_struct_0(k1_tex_2('#skF_5', '#skF_6')) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_263])).
% 4.21/1.73  tff(c_268, plain, (v7_struct_0(k1_tex_2('#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_70, c_267])).
% 4.21/1.73  tff(c_298, plain, (![B_113, A_114]: (u1_struct_0(B_113)='#skF_4'(A_114, B_113) | v1_tex_2(B_113, A_114) | ~m1_pre_topc(B_113, A_114) | ~l1_pre_topc(A_114))), inference(cnfTransformation, [status(thm)], [f_126])).
% 4.21/1.73  tff(c_301, plain, (u1_struct_0(k1_tex_2('#skF_5', '#skF_6'))='#skF_4'('#skF_5', k1_tex_2('#skF_5', '#skF_6')) | ~m1_pre_topc(k1_tex_2('#skF_5', '#skF_6'), '#skF_5') | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_298, c_90])).
% 4.21/1.73  tff(c_304, plain, (u1_struct_0(k1_tex_2('#skF_5', '#skF_6'))='#skF_4'('#skF_5', k1_tex_2('#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_291, c_301])).
% 4.21/1.73  tff(c_24, plain, (![A_17]: (v1_zfmisc_1(u1_struct_0(A_17)) | ~l1_struct_0(A_17) | ~v7_struct_0(A_17))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.21/1.73  tff(c_334, plain, (v1_zfmisc_1('#skF_4'('#skF_5', k1_tex_2('#skF_5', '#skF_6'))) | ~l1_struct_0(k1_tex_2('#skF_5', '#skF_6')) | ~v7_struct_0(k1_tex_2('#skF_5', '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_304, c_24])).
% 4.21/1.73  tff(c_359, plain, (v1_zfmisc_1('#skF_4'('#skF_5', k1_tex_2('#skF_5', '#skF_6'))) | ~l1_struct_0(k1_tex_2('#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_268, c_334])).
% 4.21/1.73  tff(c_361, plain, (~l1_struct_0(k1_tex_2('#skF_5', '#skF_6'))), inference(splitLeft, [status(thm)], [c_359])).
% 4.21/1.73  tff(c_370, plain, (~l1_pre_topc(k1_tex_2('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_18, c_361])).
% 4.21/1.73  tff(c_374, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_297, c_370])).
% 4.21/1.73  tff(c_375, plain, (v1_zfmisc_1('#skF_4'('#skF_5', k1_tex_2('#skF_5', '#skF_6')))), inference(splitRight, [status(thm)], [c_359])).
% 4.21/1.73  tff(c_808, plain, (v1_zfmisc_1(u1_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_792, c_375])).
% 4.21/1.73  tff(c_22, plain, (![A_16]: (~v1_zfmisc_1(u1_struct_0(A_16)) | ~l1_struct_0(A_16) | v7_struct_0(A_16))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.21/1.73  tff(c_828, plain, (~l1_struct_0('#skF_5') | v7_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_808, c_22])).
% 4.21/1.73  tff(c_831, plain, (v7_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_576, c_828])).
% 4.21/1.73  tff(c_833, plain, $false, inference(negUnitSimplification, [status(thm)], [c_575, c_831])).
% 4.21/1.73  tff(c_835, plain, (v1_tex_2(k1_tex_2('#skF_5', '#skF_6'), '#skF_5')), inference(splitRight, [status(thm)], [c_72])).
% 4.21/1.73  tff(c_1054, plain, (![B_226, A_227]: (~v1_tex_2(B_226, A_227) | v2_struct_0(B_226) | ~m1_pre_topc(B_226, A_227) | ~l1_pre_topc(A_227) | ~v7_struct_0(A_227) | v2_struct_0(A_227))), inference(cnfTransformation, [status(thm)], [f_102])).
% 4.21/1.73  tff(c_1060, plain, (v2_struct_0(k1_tex_2('#skF_5', '#skF_6')) | ~m1_pre_topc(k1_tex_2('#skF_5', '#skF_6'), '#skF_5') | ~l1_pre_topc('#skF_5') | ~v7_struct_0('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_835, c_1054])).
% 4.21/1.73  tff(c_1064, plain, (v2_struct_0(k1_tex_2('#skF_5', '#skF_6')) | ~v7_struct_0('#skF_5') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_1047, c_1060])).
% 4.21/1.73  tff(c_1065, plain, (~v7_struct_0('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_70, c_1010, c_1064])).
% 4.21/1.73  tff(c_1050, plain, (l1_pre_topc(k1_tex_2('#skF_5', '#skF_6')) | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_1047, c_20])).
% 4.21/1.73  tff(c_1053, plain, (l1_pre_topc(k1_tex_2('#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_1050])).
% 4.21/1.73  tff(c_1011, plain, (![A_212, B_213]: (v7_struct_0(k1_tex_2(A_212, B_213)) | ~m1_subset_1(B_213, u1_struct_0(A_212)) | ~l1_pre_topc(A_212) | v2_struct_0(A_212))), inference(cnfTransformation, [status(thm)], [f_161])).
% 4.21/1.73  tff(c_1018, plain, (v7_struct_0(k1_tex_2('#skF_5', '#skF_6')) | ~l1_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_66, c_1011])).
% 4.21/1.73  tff(c_1022, plain, (v7_struct_0(k1_tex_2('#skF_5', '#skF_6')) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_1018])).
% 4.21/1.73  tff(c_1023, plain, (v7_struct_0(k1_tex_2('#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_70, c_1022])).
% 4.21/1.73  tff(c_939, plain, (![A_196, B_197]: (v1_zfmisc_1(A_196) | k6_domain_1(A_196, B_197)!=A_196 | ~m1_subset_1(B_197, A_196) | v1_xboole_0(A_196))), inference(cnfTransformation, [status(thm)], [f_112])).
% 4.21/1.73  tff(c_947, plain, (v1_zfmisc_1(u1_struct_0('#skF_5')) | k6_domain_1(u1_struct_0('#skF_5'), '#skF_6')!=u1_struct_0('#skF_5') | v1_xboole_0(u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_66, c_939])).
% 4.21/1.73  tff(c_984, plain, (k6_domain_1(u1_struct_0('#skF_5'), '#skF_6')!=u1_struct_0('#skF_5')), inference(splitLeft, [status(thm)], [c_947])).
% 4.21/1.73  tff(c_948, plain, (![A_198, B_199]: (m1_subset_1(k6_domain_1(A_198, B_199), k1_zfmisc_1(A_198)) | ~m1_subset_1(B_199, A_198) | v1_xboole_0(A_198))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.21/1.73  tff(c_1111, plain, (![A_237, B_238]: (v1_subset_1(k6_domain_1(A_237, B_238), A_237) | k6_domain_1(A_237, B_238)=A_237 | ~m1_subset_1(B_238, A_237) | v1_xboole_0(A_237))), inference(resolution, [status(thm)], [c_948, c_48])).
% 4.21/1.73  tff(c_834, plain, (~v1_subset_1(k6_domain_1(u1_struct_0('#skF_5'), '#skF_6'), u1_struct_0('#skF_5'))), inference(splitRight, [status(thm)], [c_72])).
% 4.21/1.73  tff(c_836, plain, (v1_subset_1(k6_domain_1(u1_struct_0('#skF_5'), '#skF_6'), u1_struct_0('#skF_5'))), inference(splitLeft, [status(thm)], [c_78])).
% 4.21/1.73  tff(c_843, plain, $false, inference(negUnitSimplification, [status(thm)], [c_834, c_836])).
% 4.21/1.73  tff(c_845, plain, (~v1_subset_1(k6_domain_1(u1_struct_0('#skF_5'), '#skF_6'), u1_struct_0('#skF_5'))), inference(splitRight, [status(thm)], [c_78])).
% 4.21/1.73  tff(c_1114, plain, (k6_domain_1(u1_struct_0('#skF_5'), '#skF_6')=u1_struct_0('#skF_5') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | v1_xboole_0(u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_1111, c_845])).
% 4.21/1.73  tff(c_1120, plain, (k6_domain_1(u1_struct_0('#skF_5'), '#skF_6')=u1_struct_0('#skF_5') | v1_xboole_0(u1_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_1114])).
% 4.21/1.73  tff(c_1121, plain, (v1_xboole_0(u1_struct_0('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_984, c_1120])).
% 4.21/1.73  tff(c_927, plain, (![B_194, A_195]: (r1_tarski(u1_struct_0(B_194), u1_struct_0(A_195)) | ~m1_pre_topc(B_194, A_195) | ~l1_pre_topc(A_195))), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.21/1.73  tff(c_854, plain, (![A_172, B_173]: (r2_hidden('#skF_2'(A_172, B_173), A_172) | r1_tarski(A_172, B_173))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.21/1.73  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.21/1.73  tff(c_858, plain, (![A_172, B_173]: (~v1_xboole_0(A_172) | r1_tarski(A_172, B_173))), inference(resolution, [status(thm)], [c_854, c_2])).
% 4.21/1.73  tff(c_867, plain, (![B_178, A_179]: (B_178=A_179 | ~r1_tarski(B_178, A_179) | ~r1_tarski(A_179, B_178))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.21/1.73  tff(c_872, plain, (![B_173, A_172]: (B_173=A_172 | ~r1_tarski(B_173, A_172) | ~v1_xboole_0(A_172))), inference(resolution, [status(thm)], [c_858, c_867])).
% 4.21/1.73  tff(c_937, plain, (![B_194, A_195]: (u1_struct_0(B_194)=u1_struct_0(A_195) | ~v1_xboole_0(u1_struct_0(A_195)) | ~m1_pre_topc(B_194, A_195) | ~l1_pre_topc(A_195))), inference(resolution, [status(thm)], [c_927, c_872])).
% 4.21/1.73  tff(c_1123, plain, (![B_194]: (u1_struct_0(B_194)=u1_struct_0('#skF_5') | ~m1_pre_topc(B_194, '#skF_5') | ~l1_pre_topc('#skF_5'))), inference(resolution, [status(thm)], [c_1121, c_937])).
% 4.21/1.73  tff(c_1196, plain, (![B_245]: (u1_struct_0(B_245)=u1_struct_0('#skF_5') | ~m1_pre_topc(B_245, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_1123])).
% 4.21/1.73  tff(c_1200, plain, (u1_struct_0(k1_tex_2('#skF_5', '#skF_6'))=u1_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_1047, c_1196])).
% 4.21/1.73  tff(c_1254, plain, (v1_zfmisc_1(u1_struct_0('#skF_5')) | ~l1_struct_0(k1_tex_2('#skF_5', '#skF_6')) | ~v7_struct_0(k1_tex_2('#skF_5', '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_1200, c_24])).
% 4.21/1.73  tff(c_1296, plain, (v1_zfmisc_1(u1_struct_0('#skF_5')) | ~l1_struct_0(k1_tex_2('#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_1023, c_1254])).
% 4.21/1.73  tff(c_1325, plain, (~l1_struct_0(k1_tex_2('#skF_5', '#skF_6'))), inference(splitLeft, [status(thm)], [c_1296])).
% 4.21/1.73  tff(c_1328, plain, (~l1_pre_topc(k1_tex_2('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_18, c_1325])).
% 4.21/1.73  tff(c_1332, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1053, c_1328])).
% 4.21/1.73  tff(c_1333, plain, (v1_zfmisc_1(u1_struct_0('#skF_5'))), inference(splitRight, [status(thm)], [c_1296])).
% 4.21/1.73  tff(c_1337, plain, (~l1_struct_0('#skF_5') | v7_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_1333, c_22])).
% 4.21/1.73  tff(c_1340, plain, (~l1_struct_0('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_1065, c_1337])).
% 4.21/1.73  tff(c_1358, plain, (~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_18, c_1340])).
% 4.21/1.73  tff(c_1362, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_68, c_1358])).
% 4.21/1.73  tff(c_1363, plain, (v1_xboole_0(u1_struct_0('#skF_5')) | v1_zfmisc_1(u1_struct_0('#skF_5'))), inference(splitRight, [status(thm)], [c_947])).
% 4.21/1.73  tff(c_1365, plain, (v1_zfmisc_1(u1_struct_0('#skF_5'))), inference(splitLeft, [status(thm)], [c_1363])).
% 4.21/1.73  tff(c_1369, plain, (~l1_struct_0('#skF_5') | v7_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_1365, c_22])).
% 4.21/1.73  tff(c_1380, plain, (~l1_struct_0('#skF_5')), inference(splitLeft, [status(thm)], [c_1369])).
% 4.21/1.73  tff(c_1383, plain, (~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_18, c_1380])).
% 4.21/1.73  tff(c_1387, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_68, c_1383])).
% 4.21/1.73  tff(c_1388, plain, (v7_struct_0('#skF_5')), inference(splitRight, [status(thm)], [c_1369])).
% 4.21/1.73  tff(c_1465, plain, (![A_264, B_265]: (m1_pre_topc(k1_tex_2(A_264, B_265), A_264) | ~m1_subset_1(B_265, u1_struct_0(A_264)) | ~l1_pre_topc(A_264) | v2_struct_0(A_264))), inference(cnfTransformation, [status(thm)], [f_147])).
% 4.21/1.73  tff(c_1470, plain, (m1_pre_topc(k1_tex_2('#skF_5', '#skF_6'), '#skF_5') | ~l1_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_66, c_1465])).
% 4.21/1.73  tff(c_1474, plain, (m1_pre_topc(k1_tex_2('#skF_5', '#skF_6'), '#skF_5') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_1470])).
% 4.21/1.73  tff(c_1475, plain, (m1_pre_topc(k1_tex_2('#skF_5', '#skF_6'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_70, c_1474])).
% 4.21/1.73  tff(c_1774, plain, (![B_294, A_295]: (~v1_tex_2(B_294, A_295) | v2_struct_0(B_294) | ~m1_pre_topc(B_294, A_295) | ~l1_pre_topc(A_295) | ~v7_struct_0(A_295) | v2_struct_0(A_295))), inference(cnfTransformation, [status(thm)], [f_102])).
% 4.21/1.73  tff(c_1780, plain, (v2_struct_0(k1_tex_2('#skF_5', '#skF_6')) | ~m1_pre_topc(k1_tex_2('#skF_5', '#skF_6'), '#skF_5') | ~l1_pre_topc('#skF_5') | ~v7_struct_0('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_835, c_1774])).
% 4.21/1.73  tff(c_1784, plain, (v2_struct_0(k1_tex_2('#skF_5', '#skF_6')) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1388, c_68, c_1475, c_1780])).
% 4.21/1.73  tff(c_1786, plain, $false, inference(negUnitSimplification, [status(thm)], [c_70, c_1451, c_1784])).
% 4.21/1.73  tff(c_1788, plain, (~v1_zfmisc_1(u1_struct_0('#skF_5'))), inference(splitRight, [status(thm)], [c_1363])).
% 4.21/1.73  tff(c_1830, plain, (![A_299, B_300]: (v7_struct_0(k1_tex_2(A_299, B_300)) | ~m1_subset_1(B_300, u1_struct_0(A_299)) | ~l1_pre_topc(A_299) | v2_struct_0(A_299))), inference(cnfTransformation, [status(thm)], [f_161])).
% 4.21/1.73  tff(c_1837, plain, (v7_struct_0(k1_tex_2('#skF_5', '#skF_6')) | ~l1_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_66, c_1830])).
% 4.21/1.73  tff(c_1841, plain, (v7_struct_0(k1_tex_2('#skF_5', '#skF_6')) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_1837])).
% 4.21/1.73  tff(c_1842, plain, (v7_struct_0(k1_tex_2('#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_70, c_1841])).
% 4.21/1.73  tff(c_1787, plain, (v1_xboole_0(u1_struct_0('#skF_5'))), inference(splitRight, [status(thm)], [c_1363])).
% 4.21/1.73  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.21/1.73  tff(c_888, plain, (![C_184, B_185, A_186]: (r2_hidden(C_184, B_185) | ~r2_hidden(C_184, A_186) | ~r1_tarski(A_186, B_185))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.21/1.73  tff(c_910, plain, (![A_190, B_191]: (r2_hidden('#skF_1'(A_190), B_191) | ~r1_tarski(A_190, B_191) | v1_xboole_0(A_190))), inference(resolution, [status(thm)], [c_4, c_888])).
% 4.21/1.73  tff(c_917, plain, (![B_191, A_190]: (~v1_xboole_0(B_191) | ~r1_tarski(A_190, B_191) | v1_xboole_0(A_190))), inference(resolution, [status(thm)], [c_910, c_2])).
% 4.21/1.73  tff(c_936, plain, (![A_195, B_194]: (~v1_xboole_0(u1_struct_0(A_195)) | v1_xboole_0(u1_struct_0(B_194)) | ~m1_pre_topc(B_194, A_195) | ~l1_pre_topc(A_195))), inference(resolution, [status(thm)], [c_927, c_917])).
% 4.21/1.73  tff(c_1790, plain, (![B_194]: (v1_xboole_0(u1_struct_0(B_194)) | ~m1_pre_topc(B_194, '#skF_5') | ~l1_pre_topc('#skF_5'))), inference(resolution, [status(thm)], [c_1787, c_936])).
% 4.21/1.73  tff(c_1818, plain, (![B_297]: (v1_xboole_0(u1_struct_0(B_297)) | ~m1_pre_topc(B_297, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_1790])).
% 4.21/1.73  tff(c_877, plain, (![B_180, A_181]: (B_180=A_181 | ~r1_tarski(B_180, A_181) | ~v1_xboole_0(A_181))), inference(resolution, [status(thm)], [c_858, c_867])).
% 4.21/1.73  tff(c_884, plain, (![B_173, A_172]: (B_173=A_172 | ~v1_xboole_0(B_173) | ~v1_xboole_0(A_172))), inference(resolution, [status(thm)], [c_858, c_877])).
% 4.21/1.73  tff(c_1796, plain, (![A_172]: (u1_struct_0('#skF_5')=A_172 | ~v1_xboole_0(A_172))), inference(resolution, [status(thm)], [c_1787, c_884])).
% 4.21/1.73  tff(c_1826, plain, (![B_297]: (u1_struct_0(B_297)=u1_struct_0('#skF_5') | ~m1_pre_topc(B_297, '#skF_5'))), inference(resolution, [status(thm)], [c_1818, c_1796])).
% 4.21/1.73  tff(c_1983, plain, (u1_struct_0(k1_tex_2('#skF_5', '#skF_6'))=u1_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_1958, c_1826])).
% 4.21/1.73  tff(c_2037, plain, (v1_zfmisc_1(u1_struct_0('#skF_5')) | ~l1_struct_0(k1_tex_2('#skF_5', '#skF_6')) | ~v7_struct_0(k1_tex_2('#skF_5', '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_1983, c_24])).
% 4.21/1.73  tff(c_2068, plain, (v1_zfmisc_1(u1_struct_0('#skF_5')) | ~l1_struct_0(k1_tex_2('#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_1842, c_2037])).
% 4.21/1.73  tff(c_2069, plain, (~l1_struct_0(k1_tex_2('#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_1788, c_2068])).
% 4.21/1.73  tff(c_2099, plain, (~l1_pre_topc(k1_tex_2('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_18, c_2069])).
% 4.21/1.73  tff(c_2103, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1986, c_2099])).
% 4.21/1.73  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.21/1.73  
% 4.21/1.73  Inference rules
% 4.21/1.73  ----------------------
% 4.21/1.73  #Ref     : 0
% 4.21/1.73  #Sup     : 406
% 4.21/1.73  #Fact    : 0
% 4.21/1.73  #Define  : 0
% 4.21/1.73  #Split   : 14
% 4.21/1.73  #Chain   : 0
% 4.21/1.73  #Close   : 0
% 4.21/1.73  
% 4.21/1.73  Ordering : KBO
% 4.21/1.73  
% 4.21/1.73  Simplification rules
% 4.21/1.73  ----------------------
% 4.21/1.73  #Subsume      : 74
% 4.21/1.73  #Demod        : 251
% 4.21/1.73  #Tautology    : 72
% 4.21/1.73  #SimpNegUnit  : 61
% 4.21/1.73  #BackRed      : 19
% 4.21/1.73  
% 4.21/1.73  #Partial instantiations: 0
% 4.21/1.73  #Strategies tried      : 1
% 4.21/1.73  
% 4.21/1.73  Timing (in seconds)
% 4.21/1.73  ----------------------
% 4.21/1.73  Preprocessing        : 0.34
% 4.21/1.73  Parsing              : 0.17
% 4.21/1.73  CNF conversion       : 0.03
% 4.21/1.73  Main loop            : 0.61
% 4.21/1.73  Inferencing          : 0.23
% 4.21/1.73  Reduction            : 0.18
% 4.21/1.73  Demodulation         : 0.12
% 4.21/1.73  BG Simplification    : 0.03
% 4.21/1.73  Subsumption          : 0.12
% 4.21/1.73  Abstraction          : 0.03
% 4.21/1.73  MUC search           : 0.00
% 4.21/1.73  Cooper               : 0.00
% 4.21/1.73  Total                : 1.01
% 4.21/1.73  Index Insertion      : 0.00
% 4.21/1.73  Index Deletion       : 0.00
% 4.21/1.73  Index Matching       : 0.00
% 4.21/1.73  BG Taut test         : 0.00
%------------------------------------------------------------------------------
