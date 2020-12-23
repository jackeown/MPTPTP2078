%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:02 EST 2020

% Result     : Theorem 5.69s
% Output     : CNFRefutation 5.78s
% Verified   : 
% Statistics : Number of formulae       :  157 ( 400 expanded)
%              Number of leaves         :   47 ( 148 expanded)
%              Depth                    :   12
%              Number of atoms          :  304 (1040 expanded)
%              Number of equality atoms :   10 (  16 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_tex_2 > v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v7_struct_0 > v2_struct_0 > v1_zfmisc_1 > v1_xboole_0 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k6_enumset1 > k6_domain_1 > k1_tex_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_4 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i > $i )).

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(v7_struct_0,type,(
    v7_struct_0: $i > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

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

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k1_tex_2,type,(
    k1_tex_2: ( $i * $i ) > $i )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_201,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ( v1_tex_2(k1_tex_2(A,B),A)
            <=> v1_subset_1(k6_domain_1(u1_struct_0(A),B),u1_struct_0(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_tex_2)).

tff(f_153,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ( ~ v2_struct_0(k1_tex_2(A,B))
        & v7_struct_0(k1_tex_2(A,B))
        & v1_pre_topc(k1_tex_2(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_tex_2)).

tff(f_64,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_175,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & ~ v1_zfmisc_1(A) )
     => ! [B] :
          ( m1_subset_1(B,A)
         => v1_subset_1(k6_domain_1(A,B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tex_2)).

tff(f_188,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ~ ( v1_subset_1(k6_domain_1(u1_struct_0(A),B),u1_struct_0(A))
              & v7_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_tex_2)).

tff(f_139,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ( ~ v2_struct_0(k1_tex_2(A,B))
        & v1_pre_topc(k1_tex_2(A,B))
        & m1_pre_topc(k1_tex_2(A,B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tex_2)).

tff(f_118,axiom,(
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

tff(f_125,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( v1_subset_1(B,A)
      <=> B != A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).

tff(f_71,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_85,axiom,(
    ! [A] :
      ( ( v7_struct_0(A)
        & l1_struct_0(A) )
     => v1_zfmisc_1(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_struct_0)).

tff(f_79,axiom,(
    ! [A] :
      ( ( ~ v7_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_zfmisc_1(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_struct_0)).

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

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_60,axiom,(
    ! [A] :
      ( v1_zfmisc_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_zfmisc_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_1)).

tff(f_43,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_164,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ? [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
          & ~ v1_xboole_0(B)
          & v1_zfmisc_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_tex_2)).

tff(f_41,axiom,(
    ! [A,B,C,D,E,F,G,H] : ~ v1_xboole_0(k6_enumset1(A,B,C,D,E,F,G,H)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_subset_1)).

tff(f_104,axiom,(
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

tff(c_74,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_72,plain,(
    l1_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_70,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_4430,plain,(
    ! [A_526,B_527] :
      ( ~ v2_struct_0(k1_tex_2(A_526,B_527))
      | ~ m1_subset_1(B_527,u1_struct_0(A_526))
      | ~ l1_pre_topc(A_526)
      | v2_struct_0(A_526) ) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_4445,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_5','#skF_6'))
    | ~ l1_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_70,c_4430])).

tff(c_4451,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_5','#skF_6'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_4445])).

tff(c_4452,plain,(
    ~ v2_struct_0(k1_tex_2('#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_4451])).

tff(c_24,plain,(
    ! [A_27] :
      ( l1_struct_0(A_27)
      | ~ l1_pre_topc(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_3959,plain,(
    ! [A_479,B_480] :
      ( ~ v2_struct_0(k1_tex_2(A_479,B_480))
      | ~ m1_subset_1(B_480,u1_struct_0(A_479))
      | ~ l1_pre_topc(A_479)
      | v2_struct_0(A_479) ) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_3974,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_5','#skF_6'))
    | ~ l1_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_70,c_3959])).

tff(c_3980,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_5','#skF_6'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_3974])).

tff(c_3981,plain,(
    ~ v2_struct_0(k1_tex_2('#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_3980])).

tff(c_3752,plain,(
    ! [A_459,B_460] :
      ( v1_subset_1(k6_domain_1(A_459,B_460),A_459)
      | ~ m1_subset_1(B_460,A_459)
      | v1_zfmisc_1(A_459)
      | v1_xboole_0(A_459) ) ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_76,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0('#skF_5'),'#skF_6'),u1_struct_0('#skF_5'))
    | ~ v1_tex_2(k1_tex_2('#skF_5','#skF_6'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_93,plain,(
    ~ v1_tex_2(k1_tex_2('#skF_5','#skF_6'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_76])).

tff(c_82,plain,
    ( v1_tex_2(k1_tex_2('#skF_5','#skF_6'),'#skF_5')
    | v1_subset_1(k6_domain_1(u1_struct_0('#skF_5'),'#skF_6'),u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_123,plain,(
    v1_subset_1(k6_domain_1(u1_struct_0('#skF_5'),'#skF_6'),u1_struct_0('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_93,c_82])).

tff(c_1343,plain,(
    ! [A_226,B_227] :
      ( ~ v7_struct_0(A_226)
      | ~ v1_subset_1(k6_domain_1(u1_struct_0(A_226),B_227),u1_struct_0(A_226))
      | ~ m1_subset_1(B_227,u1_struct_0(A_226))
      | ~ l1_struct_0(A_226)
      | v2_struct_0(A_226) ) ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_1359,plain,
    ( ~ v7_struct_0('#skF_5')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_123,c_1343])).

tff(c_1370,plain,
    ( ~ v7_struct_0('#skF_5')
    | ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_1359])).

tff(c_1371,plain,
    ( ~ v7_struct_0('#skF_5')
    | ~ l1_struct_0('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_1370])).

tff(c_1372,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_1371])).

tff(c_1375,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_24,c_1372])).

tff(c_1379,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_1375])).

tff(c_1380,plain,(
    ~ v7_struct_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_1371])).

tff(c_1381,plain,(
    l1_struct_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_1371])).

tff(c_535,plain,(
    ! [A_159,B_160] :
      ( m1_pre_topc(k1_tex_2(A_159,B_160),A_159)
      | ~ m1_subset_1(B_160,u1_struct_0(A_159))
      | ~ l1_pre_topc(A_159)
      | v2_struct_0(A_159) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_546,plain,
    ( m1_pre_topc(k1_tex_2('#skF_5','#skF_6'),'#skF_5')
    | ~ l1_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_70,c_535])).

tff(c_552,plain,
    ( m1_pre_topc(k1_tex_2('#skF_5','#skF_6'),'#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_546])).

tff(c_553,plain,(
    m1_pre_topc(k1_tex_2('#skF_5','#skF_6'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_552])).

tff(c_1264,plain,(
    ! [A_218,B_219] :
      ( m1_subset_1('#skF_3'(A_218,B_219),k1_zfmisc_1(u1_struct_0(A_218)))
      | v1_tex_2(B_219,A_218)
      | ~ m1_pre_topc(B_219,A_218)
      | ~ l1_pre_topc(A_218) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_44,plain,(
    ! [B_47,A_46] :
      ( v1_subset_1(B_47,A_46)
      | B_47 = A_46
      | ~ m1_subset_1(B_47,k1_zfmisc_1(A_46)) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_2973,plain,(
    ! [A_327,B_328] :
      ( v1_subset_1('#skF_3'(A_327,B_328),u1_struct_0(A_327))
      | u1_struct_0(A_327) = '#skF_3'(A_327,B_328)
      | v1_tex_2(B_328,A_327)
      | ~ m1_pre_topc(B_328,A_327)
      | ~ l1_pre_topc(A_327) ) ),
    inference(resolution,[status(thm)],[c_1264,c_44])).

tff(c_38,plain,(
    ! [A_36,B_42] :
      ( ~ v1_subset_1('#skF_3'(A_36,B_42),u1_struct_0(A_36))
      | v1_tex_2(B_42,A_36)
      | ~ m1_pre_topc(B_42,A_36)
      | ~ l1_pre_topc(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_2988,plain,(
    ! [A_329,B_330] :
      ( u1_struct_0(A_329) = '#skF_3'(A_329,B_330)
      | v1_tex_2(B_330,A_329)
      | ~ m1_pre_topc(B_330,A_329)
      | ~ l1_pre_topc(A_329) ) ),
    inference(resolution,[status(thm)],[c_2973,c_38])).

tff(c_2998,plain,
    ( '#skF_3'('#skF_5',k1_tex_2('#skF_5','#skF_6')) = u1_struct_0('#skF_5')
    | ~ m1_pre_topc(k1_tex_2('#skF_5','#skF_6'),'#skF_5')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_2988,c_93])).

tff(c_3003,plain,(
    '#skF_3'('#skF_5',k1_tex_2('#skF_5','#skF_6')) = u1_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_553,c_2998])).

tff(c_26,plain,(
    ! [B_30,A_28] :
      ( l1_pre_topc(B_30)
      | ~ m1_pre_topc(B_30,A_28)
      | ~ l1_pre_topc(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_556,plain,
    ( l1_pre_topc(k1_tex_2('#skF_5','#skF_6'))
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_553,c_26])).

tff(c_559,plain,(
    l1_pre_topc(k1_tex_2('#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_556])).

tff(c_414,plain,(
    ! [A_146,B_147] :
      ( v7_struct_0(k1_tex_2(A_146,B_147))
      | ~ m1_subset_1(B_147,u1_struct_0(A_146))
      | ~ l1_pre_topc(A_146)
      | v2_struct_0(A_146) ) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_425,plain,
    ( v7_struct_0(k1_tex_2('#skF_5','#skF_6'))
    | ~ l1_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_70,c_414])).

tff(c_430,plain,
    ( v7_struct_0(k1_tex_2('#skF_5','#skF_6'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_425])).

tff(c_431,plain,(
    v7_struct_0(k1_tex_2('#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_430])).

tff(c_605,plain,(
    ! [B_167,A_168] :
      ( u1_struct_0(B_167) = '#skF_3'(A_168,B_167)
      | v1_tex_2(B_167,A_168)
      | ~ m1_pre_topc(B_167,A_168)
      | ~ l1_pre_topc(A_168) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_608,plain,
    ( u1_struct_0(k1_tex_2('#skF_5','#skF_6')) = '#skF_3'('#skF_5',k1_tex_2('#skF_5','#skF_6'))
    | ~ m1_pre_topc(k1_tex_2('#skF_5','#skF_6'),'#skF_5')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_605,c_93])).

tff(c_611,plain,(
    u1_struct_0(k1_tex_2('#skF_5','#skF_6')) = '#skF_3'('#skF_5',k1_tex_2('#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_553,c_608])).

tff(c_30,plain,(
    ! [A_32] :
      ( v1_zfmisc_1(u1_struct_0(A_32))
      | ~ l1_struct_0(A_32)
      | ~ v7_struct_0(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_632,plain,
    ( v1_zfmisc_1('#skF_3'('#skF_5',k1_tex_2('#skF_5','#skF_6')))
    | ~ l1_struct_0(k1_tex_2('#skF_5','#skF_6'))
    | ~ v7_struct_0(k1_tex_2('#skF_5','#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_611,c_30])).

tff(c_650,plain,
    ( v1_zfmisc_1('#skF_3'('#skF_5',k1_tex_2('#skF_5','#skF_6')))
    | ~ l1_struct_0(k1_tex_2('#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_431,c_632])).

tff(c_652,plain,(
    ~ l1_struct_0(k1_tex_2('#skF_5','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_650])).

tff(c_655,plain,(
    ~ l1_pre_topc(k1_tex_2('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_24,c_652])).

tff(c_659,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_559,c_655])).

tff(c_660,plain,(
    v1_zfmisc_1('#skF_3'('#skF_5',k1_tex_2('#skF_5','#skF_6'))) ),
    inference(splitRight,[status(thm)],[c_650])).

tff(c_3012,plain,(
    v1_zfmisc_1(u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3003,c_660])).

tff(c_28,plain,(
    ! [A_31] :
      ( ~ v1_zfmisc_1(u1_struct_0(A_31))
      | ~ l1_struct_0(A_31)
      | v7_struct_0(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_3053,plain,
    ( ~ l1_struct_0('#skF_5')
    | v7_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_3012,c_28])).

tff(c_3059,plain,(
    v7_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1381,c_3053])).

tff(c_3061,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1380,c_3059])).

tff(c_3062,plain,(
    ~ v1_subset_1(k6_domain_1(u1_struct_0('#skF_5'),'#skF_6'),u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_3755,plain,
    ( ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | v1_zfmisc_1(u1_struct_0('#skF_5'))
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_3752,c_3062])).

tff(c_3758,plain,
    ( v1_zfmisc_1(u1_struct_0('#skF_5'))
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_3755])).

tff(c_3759,plain,(
    v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_3758])).

tff(c_3212,plain,(
    ! [A_372,B_373] :
      ( r2_hidden('#skF_2'(A_372,B_373),A_372)
      | r1_tarski(A_372,B_373) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_3217,plain,(
    ! [A_374,B_375] :
      ( ~ v1_xboole_0(A_374)
      | r1_tarski(A_374,B_375) ) ),
    inference(resolution,[status(thm)],[c_3212,c_2])).

tff(c_18,plain,(
    ! [A_19,B_20] :
      ( m1_subset_1(A_19,k1_zfmisc_1(B_20))
      | ~ r1_tarski(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_3134,plain,(
    ! [B_354,A_355] :
      ( v1_zfmisc_1(B_354)
      | ~ m1_subset_1(B_354,k1_zfmisc_1(A_355))
      | ~ v1_zfmisc_1(A_355) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_3144,plain,(
    ! [A_19,B_20] :
      ( v1_zfmisc_1(A_19)
      | ~ v1_zfmisc_1(B_20)
      | ~ r1_tarski(A_19,B_20) ) ),
    inference(resolution,[status(thm)],[c_18,c_3134])).

tff(c_3221,plain,(
    ! [A_374,B_375] :
      ( v1_zfmisc_1(A_374)
      | ~ v1_zfmisc_1(B_375)
      | ~ v1_xboole_0(A_374) ) ),
    inference(resolution,[status(thm)],[c_3217,c_3144])).

tff(c_3236,plain,(
    ! [B_375] : ~ v1_zfmisc_1(B_375) ),
    inference(splitLeft,[status(thm)],[c_3221])).

tff(c_14,plain,(
    ! [A_18] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_18)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_3146,plain,(
    ! [A_18] :
      ( v1_zfmisc_1(k1_xboole_0)
      | ~ v1_zfmisc_1(A_18) ) ),
    inference(resolution,[status(thm)],[c_14,c_3134])).

tff(c_3147,plain,(
    ! [A_18] : ~ v1_zfmisc_1(A_18) ),
    inference(splitLeft,[status(thm)],[c_3146])).

tff(c_60,plain,(
    ! [A_52] :
      ( v1_zfmisc_1('#skF_4'(A_52))
      | v1_xboole_0(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_3150,plain,(
    ! [A_52] : v1_xboole_0(A_52) ),
    inference(negUnitSimplification,[status(thm)],[c_3147,c_60])).

tff(c_12,plain,(
    ! [H_17,B_11,A_10,C_12,G_16,F_15,E_14,D_13] : ~ v1_xboole_0(k6_enumset1(A_10,B_11,C_12,D_13,E_14,F_15,G_16,H_17)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_3200,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3150,c_12])).

tff(c_3201,plain,(
    v1_zfmisc_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_3146])).

tff(c_3249,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3236,c_3201])).

tff(c_3251,plain,(
    ! [A_383] :
      ( v1_zfmisc_1(A_383)
      | ~ v1_xboole_0(A_383) ) ),
    inference(splitRight,[status(thm)],[c_3221])).

tff(c_3255,plain,(
    ! [A_31] :
      ( ~ l1_struct_0(A_31)
      | v7_struct_0(A_31)
      | ~ v1_xboole_0(u1_struct_0(A_31)) ) ),
    inference(resolution,[status(thm)],[c_3251,c_28])).

tff(c_3763,plain,
    ( ~ l1_struct_0('#skF_5')
    | v7_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_3759,c_3255])).

tff(c_3764,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_3763])).

tff(c_3767,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_24,c_3764])).

tff(c_3771,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_3767])).

tff(c_3772,plain,(
    v7_struct_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_3763])).

tff(c_4104,plain,(
    ! [A_492,B_493] :
      ( m1_pre_topc(k1_tex_2(A_492,B_493),A_492)
      | ~ m1_subset_1(B_493,u1_struct_0(A_492))
      | ~ l1_pre_topc(A_492)
      | v2_struct_0(A_492) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_4121,plain,
    ( m1_pre_topc(k1_tex_2('#skF_5','#skF_6'),'#skF_5')
    | ~ l1_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_70,c_4104])).

tff(c_4129,plain,
    ( m1_pre_topc(k1_tex_2('#skF_5','#skF_6'),'#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_4121])).

tff(c_4130,plain,(
    m1_pre_topc(k1_tex_2('#skF_5','#skF_6'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_4129])).

tff(c_3063,plain,(
    v1_tex_2(k1_tex_2('#skF_5','#skF_6'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_4216,plain,(
    ! [B_506,A_507] :
      ( ~ v1_tex_2(B_506,A_507)
      | v2_struct_0(B_506)
      | ~ m1_pre_topc(B_506,A_507)
      | ~ l1_pre_topc(A_507)
      | ~ v7_struct_0(A_507)
      | v2_struct_0(A_507) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_4222,plain,
    ( v2_struct_0(k1_tex_2('#skF_5','#skF_6'))
    | ~ m1_pre_topc(k1_tex_2('#skF_5','#skF_6'),'#skF_5')
    | ~ l1_pre_topc('#skF_5')
    | ~ v7_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_3063,c_4216])).

tff(c_4226,plain,
    ( v2_struct_0(k1_tex_2('#skF_5','#skF_6'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3772,c_72,c_4130,c_4222])).

tff(c_4228,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_3981,c_4226])).

tff(c_4229,plain,(
    v1_zfmisc_1(u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_3758])).

tff(c_4234,plain,
    ( ~ l1_struct_0('#skF_5')
    | v7_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_4229,c_28])).

tff(c_4235,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_4234])).

tff(c_4238,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_24,c_4235])).

tff(c_4242,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_4238])).

tff(c_4243,plain,(
    v7_struct_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_4234])).

tff(c_4575,plain,(
    ! [A_539,B_540] :
      ( m1_pre_topc(k1_tex_2(A_539,B_540),A_539)
      | ~ m1_subset_1(B_540,u1_struct_0(A_539))
      | ~ l1_pre_topc(A_539)
      | v2_struct_0(A_539) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_4592,plain,
    ( m1_pre_topc(k1_tex_2('#skF_5','#skF_6'),'#skF_5')
    | ~ l1_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_70,c_4575])).

tff(c_4600,plain,
    ( m1_pre_topc(k1_tex_2('#skF_5','#skF_6'),'#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_4592])).

tff(c_4601,plain,(
    m1_pre_topc(k1_tex_2('#skF_5','#skF_6'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_4600])).

tff(c_4687,plain,(
    ! [B_553,A_554] :
      ( ~ v1_tex_2(B_553,A_554)
      | v2_struct_0(B_553)
      | ~ m1_pre_topc(B_553,A_554)
      | ~ l1_pre_topc(A_554)
      | ~ v7_struct_0(A_554)
      | v2_struct_0(A_554) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_4693,plain,
    ( v2_struct_0(k1_tex_2('#skF_5','#skF_6'))
    | ~ m1_pre_topc(k1_tex_2('#skF_5','#skF_6'),'#skF_5')
    | ~ l1_pre_topc('#skF_5')
    | ~ v7_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_3063,c_4687])).

tff(c_4697,plain,
    ( v2_struct_0(k1_tex_2('#skF_5','#skF_6'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4243,c_72,c_4601,c_4693])).

tff(c_4699,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_4452,c_4697])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:01:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.69/2.06  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.69/2.08  
% 5.69/2.08  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.69/2.08  %$ v1_tex_2 > v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v7_struct_0 > v2_struct_0 > v1_zfmisc_1 > v1_xboole_0 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k6_enumset1 > k6_domain_1 > k1_tex_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_4 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2
% 5.69/2.08  
% 5.69/2.08  %Foreground sorts:
% 5.69/2.08  
% 5.69/2.08  
% 5.69/2.08  %Background operators:
% 5.69/2.08  
% 5.69/2.08  
% 5.69/2.08  %Foreground operators:
% 5.69/2.08  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 5.69/2.08  tff('#skF_4', type, '#skF_4': $i > $i).
% 5.69/2.08  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.69/2.08  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.69/2.08  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 5.69/2.08  tff('#skF_1', type, '#skF_1': $i > $i).
% 5.69/2.08  tff(v1_tex_2, type, v1_tex_2: ($i * $i) > $o).
% 5.69/2.08  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.69/2.08  tff(v7_struct_0, type, v7_struct_0: $i > $o).
% 5.69/2.08  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 5.69/2.08  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 5.69/2.08  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 5.69/2.08  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.69/2.08  tff('#skF_5', type, '#skF_5': $i).
% 5.69/2.08  tff('#skF_6', type, '#skF_6': $i).
% 5.69/2.08  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 5.69/2.08  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.69/2.08  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 5.69/2.08  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 5.69/2.08  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.69/2.08  tff(k1_tex_2, type, k1_tex_2: ($i * $i) > $i).
% 5.69/2.08  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.69/2.08  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 5.69/2.08  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 5.69/2.08  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 5.69/2.08  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.69/2.08  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.69/2.08  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.69/2.08  
% 5.78/2.10  tff(f_201, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (v1_tex_2(k1_tex_2(A, B), A) <=> v1_subset_1(k6_domain_1(u1_struct_0(A), B), u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_tex_2)).
% 5.78/2.10  tff(f_153, axiom, (![A, B]: (((~v2_struct_0(A) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => ((~v2_struct_0(k1_tex_2(A, B)) & v7_struct_0(k1_tex_2(A, B))) & v1_pre_topc(k1_tex_2(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_tex_2)).
% 5.78/2.10  tff(f_64, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 5.78/2.10  tff(f_175, axiom, (![A]: ((~v1_xboole_0(A) & ~v1_zfmisc_1(A)) => (![B]: (m1_subset_1(B, A) => v1_subset_1(k6_domain_1(A, B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_tex_2)).
% 5.78/2.10  tff(f_188, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => ~(v1_subset_1(k6_domain_1(u1_struct_0(A), B), u1_struct_0(A)) & v7_struct_0(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_tex_2)).
% 5.78/2.10  tff(f_139, axiom, (![A, B]: (((~v2_struct_0(A) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => ((~v2_struct_0(k1_tex_2(A, B)) & v1_pre_topc(k1_tex_2(A, B))) & m1_pre_topc(k1_tex_2(A, B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_tex_2)).
% 5.78/2.10  tff(f_118, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (v1_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => v1_subset_1(C, u1_struct_0(A)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tex_2)).
% 5.78/2.10  tff(f_125, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (v1_subset_1(B, A) <=> ~(B = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_subset_1)).
% 5.78/2.10  tff(f_71, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 5.78/2.10  tff(f_85, axiom, (![A]: ((v7_struct_0(A) & l1_struct_0(A)) => v1_zfmisc_1(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc7_struct_0)).
% 5.78/2.10  tff(f_79, axiom, (![A]: ((~v7_struct_0(A) & l1_struct_0(A)) => ~v1_zfmisc_1(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_struct_0)).
% 5.78/2.10  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 5.78/2.10  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 5.78/2.10  tff(f_47, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 5.78/2.10  tff(f_60, axiom, (![A]: (v1_zfmisc_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_zfmisc_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc5_funct_1)).
% 5.78/2.10  tff(f_43, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 5.78/2.10  tff(f_164, axiom, (![A]: (~v1_xboole_0(A) => (?[B]: ((m1_subset_1(B, k1_zfmisc_1(A)) & ~v1_xboole_0(B)) & v1_zfmisc_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc1_tex_2)).
% 5.78/2.10  tff(f_41, axiom, (![A, B, C, D, E, F, G, H]: ~v1_xboole_0(k6_enumset1(A, B, C, D, E, F, G, H))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc7_subset_1)).
% 5.78/2.10  tff(f_104, axiom, (![A]: (((~v2_struct_0(A) & v7_struct_0(A)) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (~v2_struct_0(B) => (~v2_struct_0(B) & ~v1_tex_2(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc10_tex_2)).
% 5.78/2.10  tff(c_74, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_201])).
% 5.78/2.10  tff(c_72, plain, (l1_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_201])).
% 5.78/2.10  tff(c_70, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_201])).
% 5.78/2.10  tff(c_4430, plain, (![A_526, B_527]: (~v2_struct_0(k1_tex_2(A_526, B_527)) | ~m1_subset_1(B_527, u1_struct_0(A_526)) | ~l1_pre_topc(A_526) | v2_struct_0(A_526))), inference(cnfTransformation, [status(thm)], [f_153])).
% 5.78/2.10  tff(c_4445, plain, (~v2_struct_0(k1_tex_2('#skF_5', '#skF_6')) | ~l1_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_70, c_4430])).
% 5.78/2.10  tff(c_4451, plain, (~v2_struct_0(k1_tex_2('#skF_5', '#skF_6')) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_4445])).
% 5.78/2.10  tff(c_4452, plain, (~v2_struct_0(k1_tex_2('#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_74, c_4451])).
% 5.78/2.10  tff(c_24, plain, (![A_27]: (l1_struct_0(A_27) | ~l1_pre_topc(A_27))), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.78/2.10  tff(c_3959, plain, (![A_479, B_480]: (~v2_struct_0(k1_tex_2(A_479, B_480)) | ~m1_subset_1(B_480, u1_struct_0(A_479)) | ~l1_pre_topc(A_479) | v2_struct_0(A_479))), inference(cnfTransformation, [status(thm)], [f_153])).
% 5.78/2.10  tff(c_3974, plain, (~v2_struct_0(k1_tex_2('#skF_5', '#skF_6')) | ~l1_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_70, c_3959])).
% 5.78/2.10  tff(c_3980, plain, (~v2_struct_0(k1_tex_2('#skF_5', '#skF_6')) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_3974])).
% 5.78/2.10  tff(c_3981, plain, (~v2_struct_0(k1_tex_2('#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_74, c_3980])).
% 5.78/2.10  tff(c_3752, plain, (![A_459, B_460]: (v1_subset_1(k6_domain_1(A_459, B_460), A_459) | ~m1_subset_1(B_460, A_459) | v1_zfmisc_1(A_459) | v1_xboole_0(A_459))), inference(cnfTransformation, [status(thm)], [f_175])).
% 5.78/2.10  tff(c_76, plain, (~v1_subset_1(k6_domain_1(u1_struct_0('#skF_5'), '#skF_6'), u1_struct_0('#skF_5')) | ~v1_tex_2(k1_tex_2('#skF_5', '#skF_6'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_201])).
% 5.78/2.10  tff(c_93, plain, (~v1_tex_2(k1_tex_2('#skF_5', '#skF_6'), '#skF_5')), inference(splitLeft, [status(thm)], [c_76])).
% 5.78/2.10  tff(c_82, plain, (v1_tex_2(k1_tex_2('#skF_5', '#skF_6'), '#skF_5') | v1_subset_1(k6_domain_1(u1_struct_0('#skF_5'), '#skF_6'), u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_201])).
% 5.78/2.10  tff(c_123, plain, (v1_subset_1(k6_domain_1(u1_struct_0('#skF_5'), '#skF_6'), u1_struct_0('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_93, c_82])).
% 5.78/2.10  tff(c_1343, plain, (![A_226, B_227]: (~v7_struct_0(A_226) | ~v1_subset_1(k6_domain_1(u1_struct_0(A_226), B_227), u1_struct_0(A_226)) | ~m1_subset_1(B_227, u1_struct_0(A_226)) | ~l1_struct_0(A_226) | v2_struct_0(A_226))), inference(cnfTransformation, [status(thm)], [f_188])).
% 5.78/2.10  tff(c_1359, plain, (~v7_struct_0('#skF_5') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~l1_struct_0('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_123, c_1343])).
% 5.78/2.10  tff(c_1370, plain, (~v7_struct_0('#skF_5') | ~l1_struct_0('#skF_5') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_1359])).
% 5.78/2.10  tff(c_1371, plain, (~v7_struct_0('#skF_5') | ~l1_struct_0('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_74, c_1370])).
% 5.78/2.10  tff(c_1372, plain, (~l1_struct_0('#skF_5')), inference(splitLeft, [status(thm)], [c_1371])).
% 5.78/2.10  tff(c_1375, plain, (~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_24, c_1372])).
% 5.78/2.10  tff(c_1379, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_72, c_1375])).
% 5.78/2.10  tff(c_1380, plain, (~v7_struct_0('#skF_5')), inference(splitRight, [status(thm)], [c_1371])).
% 5.78/2.10  tff(c_1381, plain, (l1_struct_0('#skF_5')), inference(splitRight, [status(thm)], [c_1371])).
% 5.78/2.10  tff(c_535, plain, (![A_159, B_160]: (m1_pre_topc(k1_tex_2(A_159, B_160), A_159) | ~m1_subset_1(B_160, u1_struct_0(A_159)) | ~l1_pre_topc(A_159) | v2_struct_0(A_159))), inference(cnfTransformation, [status(thm)], [f_139])).
% 5.78/2.10  tff(c_546, plain, (m1_pre_topc(k1_tex_2('#skF_5', '#skF_6'), '#skF_5') | ~l1_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_70, c_535])).
% 5.78/2.10  tff(c_552, plain, (m1_pre_topc(k1_tex_2('#skF_5', '#skF_6'), '#skF_5') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_546])).
% 5.78/2.10  tff(c_553, plain, (m1_pre_topc(k1_tex_2('#skF_5', '#skF_6'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_74, c_552])).
% 5.78/2.10  tff(c_1264, plain, (![A_218, B_219]: (m1_subset_1('#skF_3'(A_218, B_219), k1_zfmisc_1(u1_struct_0(A_218))) | v1_tex_2(B_219, A_218) | ~m1_pre_topc(B_219, A_218) | ~l1_pre_topc(A_218))), inference(cnfTransformation, [status(thm)], [f_118])).
% 5.78/2.10  tff(c_44, plain, (![B_47, A_46]: (v1_subset_1(B_47, A_46) | B_47=A_46 | ~m1_subset_1(B_47, k1_zfmisc_1(A_46)))), inference(cnfTransformation, [status(thm)], [f_125])).
% 5.78/2.10  tff(c_2973, plain, (![A_327, B_328]: (v1_subset_1('#skF_3'(A_327, B_328), u1_struct_0(A_327)) | u1_struct_0(A_327)='#skF_3'(A_327, B_328) | v1_tex_2(B_328, A_327) | ~m1_pre_topc(B_328, A_327) | ~l1_pre_topc(A_327))), inference(resolution, [status(thm)], [c_1264, c_44])).
% 5.78/2.10  tff(c_38, plain, (![A_36, B_42]: (~v1_subset_1('#skF_3'(A_36, B_42), u1_struct_0(A_36)) | v1_tex_2(B_42, A_36) | ~m1_pre_topc(B_42, A_36) | ~l1_pre_topc(A_36))), inference(cnfTransformation, [status(thm)], [f_118])).
% 5.78/2.10  tff(c_2988, plain, (![A_329, B_330]: (u1_struct_0(A_329)='#skF_3'(A_329, B_330) | v1_tex_2(B_330, A_329) | ~m1_pre_topc(B_330, A_329) | ~l1_pre_topc(A_329))), inference(resolution, [status(thm)], [c_2973, c_38])).
% 5.78/2.10  tff(c_2998, plain, ('#skF_3'('#skF_5', k1_tex_2('#skF_5', '#skF_6'))=u1_struct_0('#skF_5') | ~m1_pre_topc(k1_tex_2('#skF_5', '#skF_6'), '#skF_5') | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_2988, c_93])).
% 5.78/2.10  tff(c_3003, plain, ('#skF_3'('#skF_5', k1_tex_2('#skF_5', '#skF_6'))=u1_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_553, c_2998])).
% 5.78/2.10  tff(c_26, plain, (![B_30, A_28]: (l1_pre_topc(B_30) | ~m1_pre_topc(B_30, A_28) | ~l1_pre_topc(A_28))), inference(cnfTransformation, [status(thm)], [f_71])).
% 5.78/2.10  tff(c_556, plain, (l1_pre_topc(k1_tex_2('#skF_5', '#skF_6')) | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_553, c_26])).
% 5.78/2.10  tff(c_559, plain, (l1_pre_topc(k1_tex_2('#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_556])).
% 5.78/2.10  tff(c_414, plain, (![A_146, B_147]: (v7_struct_0(k1_tex_2(A_146, B_147)) | ~m1_subset_1(B_147, u1_struct_0(A_146)) | ~l1_pre_topc(A_146) | v2_struct_0(A_146))), inference(cnfTransformation, [status(thm)], [f_153])).
% 5.78/2.10  tff(c_425, plain, (v7_struct_0(k1_tex_2('#skF_5', '#skF_6')) | ~l1_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_70, c_414])).
% 5.78/2.10  tff(c_430, plain, (v7_struct_0(k1_tex_2('#skF_5', '#skF_6')) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_425])).
% 5.78/2.10  tff(c_431, plain, (v7_struct_0(k1_tex_2('#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_74, c_430])).
% 5.78/2.10  tff(c_605, plain, (![B_167, A_168]: (u1_struct_0(B_167)='#skF_3'(A_168, B_167) | v1_tex_2(B_167, A_168) | ~m1_pre_topc(B_167, A_168) | ~l1_pre_topc(A_168))), inference(cnfTransformation, [status(thm)], [f_118])).
% 5.78/2.10  tff(c_608, plain, (u1_struct_0(k1_tex_2('#skF_5', '#skF_6'))='#skF_3'('#skF_5', k1_tex_2('#skF_5', '#skF_6')) | ~m1_pre_topc(k1_tex_2('#skF_5', '#skF_6'), '#skF_5') | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_605, c_93])).
% 5.78/2.10  tff(c_611, plain, (u1_struct_0(k1_tex_2('#skF_5', '#skF_6'))='#skF_3'('#skF_5', k1_tex_2('#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_553, c_608])).
% 5.78/2.10  tff(c_30, plain, (![A_32]: (v1_zfmisc_1(u1_struct_0(A_32)) | ~l1_struct_0(A_32) | ~v7_struct_0(A_32))), inference(cnfTransformation, [status(thm)], [f_85])).
% 5.78/2.10  tff(c_632, plain, (v1_zfmisc_1('#skF_3'('#skF_5', k1_tex_2('#skF_5', '#skF_6'))) | ~l1_struct_0(k1_tex_2('#skF_5', '#skF_6')) | ~v7_struct_0(k1_tex_2('#skF_5', '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_611, c_30])).
% 5.78/2.10  tff(c_650, plain, (v1_zfmisc_1('#skF_3'('#skF_5', k1_tex_2('#skF_5', '#skF_6'))) | ~l1_struct_0(k1_tex_2('#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_431, c_632])).
% 5.78/2.10  tff(c_652, plain, (~l1_struct_0(k1_tex_2('#skF_5', '#skF_6'))), inference(splitLeft, [status(thm)], [c_650])).
% 5.78/2.10  tff(c_655, plain, (~l1_pre_topc(k1_tex_2('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_24, c_652])).
% 5.78/2.10  tff(c_659, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_559, c_655])).
% 5.78/2.10  tff(c_660, plain, (v1_zfmisc_1('#skF_3'('#skF_5', k1_tex_2('#skF_5', '#skF_6')))), inference(splitRight, [status(thm)], [c_650])).
% 5.78/2.10  tff(c_3012, plain, (v1_zfmisc_1(u1_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_3003, c_660])).
% 5.78/2.10  tff(c_28, plain, (![A_31]: (~v1_zfmisc_1(u1_struct_0(A_31)) | ~l1_struct_0(A_31) | v7_struct_0(A_31))), inference(cnfTransformation, [status(thm)], [f_79])).
% 5.78/2.10  tff(c_3053, plain, (~l1_struct_0('#skF_5') | v7_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_3012, c_28])).
% 5.78/2.10  tff(c_3059, plain, (v7_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1381, c_3053])).
% 5.78/2.10  tff(c_3061, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1380, c_3059])).
% 5.78/2.10  tff(c_3062, plain, (~v1_subset_1(k6_domain_1(u1_struct_0('#skF_5'), '#skF_6'), u1_struct_0('#skF_5'))), inference(splitRight, [status(thm)], [c_76])).
% 5.78/2.10  tff(c_3755, plain, (~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | v1_zfmisc_1(u1_struct_0('#skF_5')) | v1_xboole_0(u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_3752, c_3062])).
% 5.78/2.10  tff(c_3758, plain, (v1_zfmisc_1(u1_struct_0('#skF_5')) | v1_xboole_0(u1_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_3755])).
% 5.78/2.10  tff(c_3759, plain, (v1_xboole_0(u1_struct_0('#skF_5'))), inference(splitLeft, [status(thm)], [c_3758])).
% 5.78/2.10  tff(c_3212, plain, (![A_372, B_373]: (r2_hidden('#skF_2'(A_372, B_373), A_372) | r1_tarski(A_372, B_373))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.78/2.10  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.78/2.10  tff(c_3217, plain, (![A_374, B_375]: (~v1_xboole_0(A_374) | r1_tarski(A_374, B_375))), inference(resolution, [status(thm)], [c_3212, c_2])).
% 5.78/2.10  tff(c_18, plain, (![A_19, B_20]: (m1_subset_1(A_19, k1_zfmisc_1(B_20)) | ~r1_tarski(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.78/2.10  tff(c_3134, plain, (![B_354, A_355]: (v1_zfmisc_1(B_354) | ~m1_subset_1(B_354, k1_zfmisc_1(A_355)) | ~v1_zfmisc_1(A_355))), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.78/2.10  tff(c_3144, plain, (![A_19, B_20]: (v1_zfmisc_1(A_19) | ~v1_zfmisc_1(B_20) | ~r1_tarski(A_19, B_20))), inference(resolution, [status(thm)], [c_18, c_3134])).
% 5.78/2.10  tff(c_3221, plain, (![A_374, B_375]: (v1_zfmisc_1(A_374) | ~v1_zfmisc_1(B_375) | ~v1_xboole_0(A_374))), inference(resolution, [status(thm)], [c_3217, c_3144])).
% 5.78/2.10  tff(c_3236, plain, (![B_375]: (~v1_zfmisc_1(B_375))), inference(splitLeft, [status(thm)], [c_3221])).
% 5.78/2.10  tff(c_14, plain, (![A_18]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_18)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.78/2.10  tff(c_3146, plain, (![A_18]: (v1_zfmisc_1(k1_xboole_0) | ~v1_zfmisc_1(A_18))), inference(resolution, [status(thm)], [c_14, c_3134])).
% 5.78/2.10  tff(c_3147, plain, (![A_18]: (~v1_zfmisc_1(A_18))), inference(splitLeft, [status(thm)], [c_3146])).
% 5.78/2.10  tff(c_60, plain, (![A_52]: (v1_zfmisc_1('#skF_4'(A_52)) | v1_xboole_0(A_52))), inference(cnfTransformation, [status(thm)], [f_164])).
% 5.78/2.10  tff(c_3150, plain, (![A_52]: (v1_xboole_0(A_52))), inference(negUnitSimplification, [status(thm)], [c_3147, c_60])).
% 5.78/2.10  tff(c_12, plain, (![H_17, B_11, A_10, C_12, G_16, F_15, E_14, D_13]: (~v1_xboole_0(k6_enumset1(A_10, B_11, C_12, D_13, E_14, F_15, G_16, H_17)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.78/2.10  tff(c_3200, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3150, c_12])).
% 5.78/2.10  tff(c_3201, plain, (v1_zfmisc_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_3146])).
% 5.78/2.10  tff(c_3249, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3236, c_3201])).
% 5.78/2.10  tff(c_3251, plain, (![A_383]: (v1_zfmisc_1(A_383) | ~v1_xboole_0(A_383))), inference(splitRight, [status(thm)], [c_3221])).
% 5.78/2.10  tff(c_3255, plain, (![A_31]: (~l1_struct_0(A_31) | v7_struct_0(A_31) | ~v1_xboole_0(u1_struct_0(A_31)))), inference(resolution, [status(thm)], [c_3251, c_28])).
% 5.78/2.10  tff(c_3763, plain, (~l1_struct_0('#skF_5') | v7_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_3759, c_3255])).
% 5.78/2.10  tff(c_3764, plain, (~l1_struct_0('#skF_5')), inference(splitLeft, [status(thm)], [c_3763])).
% 5.78/2.10  tff(c_3767, plain, (~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_24, c_3764])).
% 5.78/2.10  tff(c_3771, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_72, c_3767])).
% 5.78/2.10  tff(c_3772, plain, (v7_struct_0('#skF_5')), inference(splitRight, [status(thm)], [c_3763])).
% 5.78/2.10  tff(c_4104, plain, (![A_492, B_493]: (m1_pre_topc(k1_tex_2(A_492, B_493), A_492) | ~m1_subset_1(B_493, u1_struct_0(A_492)) | ~l1_pre_topc(A_492) | v2_struct_0(A_492))), inference(cnfTransformation, [status(thm)], [f_139])).
% 5.78/2.10  tff(c_4121, plain, (m1_pre_topc(k1_tex_2('#skF_5', '#skF_6'), '#skF_5') | ~l1_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_70, c_4104])).
% 5.78/2.10  tff(c_4129, plain, (m1_pre_topc(k1_tex_2('#skF_5', '#skF_6'), '#skF_5') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_4121])).
% 5.78/2.10  tff(c_4130, plain, (m1_pre_topc(k1_tex_2('#skF_5', '#skF_6'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_74, c_4129])).
% 5.78/2.10  tff(c_3063, plain, (v1_tex_2(k1_tex_2('#skF_5', '#skF_6'), '#skF_5')), inference(splitRight, [status(thm)], [c_76])).
% 5.78/2.10  tff(c_4216, plain, (![B_506, A_507]: (~v1_tex_2(B_506, A_507) | v2_struct_0(B_506) | ~m1_pre_topc(B_506, A_507) | ~l1_pre_topc(A_507) | ~v7_struct_0(A_507) | v2_struct_0(A_507))), inference(cnfTransformation, [status(thm)], [f_104])).
% 5.78/2.10  tff(c_4222, plain, (v2_struct_0(k1_tex_2('#skF_5', '#skF_6')) | ~m1_pre_topc(k1_tex_2('#skF_5', '#skF_6'), '#skF_5') | ~l1_pre_topc('#skF_5') | ~v7_struct_0('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_3063, c_4216])).
% 5.78/2.10  tff(c_4226, plain, (v2_struct_0(k1_tex_2('#skF_5', '#skF_6')) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_3772, c_72, c_4130, c_4222])).
% 5.78/2.10  tff(c_4228, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_3981, c_4226])).
% 5.78/2.10  tff(c_4229, plain, (v1_zfmisc_1(u1_struct_0('#skF_5'))), inference(splitRight, [status(thm)], [c_3758])).
% 5.78/2.10  tff(c_4234, plain, (~l1_struct_0('#skF_5') | v7_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_4229, c_28])).
% 5.78/2.10  tff(c_4235, plain, (~l1_struct_0('#skF_5')), inference(splitLeft, [status(thm)], [c_4234])).
% 5.78/2.10  tff(c_4238, plain, (~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_24, c_4235])).
% 5.78/2.10  tff(c_4242, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_72, c_4238])).
% 5.78/2.10  tff(c_4243, plain, (v7_struct_0('#skF_5')), inference(splitRight, [status(thm)], [c_4234])).
% 5.78/2.10  tff(c_4575, plain, (![A_539, B_540]: (m1_pre_topc(k1_tex_2(A_539, B_540), A_539) | ~m1_subset_1(B_540, u1_struct_0(A_539)) | ~l1_pre_topc(A_539) | v2_struct_0(A_539))), inference(cnfTransformation, [status(thm)], [f_139])).
% 5.78/2.10  tff(c_4592, plain, (m1_pre_topc(k1_tex_2('#skF_5', '#skF_6'), '#skF_5') | ~l1_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_70, c_4575])).
% 5.78/2.10  tff(c_4600, plain, (m1_pre_topc(k1_tex_2('#skF_5', '#skF_6'), '#skF_5') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_4592])).
% 5.78/2.10  tff(c_4601, plain, (m1_pre_topc(k1_tex_2('#skF_5', '#skF_6'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_74, c_4600])).
% 5.78/2.10  tff(c_4687, plain, (![B_553, A_554]: (~v1_tex_2(B_553, A_554) | v2_struct_0(B_553) | ~m1_pre_topc(B_553, A_554) | ~l1_pre_topc(A_554) | ~v7_struct_0(A_554) | v2_struct_0(A_554))), inference(cnfTransformation, [status(thm)], [f_104])).
% 5.78/2.10  tff(c_4693, plain, (v2_struct_0(k1_tex_2('#skF_5', '#skF_6')) | ~m1_pre_topc(k1_tex_2('#skF_5', '#skF_6'), '#skF_5') | ~l1_pre_topc('#skF_5') | ~v7_struct_0('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_3063, c_4687])).
% 5.78/2.10  tff(c_4697, plain, (v2_struct_0(k1_tex_2('#skF_5', '#skF_6')) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_4243, c_72, c_4601, c_4693])).
% 5.78/2.10  tff(c_4699, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_4452, c_4697])).
% 5.78/2.10  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.78/2.10  
% 5.78/2.10  Inference rules
% 5.78/2.10  ----------------------
% 5.78/2.10  #Ref     : 0
% 5.78/2.10  #Sup     : 895
% 5.78/2.10  #Fact    : 0
% 5.78/2.10  #Define  : 0
% 5.78/2.10  #Split   : 29
% 5.78/2.10  #Chain   : 0
% 5.78/2.10  #Close   : 0
% 5.78/2.10  
% 5.78/2.10  Ordering : KBO
% 5.78/2.10  
% 5.78/2.10  Simplification rules
% 5.78/2.10  ----------------------
% 5.78/2.10  #Subsume      : 305
% 5.78/2.10  #Demod        : 221
% 5.78/2.10  #Tautology    : 142
% 5.78/2.10  #SimpNegUnit  : 241
% 5.78/2.10  #BackRed      : 160
% 5.78/2.10  
% 5.78/2.10  #Partial instantiations: 0
% 5.78/2.10  #Strategies tried      : 1
% 5.78/2.10  
% 5.78/2.10  Timing (in seconds)
% 5.78/2.10  ----------------------
% 5.78/2.11  Preprocessing        : 0.35
% 5.78/2.11  Parsing              : 0.19
% 5.78/2.11  CNF conversion       : 0.03
% 5.78/2.11  Main loop            : 0.97
% 5.78/2.11  Inferencing          : 0.33
% 5.78/2.11  Reduction            : 0.28
% 5.78/2.11  Demodulation         : 0.18
% 5.78/2.11  BG Simplification    : 0.04
% 5.78/2.11  Subsumption          : 0.23
% 5.78/2.11  Abstraction          : 0.04
% 5.78/2.11  MUC search           : 0.00
% 5.78/2.11  Cooper               : 0.00
% 5.78/2.11  Total                : 1.37
% 5.78/2.11  Index Insertion      : 0.00
% 5.78/2.11  Index Deletion       : 0.00
% 5.78/2.11  Index Matching       : 0.00
% 5.78/2.11  BG Taut test         : 0.00
%------------------------------------------------------------------------------
