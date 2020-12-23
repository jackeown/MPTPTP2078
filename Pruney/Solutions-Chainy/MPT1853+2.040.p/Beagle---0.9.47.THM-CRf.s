%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:05 EST 2020

% Result     : Theorem 8.68s
% Output     : CNFRefutation 9.00s
% Verified   : 
% Statistics : Number of formulae       :  182 ( 671 expanded)
%              Number of leaves         :   50 ( 240 expanded)
%              Depth                    :   15
%              Number of atoms          :  387 (1857 expanded)
%              Number of equality atoms :   18 (  64 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_tex_2 > v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v7_struct_0 > v2_struct_0 > v1_zfmisc_1 > v1_xboole_0 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k6_domain_1 > k2_tarski > k1_tex_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_1 > #skF_4 > #skF_7 > #skF_8 > #skF_3 > #skF_2 > #skF_6

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': $i > $i )).

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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k1_tex_2,type,(
    k1_tex_2: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

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

tff('#skF_6',type,(
    '#skF_6': $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_227,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ( v1_tex_2(k1_tex_2(A,B),A)
            <=> v1_subset_1(k6_domain_1(u1_struct_0(A),B),u1_struct_0(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_tex_2)).

tff(f_140,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ( ~ v2_struct_0(k1_tex_2(A,B))
        & v1_pre_topc(k1_tex_2(A,B))
        & m1_pre_topc(k1_tex_2(A,B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tex_2)).

tff(f_77,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_70,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_154,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ( ~ v2_struct_0(k1_tex_2(A,B))
        & v7_struct_0(k1_tex_2(A,B))
        & v1_pre_topc(k1_tex_2(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_tex_2)).

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

tff(f_59,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_66,axiom,(
    ! [A] :
      ( v1_zfmisc_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_zfmisc_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_1)).

tff(f_165,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ? [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
          & ~ v1_xboole_0(B)
          & v1_zfmisc_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_tex_2)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(f_190,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,A)
         => ~ ( v1_subset_1(k6_domain_1(A,B),A)
              & v1_zfmisc_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tex_2)).

tff(f_105,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_126,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( v1_subset_1(B,A)
      <=> B != A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).

tff(f_179,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( C = u1_struct_0(B)
               => ( v1_subset_1(C,u1_struct_0(A))
                <=> v1_tex_2(B,A) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_tex_2)).

tff(f_201,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & ~ v1_zfmisc_1(A) )
     => ! [B] :
          ( m1_subset_1(B,A)
         => v1_subset_1(k6_domain_1(A,B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tex_2)).

tff(f_214,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ~ ( v1_subset_1(k6_domain_1(u1_struct_0(A),B),u1_struct_0(A))
              & v7_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_tex_2)).

tff(f_91,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_119,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_zfmisc_1(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => ( ~ v1_xboole_0(B)
           => ~ v1_subset_1(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_tex_2)).

tff(f_98,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ? [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
          & v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_connsp_1)).

tff(f_55,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => ~ v1_subset_1(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_subset_1)).

tff(c_88,plain,(
    l1_pre_topc('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_227])).

tff(c_90,plain,(
    ~ v2_struct_0('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_227])).

tff(c_86,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_227])).

tff(c_2704,plain,(
    ! [A_409,B_410] :
      ( m1_pre_topc(k1_tex_2(A_409,B_410),A_409)
      | ~ m1_subset_1(B_410,u1_struct_0(A_409))
      | ~ l1_pre_topc(A_409)
      | v2_struct_0(A_409) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_2706,plain,
    ( m1_pre_topc(k1_tex_2('#skF_7','#skF_8'),'#skF_7')
    | ~ l1_pre_topc('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_86,c_2704])).

tff(c_2709,plain,
    ( m1_pre_topc(k1_tex_2('#skF_7','#skF_8'),'#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_2706])).

tff(c_2710,plain,(
    m1_pre_topc(k1_tex_2('#skF_7','#skF_8'),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_2709])).

tff(c_40,plain,(
    ! [B_27,A_25] :
      ( l1_pre_topc(B_27)
      | ~ m1_pre_topc(B_27,A_25)
      | ~ l1_pre_topc(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_2715,plain,
    ( l1_pre_topc(k1_tex_2('#skF_7','#skF_8'))
    | ~ l1_pre_topc('#skF_7') ),
    inference(resolution,[status(thm)],[c_2710,c_40])).

tff(c_2721,plain,(
    l1_pre_topc(k1_tex_2('#skF_7','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_2715])).

tff(c_38,plain,(
    ! [A_24] :
      ( l1_struct_0(A_24)
      | ~ l1_pre_topc(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_2559,plain,(
    ! [A_388,B_389] :
      ( ~ v2_struct_0(k1_tex_2(A_388,B_389))
      | ~ m1_subset_1(B_389,u1_struct_0(A_388))
      | ~ l1_pre_topc(A_388)
      | v2_struct_0(A_388) ) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_2562,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_7','#skF_8'))
    | ~ l1_pre_topc('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_86,c_2559])).

tff(c_2565,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_7','#skF_8'))
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_2562])).

tff(c_2566,plain,(
    ~ v2_struct_0(k1_tex_2('#skF_7','#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_2565])).

tff(c_98,plain,
    ( v1_tex_2(k1_tex_2('#skF_7','#skF_8'),'#skF_7')
    | v1_subset_1(k6_domain_1(u1_struct_0('#skF_7'),'#skF_8'),u1_struct_0('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_227])).

tff(c_113,plain,(
    v1_subset_1(k6_domain_1(u1_struct_0('#skF_7'),'#skF_8'),u1_struct_0('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_98])).

tff(c_777,plain,(
    ! [A_181,B_182] :
      ( m1_pre_topc(k1_tex_2(A_181,B_182),A_181)
      | ~ m1_subset_1(B_182,u1_struct_0(A_181))
      | ~ l1_pre_topc(A_181)
      | v2_struct_0(A_181) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_779,plain,
    ( m1_pre_topc(k1_tex_2('#skF_7','#skF_8'),'#skF_7')
    | ~ l1_pre_topc('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_86,c_777])).

tff(c_782,plain,
    ( m1_pre_topc(k1_tex_2('#skF_7','#skF_8'),'#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_779])).

tff(c_783,plain,(
    m1_pre_topc(k1_tex_2('#skF_7','#skF_8'),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_782])).

tff(c_786,plain,
    ( l1_pre_topc(k1_tex_2('#skF_7','#skF_8'))
    | ~ l1_pre_topc('#skF_7') ),
    inference(resolution,[status(thm)],[c_783,c_40])).

tff(c_789,plain,(
    l1_pre_topc(k1_tex_2('#skF_7','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_786])).

tff(c_155,plain,(
    ! [A_92,B_93] :
      ( r2_hidden('#skF_2'(A_92,B_93),A_92)
      | r1_tarski(A_92,B_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_164,plain,(
    ! [A_92,B_93] :
      ( ~ v1_xboole_0(A_92)
      | r1_tarski(A_92,B_93) ) ),
    inference(resolution,[status(thm)],[c_155,c_2])).

tff(c_34,plain,(
    ! [A_19,B_20] :
      ( m1_subset_1(A_19,k1_zfmisc_1(B_20))
      | ~ r1_tarski(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_170,plain,(
    ! [B_98,A_99] :
      ( v1_zfmisc_1(B_98)
      | ~ m1_subset_1(B_98,k1_zfmisc_1(A_99))
      | ~ v1_zfmisc_1(A_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_183,plain,(
    ! [A_100,B_101] :
      ( v1_zfmisc_1(A_100)
      | ~ v1_zfmisc_1(B_101)
      | ~ r1_tarski(A_100,B_101) ) ),
    inference(resolution,[status(thm)],[c_34,c_170])).

tff(c_196,plain,(
    ! [A_92,B_93] :
      ( v1_zfmisc_1(A_92)
      | ~ v1_zfmisc_1(B_93)
      | ~ v1_xboole_0(A_92) ) ),
    inference(resolution,[status(thm)],[c_164,c_183])).

tff(c_213,plain,(
    ! [B_93] : ~ v1_zfmisc_1(B_93) ),
    inference(splitLeft,[status(thm)],[c_196])).

tff(c_70,plain,(
    ! [A_44] :
      ( v1_zfmisc_1('#skF_6'(A_44))
      | v1_xboole_0(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_216,plain,(
    ! [A_44] : v1_xboole_0(A_44) ),
    inference(negUnitSimplification,[status(thm)],[c_213,c_70])).

tff(c_14,plain,(
    ! [D_15,A_10] : r2_hidden(D_15,k2_tarski(A_10,D_15)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_104,plain,(
    ! [B_70,A_71] :
      ( ~ r2_hidden(B_70,A_71)
      | ~ v1_xboole_0(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_111,plain,(
    ! [A_10,D_15] : ~ v1_xboole_0(k2_tarski(A_10,D_15)) ),
    inference(resolution,[status(thm)],[c_14,c_104])).

tff(c_233,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_216,c_111])).

tff(c_234,plain,(
    ! [A_92] :
      ( v1_zfmisc_1(A_92)
      | ~ v1_xboole_0(A_92) ) ),
    inference(splitRight,[status(thm)],[c_196])).

tff(c_452,plain,(
    ! [A_146,B_147] :
      ( ~ v1_zfmisc_1(A_146)
      | ~ v1_subset_1(k6_domain_1(A_146,B_147),A_146)
      | ~ m1_subset_1(B_147,A_146)
      | v1_xboole_0(A_146) ) ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_459,plain,
    ( ~ v1_zfmisc_1(u1_struct_0('#skF_7'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_7'))
    | v1_xboole_0(u1_struct_0('#skF_7')) ),
    inference(resolution,[status(thm)],[c_113,c_452])).

tff(c_463,plain,
    ( ~ v1_zfmisc_1(u1_struct_0('#skF_7'))
    | v1_xboole_0(u1_struct_0('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_459])).

tff(c_464,plain,(
    ~ v1_zfmisc_1(u1_struct_0('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_463])).

tff(c_468,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_7')) ),
    inference(resolution,[status(thm)],[c_234,c_464])).

tff(c_473,plain,(
    ! [A_148,B_149] :
      ( ~ v2_struct_0(k1_tex_2(A_148,B_149))
      | ~ m1_subset_1(B_149,u1_struct_0(A_148))
      | ~ l1_pre_topc(A_148)
      | v2_struct_0(A_148) ) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_476,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_7','#skF_8'))
    | ~ l1_pre_topc('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_86,c_473])).

tff(c_479,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_7','#skF_8'))
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_476])).

tff(c_480,plain,(
    ~ v2_struct_0(k1_tex_2('#skF_7','#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_479])).

tff(c_393,plain,(
    ! [B_137,A_138] :
      ( m1_subset_1(u1_struct_0(B_137),k1_zfmisc_1(u1_struct_0(A_138)))
      | ~ m1_pre_topc(B_137,A_138)
      | ~ l1_pre_topc(A_138) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_54,plain,(
    ! [B_39,A_38] :
      ( v1_subset_1(B_39,A_38)
      | B_39 = A_38
      | ~ m1_subset_1(B_39,k1_zfmisc_1(A_38)) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_406,plain,(
    ! [B_137,A_138] :
      ( v1_subset_1(u1_struct_0(B_137),u1_struct_0(A_138))
      | u1_struct_0(B_137) = u1_struct_0(A_138)
      | ~ m1_pre_topc(B_137,A_138)
      | ~ l1_pre_topc(A_138) ) ),
    inference(resolution,[status(thm)],[c_393,c_54])).

tff(c_50,plain,(
    ! [B_34,A_32] :
      ( m1_subset_1(u1_struct_0(B_34),k1_zfmisc_1(u1_struct_0(A_32)))
      | ~ m1_pre_topc(B_34,A_32)
      | ~ l1_pre_topc(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_1479,plain,(
    ! [B_267,A_268] :
      ( v1_tex_2(B_267,A_268)
      | ~ v1_subset_1(u1_struct_0(B_267),u1_struct_0(A_268))
      | ~ m1_subset_1(u1_struct_0(B_267),k1_zfmisc_1(u1_struct_0(A_268)))
      | ~ m1_pre_topc(B_267,A_268)
      | ~ l1_pre_topc(A_268) ) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_1488,plain,(
    ! [B_269,A_270] :
      ( v1_tex_2(B_269,A_270)
      | ~ v1_subset_1(u1_struct_0(B_269),u1_struct_0(A_270))
      | ~ m1_pre_topc(B_269,A_270)
      | ~ l1_pre_topc(A_270) ) ),
    inference(resolution,[status(thm)],[c_50,c_1479])).

tff(c_1501,plain,(
    ! [B_271,A_272] :
      ( v1_tex_2(B_271,A_272)
      | u1_struct_0(B_271) = u1_struct_0(A_272)
      | ~ m1_pre_topc(B_271,A_272)
      | ~ l1_pre_topc(A_272) ) ),
    inference(resolution,[status(thm)],[c_406,c_1488])).

tff(c_92,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0('#skF_7'),'#skF_8'),u1_struct_0('#skF_7'))
    | ~ v1_tex_2(k1_tex_2('#skF_7','#skF_8'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_227])).

tff(c_130,plain,(
    ~ v1_tex_2(k1_tex_2('#skF_7','#skF_8'),'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_92])).

tff(c_1511,plain,
    ( u1_struct_0(k1_tex_2('#skF_7','#skF_8')) = u1_struct_0('#skF_7')
    | ~ m1_pre_topc(k1_tex_2('#skF_7','#skF_8'),'#skF_7')
    | ~ l1_pre_topc('#skF_7') ),
    inference(resolution,[status(thm)],[c_1501,c_130])).

tff(c_1517,plain,(
    u1_struct_0(k1_tex_2('#skF_7','#skF_8')) = u1_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_783,c_1511])).

tff(c_648,plain,(
    ! [A_170,B_171] :
      ( v7_struct_0(k1_tex_2(A_170,B_171))
      | ~ m1_subset_1(B_171,u1_struct_0(A_170))
      | ~ l1_pre_topc(A_170)
      | v2_struct_0(A_170) ) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_651,plain,
    ( v7_struct_0(k1_tex_2('#skF_7','#skF_8'))
    | ~ l1_pre_topc('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_86,c_648])).

tff(c_654,plain,
    ( v7_struct_0(k1_tex_2('#skF_7','#skF_8'))
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_651])).

tff(c_655,plain,(
    v7_struct_0(k1_tex_2('#skF_7','#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_654])).

tff(c_82,plain,(
    ! [A_56,B_58] :
      ( v1_subset_1(k6_domain_1(A_56,B_58),A_56)
      | ~ m1_subset_1(B_58,A_56)
      | v1_zfmisc_1(A_56)
      | v1_xboole_0(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_1125,plain,(
    ! [A_220,B_221] :
      ( ~ v7_struct_0(A_220)
      | ~ v1_subset_1(k6_domain_1(u1_struct_0(A_220),B_221),u1_struct_0(A_220))
      | ~ m1_subset_1(B_221,u1_struct_0(A_220))
      | ~ l1_struct_0(A_220)
      | v2_struct_0(A_220) ) ),
    inference(cnfTransformation,[status(thm)],[f_214])).

tff(c_2007,plain,(
    ! [A_293,B_294] :
      ( ~ v7_struct_0(A_293)
      | ~ l1_struct_0(A_293)
      | v2_struct_0(A_293)
      | ~ m1_subset_1(B_294,u1_struct_0(A_293))
      | v1_zfmisc_1(u1_struct_0(A_293))
      | v1_xboole_0(u1_struct_0(A_293)) ) ),
    inference(resolution,[status(thm)],[c_82,c_1125])).

tff(c_2010,plain,(
    ! [B_294] :
      ( ~ v7_struct_0(k1_tex_2('#skF_7','#skF_8'))
      | ~ l1_struct_0(k1_tex_2('#skF_7','#skF_8'))
      | v2_struct_0(k1_tex_2('#skF_7','#skF_8'))
      | ~ m1_subset_1(B_294,u1_struct_0('#skF_7'))
      | v1_zfmisc_1(u1_struct_0(k1_tex_2('#skF_7','#skF_8')))
      | v1_xboole_0(u1_struct_0(k1_tex_2('#skF_7','#skF_8'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1517,c_2007])).

tff(c_2015,plain,(
    ! [B_294] :
      ( ~ l1_struct_0(k1_tex_2('#skF_7','#skF_8'))
      | v2_struct_0(k1_tex_2('#skF_7','#skF_8'))
      | ~ m1_subset_1(B_294,u1_struct_0('#skF_7'))
      | v1_zfmisc_1(u1_struct_0('#skF_7'))
      | v1_xboole_0(u1_struct_0('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1517,c_1517,c_655,c_2010])).

tff(c_2016,plain,(
    ! [B_294] :
      ( ~ l1_struct_0(k1_tex_2('#skF_7','#skF_8'))
      | ~ m1_subset_1(B_294,u1_struct_0('#skF_7')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_468,c_464,c_480,c_2015])).

tff(c_2021,plain,(
    ~ l1_struct_0(k1_tex_2('#skF_7','#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_2016])).

tff(c_2024,plain,(
    ~ l1_pre_topc(k1_tex_2('#skF_7','#skF_8')) ),
    inference(resolution,[status(thm)],[c_38,c_2021])).

tff(c_2028,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_789,c_2024])).

tff(c_2029,plain,(
    ! [B_294] : ~ m1_subset_1(B_294,u1_struct_0('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_2016])).

tff(c_2038,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2029,c_86])).

tff(c_2039,plain,(
    v1_xboole_0(u1_struct_0('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_463])).

tff(c_44,plain,(
    ! [A_29] :
      ( ~ v1_xboole_0(u1_struct_0(A_29))
      | ~ l1_struct_0(A_29)
      | v2_struct_0(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_2063,plain,
    ( ~ l1_struct_0('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_2039,c_44])).

tff(c_2069,plain,(
    ~ l1_struct_0('#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_2063])).

tff(c_2072,plain,(
    ~ l1_pre_topc('#skF_7') ),
    inference(resolution,[status(thm)],[c_38,c_2069])).

tff(c_2076,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_2072])).

tff(c_2077,plain,(
    ~ v1_subset_1(k6_domain_1(u1_struct_0('#skF_7'),'#skF_8'),u1_struct_0('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_92])).

tff(c_2097,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_2077])).

tff(c_2098,plain,(
    v1_tex_2(k1_tex_2('#skF_7','#skF_8'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_98])).

tff(c_2581,plain,(
    ! [A_393,B_394] :
      ( v1_subset_1(k6_domain_1(A_393,B_394),A_393)
      | ~ m1_subset_1(B_394,A_393)
      | v1_zfmisc_1(A_393)
      | v1_xboole_0(A_393) ) ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_2099,plain,(
    ~ v1_subset_1(k6_domain_1(u1_struct_0('#skF_7'),'#skF_8'),u1_struct_0('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_98])).

tff(c_2590,plain,
    ( ~ m1_subset_1('#skF_8',u1_struct_0('#skF_7'))
    | v1_zfmisc_1(u1_struct_0('#skF_7'))
    | v1_xboole_0(u1_struct_0('#skF_7')) ),
    inference(resolution,[status(thm)],[c_2581,c_2099])).

tff(c_2595,plain,
    ( v1_zfmisc_1(u1_struct_0('#skF_7'))
    | v1_xboole_0(u1_struct_0('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_2590])).

tff(c_2596,plain,(
    v1_xboole_0(u1_struct_0('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_2595])).

tff(c_2605,plain,
    ( ~ l1_struct_0('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_2596,c_44])).

tff(c_2611,plain,(
    ~ l1_struct_0('#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_2605])).

tff(c_2614,plain,(
    ~ l1_pre_topc('#skF_7') ),
    inference(resolution,[status(thm)],[c_38,c_2611])).

tff(c_2618,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_2614])).

tff(c_2620,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_2595])).

tff(c_2619,plain,(
    v1_zfmisc_1(u1_struct_0('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_2595])).

tff(c_3605,plain,(
    ! [B_466,A_467] :
      ( v1_subset_1(u1_struct_0(B_466),u1_struct_0(A_467))
      | ~ v1_tex_2(B_466,A_467)
      | ~ m1_subset_1(u1_struct_0(B_466),k1_zfmisc_1(u1_struct_0(A_467)))
      | ~ m1_pre_topc(B_466,A_467)
      | ~ l1_pre_topc(A_467) ) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_3626,plain,(
    ! [B_34,A_32] :
      ( v1_subset_1(u1_struct_0(B_34),u1_struct_0(A_32))
      | ~ v1_tex_2(B_34,A_32)
      | ~ m1_pre_topc(B_34,A_32)
      | ~ l1_pre_topc(A_32) ) ),
    inference(resolution,[status(thm)],[c_50,c_3605])).

tff(c_2818,plain,(
    ! [B_412,A_413] :
      ( ~ v1_subset_1(B_412,A_413)
      | v1_xboole_0(B_412)
      | ~ m1_subset_1(B_412,k1_zfmisc_1(A_413))
      | ~ v1_zfmisc_1(A_413)
      | v1_xboole_0(A_413) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_6463,plain,(
    ! [B_622,A_623] :
      ( ~ v1_subset_1(u1_struct_0(B_622),u1_struct_0(A_623))
      | v1_xboole_0(u1_struct_0(B_622))
      | ~ v1_zfmisc_1(u1_struct_0(A_623))
      | v1_xboole_0(u1_struct_0(A_623))
      | ~ m1_pre_topc(B_622,A_623)
      | ~ l1_pre_topc(A_623) ) ),
    inference(resolution,[status(thm)],[c_50,c_2818])).

tff(c_7883,plain,(
    ! [B_701,A_702] :
      ( v1_xboole_0(u1_struct_0(B_701))
      | ~ v1_zfmisc_1(u1_struct_0(A_702))
      | v1_xboole_0(u1_struct_0(A_702))
      | ~ v1_tex_2(B_701,A_702)
      | ~ m1_pre_topc(B_701,A_702)
      | ~ l1_pre_topc(A_702) ) ),
    inference(resolution,[status(thm)],[c_3626,c_6463])).

tff(c_7889,plain,(
    ! [B_701] :
      ( v1_xboole_0(u1_struct_0(B_701))
      | v1_xboole_0(u1_struct_0('#skF_7'))
      | ~ v1_tex_2(B_701,'#skF_7')
      | ~ m1_pre_topc(B_701,'#skF_7')
      | ~ l1_pre_topc('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_2619,c_7883])).

tff(c_7900,plain,(
    ! [B_701] :
      ( v1_xboole_0(u1_struct_0(B_701))
      | v1_xboole_0(u1_struct_0('#skF_7'))
      | ~ v1_tex_2(B_701,'#skF_7')
      | ~ m1_pre_topc(B_701,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_7889])).

tff(c_7903,plain,(
    ! [B_703] :
      ( v1_xboole_0(u1_struct_0(B_703))
      | ~ v1_tex_2(B_703,'#skF_7')
      | ~ m1_pre_topc(B_703,'#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_2620,c_7900])).

tff(c_46,plain,(
    ! [A_30] :
      ( v1_xboole_0('#skF_5'(A_30))
      | ~ l1_pre_topc(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_2154,plain,(
    ! [A_325,B_326] :
      ( r2_hidden('#skF_2'(A_325,B_326),A_325)
      | r1_tarski(A_325,B_326) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2163,plain,(
    ! [A_325,B_326] :
      ( ~ v1_xboole_0(A_325)
      | r1_tarski(A_325,B_326) ) ),
    inference(resolution,[status(thm)],[c_2154,c_2])).

tff(c_2247,plain,(
    ! [B_344,A_345] :
      ( v1_subset_1(B_344,A_345)
      | B_344 = A_345
      | ~ m1_subset_1(B_344,k1_zfmisc_1(A_345)) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_2284,plain,(
    ! [A_352,B_353] :
      ( v1_subset_1(A_352,B_353)
      | B_353 = A_352
      | ~ r1_tarski(A_352,B_353) ) ),
    inference(resolution,[status(thm)],[c_34,c_2247])).

tff(c_2214,plain,(
    ! [B_335,A_336] :
      ( ~ v1_subset_1(B_335,A_336)
      | ~ m1_subset_1(B_335,k1_zfmisc_1(A_336))
      | ~ v1_xboole_0(A_336) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_2225,plain,(
    ! [A_19,B_20] :
      ( ~ v1_subset_1(A_19,B_20)
      | ~ v1_xboole_0(B_20)
      | ~ r1_tarski(A_19,B_20) ) ),
    inference(resolution,[status(thm)],[c_34,c_2214])).

tff(c_2302,plain,(
    ! [B_354,A_355] :
      ( ~ v1_xboole_0(B_354)
      | B_354 = A_355
      | ~ r1_tarski(A_355,B_354) ) ),
    inference(resolution,[status(thm)],[c_2284,c_2225])).

tff(c_2320,plain,(
    ! [B_356,A_357] :
      ( ~ v1_xboole_0(B_356)
      | B_356 = A_357
      | ~ v1_xboole_0(A_357) ) ),
    inference(resolution,[status(thm)],[c_2163,c_2302])).

tff(c_2331,plain,(
    ! [A_358,A_359] :
      ( A_358 = '#skF_5'(A_359)
      | ~ v1_xboole_0(A_358)
      | ~ l1_pre_topc(A_359) ) ),
    inference(resolution,[status(thm)],[c_46,c_2320])).

tff(c_2361,plain,(
    ! [A_364,A_363] :
      ( '#skF_5'(A_364) = '#skF_5'(A_363)
      | ~ l1_pre_topc(A_363)
      | ~ l1_pre_topc(A_364) ) ),
    inference(resolution,[status(thm)],[c_46,c_2331])).

tff(c_2364,plain,(
    ! [A_364] :
      ( '#skF_5'(A_364) = '#skF_5'('#skF_7')
      | ~ l1_pre_topc(A_364) ) ),
    inference(resolution,[status(thm)],[c_88,c_2361])).

tff(c_2730,plain,(
    '#skF_5'(k1_tex_2('#skF_7','#skF_8')) = '#skF_5'('#skF_7') ),
    inference(resolution,[status(thm)],[c_2721,c_2364])).

tff(c_2200,plain,(
    ! [A_333] :
      ( m1_subset_1('#skF_5'(A_333),k1_zfmisc_1(u1_struct_0(A_333)))
      | ~ l1_pre_topc(A_333) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_32,plain,(
    ! [A_19,B_20] :
      ( r1_tarski(A_19,B_20)
      | ~ m1_subset_1(A_19,k1_zfmisc_1(B_20)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_2208,plain,(
    ! [A_333] :
      ( r1_tarski('#skF_5'(A_333),u1_struct_0(A_333))
      | ~ l1_pre_topc(A_333) ) ),
    inference(resolution,[status(thm)],[c_2200,c_32])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_2'(A_5,B_6),A_5)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2234,plain,(
    ! [C_341,B_342,A_343] :
      ( r2_hidden(C_341,B_342)
      | ~ r2_hidden(C_341,A_343)
      | ~ r1_tarski(A_343,B_342) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2653,plain,(
    ! [A_399,B_400,B_401] :
      ( r2_hidden('#skF_2'(A_399,B_400),B_401)
      | ~ r1_tarski(A_399,B_401)
      | r1_tarski(A_399,B_400) ) ),
    inference(resolution,[status(thm)],[c_10,c_2234])).

tff(c_2671,plain,(
    ! [B_402,A_403,B_404] :
      ( ~ v1_xboole_0(B_402)
      | ~ r1_tarski(A_403,B_402)
      | r1_tarski(A_403,B_404) ) ),
    inference(resolution,[status(thm)],[c_2653,c_2])).

tff(c_2683,plain,(
    ! [A_333,B_404] :
      ( ~ v1_xboole_0(u1_struct_0(A_333))
      | r1_tarski('#skF_5'(A_333),B_404)
      | ~ l1_pre_topc(A_333) ) ),
    inference(resolution,[status(thm)],[c_2208,c_2671])).

tff(c_2735,plain,(
    ! [B_404] :
      ( ~ v1_xboole_0(u1_struct_0(k1_tex_2('#skF_7','#skF_8')))
      | r1_tarski('#skF_5'('#skF_7'),B_404)
      | ~ l1_pre_topc(k1_tex_2('#skF_7','#skF_8')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2730,c_2683])).

tff(c_2760,plain,(
    ! [B_404] :
      ( ~ v1_xboole_0(u1_struct_0(k1_tex_2('#skF_7','#skF_8')))
      | r1_tarski('#skF_5'('#skF_7'),B_404) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2721,c_2735])).

tff(c_2858,plain,(
    ~ v1_xboole_0(u1_struct_0(k1_tex_2('#skF_7','#skF_8'))) ),
    inference(splitLeft,[status(thm)],[c_2760])).

tff(c_7921,plain,
    ( ~ v1_tex_2(k1_tex_2('#skF_7','#skF_8'),'#skF_7')
    | ~ m1_pre_topc(k1_tex_2('#skF_7','#skF_8'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_7903,c_2858])).

tff(c_7947,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2710,c_2098,c_7921])).

tff(c_7949,plain,(
    v1_xboole_0(u1_struct_0(k1_tex_2('#skF_7','#skF_8'))) ),
    inference(splitRight,[status(thm)],[c_2760])).

tff(c_7981,plain,
    ( ~ l1_struct_0(k1_tex_2('#skF_7','#skF_8'))
    | v2_struct_0(k1_tex_2('#skF_7','#skF_8')) ),
    inference(resolution,[status(thm)],[c_7949,c_44])).

tff(c_7988,plain,(
    ~ l1_struct_0(k1_tex_2('#skF_7','#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_2566,c_7981])).

tff(c_7991,plain,(
    ~ l1_pre_topc(k1_tex_2('#skF_7','#skF_8')) ),
    inference(resolution,[status(thm)],[c_38,c_7988])).

tff(c_7995,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2721,c_7991])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:23:46 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.68/2.87  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.68/2.89  
% 8.68/2.89  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.68/2.89  %$ v1_tex_2 > v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v7_struct_0 > v2_struct_0 > v1_zfmisc_1 > v1_xboole_0 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k6_domain_1 > k2_tarski > k1_tex_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_1 > #skF_4 > #skF_7 > #skF_8 > #skF_3 > #skF_2 > #skF_6
% 8.68/2.89  
% 8.68/2.89  %Foreground sorts:
% 8.68/2.89  
% 8.68/2.89  
% 8.68/2.89  %Background operators:
% 8.68/2.89  
% 8.68/2.89  
% 8.68/2.89  %Foreground operators:
% 8.68/2.89  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 8.68/2.89  tff('#skF_5', type, '#skF_5': $i > $i).
% 8.68/2.89  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.68/2.89  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.68/2.89  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 8.68/2.89  tff('#skF_1', type, '#skF_1': $i > $i).
% 8.68/2.89  tff(v1_tex_2, type, v1_tex_2: ($i * $i) > $o).
% 8.68/2.89  tff(v7_struct_0, type, v7_struct_0: $i > $o).
% 8.68/2.89  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 8.68/2.89  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 8.68/2.89  tff('#skF_7', type, '#skF_7': $i).
% 8.68/2.89  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 8.68/2.89  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.68/2.89  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 8.68/2.89  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 8.68/2.89  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.68/2.89  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 8.68/2.89  tff('#skF_8', type, '#skF_8': $i).
% 8.68/2.89  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.68/2.89  tff(k1_tex_2, type, k1_tex_2: ($i * $i) > $i).
% 8.68/2.89  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 8.68/2.89  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.68/2.89  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 8.68/2.89  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 8.68/2.89  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 8.68/2.89  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 8.68/2.89  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 8.68/2.89  tff('#skF_6', type, '#skF_6': $i > $i).
% 8.68/2.89  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.68/2.89  
% 9.00/2.92  tff(f_227, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (v1_tex_2(k1_tex_2(A, B), A) <=> v1_subset_1(k6_domain_1(u1_struct_0(A), B), u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_tex_2)).
% 9.00/2.92  tff(f_140, axiom, (![A, B]: (((~v2_struct_0(A) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => ((~v2_struct_0(k1_tex_2(A, B)) & v1_pre_topc(k1_tex_2(A, B))) & m1_pre_topc(k1_tex_2(A, B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_tex_2)).
% 9.00/2.92  tff(f_77, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 9.00/2.92  tff(f_70, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 9.00/2.92  tff(f_154, axiom, (![A, B]: (((~v2_struct_0(A) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => ((~v2_struct_0(k1_tex_2(A, B)) & v7_struct_0(k1_tex_2(A, B))) & v1_pre_topc(k1_tex_2(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_tex_2)).
% 9.00/2.92  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 9.00/2.92  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 9.00/2.92  tff(f_59, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 9.00/2.92  tff(f_66, axiom, (![A]: (v1_zfmisc_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_zfmisc_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc5_funct_1)).
% 9.00/2.92  tff(f_165, axiom, (![A]: (~v1_xboole_0(A) => (?[B]: ((m1_subset_1(B, k1_zfmisc_1(A)) & ~v1_xboole_0(B)) & v1_zfmisc_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc1_tex_2)).
% 9.00/2.92  tff(f_47, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 9.00/2.92  tff(f_190, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, A) => ~(v1_subset_1(k6_domain_1(A, B), A) & v1_zfmisc_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_tex_2)).
% 9.00/2.92  tff(f_105, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 9.00/2.92  tff(f_126, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (v1_subset_1(B, A) <=> ~(B = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_subset_1)).
% 9.00/2.92  tff(f_179, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => (v1_subset_1(C, u1_struct_0(A)) <=> v1_tex_2(B, A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_tex_2)).
% 9.00/2.92  tff(f_201, axiom, (![A]: ((~v1_xboole_0(A) & ~v1_zfmisc_1(A)) => (![B]: (m1_subset_1(B, A) => v1_subset_1(k6_domain_1(A, B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_tex_2)).
% 9.00/2.92  tff(f_214, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => ~(v1_subset_1(k6_domain_1(u1_struct_0(A), B), u1_struct_0(A)) & v7_struct_0(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_tex_2)).
% 9.00/2.92  tff(f_91, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 9.00/2.92  tff(f_119, axiom, (![A]: ((~v1_xboole_0(A) & v1_zfmisc_1(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (~v1_xboole_0(B) => ~v1_subset_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_tex_2)).
% 9.00/2.92  tff(f_98, axiom, (![A]: (l1_pre_topc(A) => (?[B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) & v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc1_connsp_1)).
% 9.00/2.92  tff(f_55, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => ~v1_subset_1(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc4_subset_1)).
% 9.00/2.92  tff(c_88, plain, (l1_pre_topc('#skF_7')), inference(cnfTransformation, [status(thm)], [f_227])).
% 9.00/2.92  tff(c_90, plain, (~v2_struct_0('#skF_7')), inference(cnfTransformation, [status(thm)], [f_227])).
% 9.00/2.92  tff(c_86, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_227])).
% 9.00/2.92  tff(c_2704, plain, (![A_409, B_410]: (m1_pre_topc(k1_tex_2(A_409, B_410), A_409) | ~m1_subset_1(B_410, u1_struct_0(A_409)) | ~l1_pre_topc(A_409) | v2_struct_0(A_409))), inference(cnfTransformation, [status(thm)], [f_140])).
% 9.00/2.92  tff(c_2706, plain, (m1_pre_topc(k1_tex_2('#skF_7', '#skF_8'), '#skF_7') | ~l1_pre_topc('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_86, c_2704])).
% 9.00/2.92  tff(c_2709, plain, (m1_pre_topc(k1_tex_2('#skF_7', '#skF_8'), '#skF_7') | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_2706])).
% 9.00/2.92  tff(c_2710, plain, (m1_pre_topc(k1_tex_2('#skF_7', '#skF_8'), '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_90, c_2709])).
% 9.00/2.92  tff(c_40, plain, (![B_27, A_25]: (l1_pre_topc(B_27) | ~m1_pre_topc(B_27, A_25) | ~l1_pre_topc(A_25))), inference(cnfTransformation, [status(thm)], [f_77])).
% 9.00/2.92  tff(c_2715, plain, (l1_pre_topc(k1_tex_2('#skF_7', '#skF_8')) | ~l1_pre_topc('#skF_7')), inference(resolution, [status(thm)], [c_2710, c_40])).
% 9.00/2.92  tff(c_2721, plain, (l1_pre_topc(k1_tex_2('#skF_7', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_2715])).
% 9.00/2.92  tff(c_38, plain, (![A_24]: (l1_struct_0(A_24) | ~l1_pre_topc(A_24))), inference(cnfTransformation, [status(thm)], [f_70])).
% 9.00/2.92  tff(c_2559, plain, (![A_388, B_389]: (~v2_struct_0(k1_tex_2(A_388, B_389)) | ~m1_subset_1(B_389, u1_struct_0(A_388)) | ~l1_pre_topc(A_388) | v2_struct_0(A_388))), inference(cnfTransformation, [status(thm)], [f_154])).
% 9.00/2.92  tff(c_2562, plain, (~v2_struct_0(k1_tex_2('#skF_7', '#skF_8')) | ~l1_pre_topc('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_86, c_2559])).
% 9.00/2.92  tff(c_2565, plain, (~v2_struct_0(k1_tex_2('#skF_7', '#skF_8')) | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_2562])).
% 9.00/2.92  tff(c_2566, plain, (~v2_struct_0(k1_tex_2('#skF_7', '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_90, c_2565])).
% 9.00/2.92  tff(c_98, plain, (v1_tex_2(k1_tex_2('#skF_7', '#skF_8'), '#skF_7') | v1_subset_1(k6_domain_1(u1_struct_0('#skF_7'), '#skF_8'), u1_struct_0('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_227])).
% 9.00/2.92  tff(c_113, plain, (v1_subset_1(k6_domain_1(u1_struct_0('#skF_7'), '#skF_8'), u1_struct_0('#skF_7'))), inference(splitLeft, [status(thm)], [c_98])).
% 9.00/2.92  tff(c_777, plain, (![A_181, B_182]: (m1_pre_topc(k1_tex_2(A_181, B_182), A_181) | ~m1_subset_1(B_182, u1_struct_0(A_181)) | ~l1_pre_topc(A_181) | v2_struct_0(A_181))), inference(cnfTransformation, [status(thm)], [f_140])).
% 9.00/2.92  tff(c_779, plain, (m1_pre_topc(k1_tex_2('#skF_7', '#skF_8'), '#skF_7') | ~l1_pre_topc('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_86, c_777])).
% 9.00/2.92  tff(c_782, plain, (m1_pre_topc(k1_tex_2('#skF_7', '#skF_8'), '#skF_7') | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_779])).
% 9.00/2.92  tff(c_783, plain, (m1_pre_topc(k1_tex_2('#skF_7', '#skF_8'), '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_90, c_782])).
% 9.00/2.92  tff(c_786, plain, (l1_pre_topc(k1_tex_2('#skF_7', '#skF_8')) | ~l1_pre_topc('#skF_7')), inference(resolution, [status(thm)], [c_783, c_40])).
% 9.00/2.92  tff(c_789, plain, (l1_pre_topc(k1_tex_2('#skF_7', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_786])).
% 9.00/2.92  tff(c_155, plain, (![A_92, B_93]: (r2_hidden('#skF_2'(A_92, B_93), A_92) | r1_tarski(A_92, B_93))), inference(cnfTransformation, [status(thm)], [f_38])).
% 9.00/2.92  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.00/2.92  tff(c_164, plain, (![A_92, B_93]: (~v1_xboole_0(A_92) | r1_tarski(A_92, B_93))), inference(resolution, [status(thm)], [c_155, c_2])).
% 9.00/2.92  tff(c_34, plain, (![A_19, B_20]: (m1_subset_1(A_19, k1_zfmisc_1(B_20)) | ~r1_tarski(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_59])).
% 9.00/2.92  tff(c_170, plain, (![B_98, A_99]: (v1_zfmisc_1(B_98) | ~m1_subset_1(B_98, k1_zfmisc_1(A_99)) | ~v1_zfmisc_1(A_99))), inference(cnfTransformation, [status(thm)], [f_66])).
% 9.00/2.92  tff(c_183, plain, (![A_100, B_101]: (v1_zfmisc_1(A_100) | ~v1_zfmisc_1(B_101) | ~r1_tarski(A_100, B_101))), inference(resolution, [status(thm)], [c_34, c_170])).
% 9.00/2.92  tff(c_196, plain, (![A_92, B_93]: (v1_zfmisc_1(A_92) | ~v1_zfmisc_1(B_93) | ~v1_xboole_0(A_92))), inference(resolution, [status(thm)], [c_164, c_183])).
% 9.00/2.92  tff(c_213, plain, (![B_93]: (~v1_zfmisc_1(B_93))), inference(splitLeft, [status(thm)], [c_196])).
% 9.00/2.92  tff(c_70, plain, (![A_44]: (v1_zfmisc_1('#skF_6'(A_44)) | v1_xboole_0(A_44))), inference(cnfTransformation, [status(thm)], [f_165])).
% 9.00/2.92  tff(c_216, plain, (![A_44]: (v1_xboole_0(A_44))), inference(negUnitSimplification, [status(thm)], [c_213, c_70])).
% 9.00/2.92  tff(c_14, plain, (![D_15, A_10]: (r2_hidden(D_15, k2_tarski(A_10, D_15)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 9.00/2.92  tff(c_104, plain, (![B_70, A_71]: (~r2_hidden(B_70, A_71) | ~v1_xboole_0(A_71))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.00/2.92  tff(c_111, plain, (![A_10, D_15]: (~v1_xboole_0(k2_tarski(A_10, D_15)))), inference(resolution, [status(thm)], [c_14, c_104])).
% 9.00/2.92  tff(c_233, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_216, c_111])).
% 9.00/2.92  tff(c_234, plain, (![A_92]: (v1_zfmisc_1(A_92) | ~v1_xboole_0(A_92))), inference(splitRight, [status(thm)], [c_196])).
% 9.00/2.92  tff(c_452, plain, (![A_146, B_147]: (~v1_zfmisc_1(A_146) | ~v1_subset_1(k6_domain_1(A_146, B_147), A_146) | ~m1_subset_1(B_147, A_146) | v1_xboole_0(A_146))), inference(cnfTransformation, [status(thm)], [f_190])).
% 9.00/2.92  tff(c_459, plain, (~v1_zfmisc_1(u1_struct_0('#skF_7')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_7')) | v1_xboole_0(u1_struct_0('#skF_7'))), inference(resolution, [status(thm)], [c_113, c_452])).
% 9.00/2.92  tff(c_463, plain, (~v1_zfmisc_1(u1_struct_0('#skF_7')) | v1_xboole_0(u1_struct_0('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_459])).
% 9.00/2.92  tff(c_464, plain, (~v1_zfmisc_1(u1_struct_0('#skF_7'))), inference(splitLeft, [status(thm)], [c_463])).
% 9.00/2.92  tff(c_468, plain, (~v1_xboole_0(u1_struct_0('#skF_7'))), inference(resolution, [status(thm)], [c_234, c_464])).
% 9.00/2.92  tff(c_473, plain, (![A_148, B_149]: (~v2_struct_0(k1_tex_2(A_148, B_149)) | ~m1_subset_1(B_149, u1_struct_0(A_148)) | ~l1_pre_topc(A_148) | v2_struct_0(A_148))), inference(cnfTransformation, [status(thm)], [f_154])).
% 9.00/2.92  tff(c_476, plain, (~v2_struct_0(k1_tex_2('#skF_7', '#skF_8')) | ~l1_pre_topc('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_86, c_473])).
% 9.00/2.92  tff(c_479, plain, (~v2_struct_0(k1_tex_2('#skF_7', '#skF_8')) | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_476])).
% 9.00/2.92  tff(c_480, plain, (~v2_struct_0(k1_tex_2('#skF_7', '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_90, c_479])).
% 9.00/2.92  tff(c_393, plain, (![B_137, A_138]: (m1_subset_1(u1_struct_0(B_137), k1_zfmisc_1(u1_struct_0(A_138))) | ~m1_pre_topc(B_137, A_138) | ~l1_pre_topc(A_138))), inference(cnfTransformation, [status(thm)], [f_105])).
% 9.00/2.92  tff(c_54, plain, (![B_39, A_38]: (v1_subset_1(B_39, A_38) | B_39=A_38 | ~m1_subset_1(B_39, k1_zfmisc_1(A_38)))), inference(cnfTransformation, [status(thm)], [f_126])).
% 9.00/2.92  tff(c_406, plain, (![B_137, A_138]: (v1_subset_1(u1_struct_0(B_137), u1_struct_0(A_138)) | u1_struct_0(B_137)=u1_struct_0(A_138) | ~m1_pre_topc(B_137, A_138) | ~l1_pre_topc(A_138))), inference(resolution, [status(thm)], [c_393, c_54])).
% 9.00/2.92  tff(c_50, plain, (![B_34, A_32]: (m1_subset_1(u1_struct_0(B_34), k1_zfmisc_1(u1_struct_0(A_32))) | ~m1_pre_topc(B_34, A_32) | ~l1_pre_topc(A_32))), inference(cnfTransformation, [status(thm)], [f_105])).
% 9.00/2.92  tff(c_1479, plain, (![B_267, A_268]: (v1_tex_2(B_267, A_268) | ~v1_subset_1(u1_struct_0(B_267), u1_struct_0(A_268)) | ~m1_subset_1(u1_struct_0(B_267), k1_zfmisc_1(u1_struct_0(A_268))) | ~m1_pre_topc(B_267, A_268) | ~l1_pre_topc(A_268))), inference(cnfTransformation, [status(thm)], [f_179])).
% 9.00/2.92  tff(c_1488, plain, (![B_269, A_270]: (v1_tex_2(B_269, A_270) | ~v1_subset_1(u1_struct_0(B_269), u1_struct_0(A_270)) | ~m1_pre_topc(B_269, A_270) | ~l1_pre_topc(A_270))), inference(resolution, [status(thm)], [c_50, c_1479])).
% 9.00/2.92  tff(c_1501, plain, (![B_271, A_272]: (v1_tex_2(B_271, A_272) | u1_struct_0(B_271)=u1_struct_0(A_272) | ~m1_pre_topc(B_271, A_272) | ~l1_pre_topc(A_272))), inference(resolution, [status(thm)], [c_406, c_1488])).
% 9.00/2.92  tff(c_92, plain, (~v1_subset_1(k6_domain_1(u1_struct_0('#skF_7'), '#skF_8'), u1_struct_0('#skF_7')) | ~v1_tex_2(k1_tex_2('#skF_7', '#skF_8'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_227])).
% 9.00/2.92  tff(c_130, plain, (~v1_tex_2(k1_tex_2('#skF_7', '#skF_8'), '#skF_7')), inference(splitLeft, [status(thm)], [c_92])).
% 9.00/2.92  tff(c_1511, plain, (u1_struct_0(k1_tex_2('#skF_7', '#skF_8'))=u1_struct_0('#skF_7') | ~m1_pre_topc(k1_tex_2('#skF_7', '#skF_8'), '#skF_7') | ~l1_pre_topc('#skF_7')), inference(resolution, [status(thm)], [c_1501, c_130])).
% 9.00/2.92  tff(c_1517, plain, (u1_struct_0(k1_tex_2('#skF_7', '#skF_8'))=u1_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_783, c_1511])).
% 9.00/2.92  tff(c_648, plain, (![A_170, B_171]: (v7_struct_0(k1_tex_2(A_170, B_171)) | ~m1_subset_1(B_171, u1_struct_0(A_170)) | ~l1_pre_topc(A_170) | v2_struct_0(A_170))), inference(cnfTransformation, [status(thm)], [f_154])).
% 9.00/2.92  tff(c_651, plain, (v7_struct_0(k1_tex_2('#skF_7', '#skF_8')) | ~l1_pre_topc('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_86, c_648])).
% 9.00/2.92  tff(c_654, plain, (v7_struct_0(k1_tex_2('#skF_7', '#skF_8')) | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_651])).
% 9.00/2.92  tff(c_655, plain, (v7_struct_0(k1_tex_2('#skF_7', '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_90, c_654])).
% 9.00/2.92  tff(c_82, plain, (![A_56, B_58]: (v1_subset_1(k6_domain_1(A_56, B_58), A_56) | ~m1_subset_1(B_58, A_56) | v1_zfmisc_1(A_56) | v1_xboole_0(A_56))), inference(cnfTransformation, [status(thm)], [f_201])).
% 9.00/2.92  tff(c_1125, plain, (![A_220, B_221]: (~v7_struct_0(A_220) | ~v1_subset_1(k6_domain_1(u1_struct_0(A_220), B_221), u1_struct_0(A_220)) | ~m1_subset_1(B_221, u1_struct_0(A_220)) | ~l1_struct_0(A_220) | v2_struct_0(A_220))), inference(cnfTransformation, [status(thm)], [f_214])).
% 9.00/2.92  tff(c_2007, plain, (![A_293, B_294]: (~v7_struct_0(A_293) | ~l1_struct_0(A_293) | v2_struct_0(A_293) | ~m1_subset_1(B_294, u1_struct_0(A_293)) | v1_zfmisc_1(u1_struct_0(A_293)) | v1_xboole_0(u1_struct_0(A_293)))), inference(resolution, [status(thm)], [c_82, c_1125])).
% 9.00/2.92  tff(c_2010, plain, (![B_294]: (~v7_struct_0(k1_tex_2('#skF_7', '#skF_8')) | ~l1_struct_0(k1_tex_2('#skF_7', '#skF_8')) | v2_struct_0(k1_tex_2('#skF_7', '#skF_8')) | ~m1_subset_1(B_294, u1_struct_0('#skF_7')) | v1_zfmisc_1(u1_struct_0(k1_tex_2('#skF_7', '#skF_8'))) | v1_xboole_0(u1_struct_0(k1_tex_2('#skF_7', '#skF_8'))))), inference(superposition, [status(thm), theory('equality')], [c_1517, c_2007])).
% 9.00/2.92  tff(c_2015, plain, (![B_294]: (~l1_struct_0(k1_tex_2('#skF_7', '#skF_8')) | v2_struct_0(k1_tex_2('#skF_7', '#skF_8')) | ~m1_subset_1(B_294, u1_struct_0('#skF_7')) | v1_zfmisc_1(u1_struct_0('#skF_7')) | v1_xboole_0(u1_struct_0('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_1517, c_1517, c_655, c_2010])).
% 9.00/2.92  tff(c_2016, plain, (![B_294]: (~l1_struct_0(k1_tex_2('#skF_7', '#skF_8')) | ~m1_subset_1(B_294, u1_struct_0('#skF_7')))), inference(negUnitSimplification, [status(thm)], [c_468, c_464, c_480, c_2015])).
% 9.00/2.92  tff(c_2021, plain, (~l1_struct_0(k1_tex_2('#skF_7', '#skF_8'))), inference(splitLeft, [status(thm)], [c_2016])).
% 9.00/2.92  tff(c_2024, plain, (~l1_pre_topc(k1_tex_2('#skF_7', '#skF_8'))), inference(resolution, [status(thm)], [c_38, c_2021])).
% 9.00/2.92  tff(c_2028, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_789, c_2024])).
% 9.00/2.92  tff(c_2029, plain, (![B_294]: (~m1_subset_1(B_294, u1_struct_0('#skF_7')))), inference(splitRight, [status(thm)], [c_2016])).
% 9.00/2.92  tff(c_2038, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2029, c_86])).
% 9.00/2.92  tff(c_2039, plain, (v1_xboole_0(u1_struct_0('#skF_7'))), inference(splitRight, [status(thm)], [c_463])).
% 9.00/2.92  tff(c_44, plain, (![A_29]: (~v1_xboole_0(u1_struct_0(A_29)) | ~l1_struct_0(A_29) | v2_struct_0(A_29))), inference(cnfTransformation, [status(thm)], [f_91])).
% 9.00/2.92  tff(c_2063, plain, (~l1_struct_0('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_2039, c_44])).
% 9.00/2.92  tff(c_2069, plain, (~l1_struct_0('#skF_7')), inference(negUnitSimplification, [status(thm)], [c_90, c_2063])).
% 9.00/2.92  tff(c_2072, plain, (~l1_pre_topc('#skF_7')), inference(resolution, [status(thm)], [c_38, c_2069])).
% 9.00/2.92  tff(c_2076, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_88, c_2072])).
% 9.00/2.92  tff(c_2077, plain, (~v1_subset_1(k6_domain_1(u1_struct_0('#skF_7'), '#skF_8'), u1_struct_0('#skF_7'))), inference(splitRight, [status(thm)], [c_92])).
% 9.00/2.92  tff(c_2097, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_113, c_2077])).
% 9.00/2.92  tff(c_2098, plain, (v1_tex_2(k1_tex_2('#skF_7', '#skF_8'), '#skF_7')), inference(splitRight, [status(thm)], [c_98])).
% 9.00/2.92  tff(c_2581, plain, (![A_393, B_394]: (v1_subset_1(k6_domain_1(A_393, B_394), A_393) | ~m1_subset_1(B_394, A_393) | v1_zfmisc_1(A_393) | v1_xboole_0(A_393))), inference(cnfTransformation, [status(thm)], [f_201])).
% 9.00/2.92  tff(c_2099, plain, (~v1_subset_1(k6_domain_1(u1_struct_0('#skF_7'), '#skF_8'), u1_struct_0('#skF_7'))), inference(splitRight, [status(thm)], [c_98])).
% 9.00/2.92  tff(c_2590, plain, (~m1_subset_1('#skF_8', u1_struct_0('#skF_7')) | v1_zfmisc_1(u1_struct_0('#skF_7')) | v1_xboole_0(u1_struct_0('#skF_7'))), inference(resolution, [status(thm)], [c_2581, c_2099])).
% 9.00/2.92  tff(c_2595, plain, (v1_zfmisc_1(u1_struct_0('#skF_7')) | v1_xboole_0(u1_struct_0('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_2590])).
% 9.00/2.92  tff(c_2596, plain, (v1_xboole_0(u1_struct_0('#skF_7'))), inference(splitLeft, [status(thm)], [c_2595])).
% 9.00/2.92  tff(c_2605, plain, (~l1_struct_0('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_2596, c_44])).
% 9.00/2.92  tff(c_2611, plain, (~l1_struct_0('#skF_7')), inference(negUnitSimplification, [status(thm)], [c_90, c_2605])).
% 9.00/2.92  tff(c_2614, plain, (~l1_pre_topc('#skF_7')), inference(resolution, [status(thm)], [c_38, c_2611])).
% 9.00/2.92  tff(c_2618, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_88, c_2614])).
% 9.00/2.92  tff(c_2620, plain, (~v1_xboole_0(u1_struct_0('#skF_7'))), inference(splitRight, [status(thm)], [c_2595])).
% 9.00/2.92  tff(c_2619, plain, (v1_zfmisc_1(u1_struct_0('#skF_7'))), inference(splitRight, [status(thm)], [c_2595])).
% 9.00/2.92  tff(c_3605, plain, (![B_466, A_467]: (v1_subset_1(u1_struct_0(B_466), u1_struct_0(A_467)) | ~v1_tex_2(B_466, A_467) | ~m1_subset_1(u1_struct_0(B_466), k1_zfmisc_1(u1_struct_0(A_467))) | ~m1_pre_topc(B_466, A_467) | ~l1_pre_topc(A_467))), inference(cnfTransformation, [status(thm)], [f_179])).
% 9.00/2.92  tff(c_3626, plain, (![B_34, A_32]: (v1_subset_1(u1_struct_0(B_34), u1_struct_0(A_32)) | ~v1_tex_2(B_34, A_32) | ~m1_pre_topc(B_34, A_32) | ~l1_pre_topc(A_32))), inference(resolution, [status(thm)], [c_50, c_3605])).
% 9.00/2.92  tff(c_2818, plain, (![B_412, A_413]: (~v1_subset_1(B_412, A_413) | v1_xboole_0(B_412) | ~m1_subset_1(B_412, k1_zfmisc_1(A_413)) | ~v1_zfmisc_1(A_413) | v1_xboole_0(A_413))), inference(cnfTransformation, [status(thm)], [f_119])).
% 9.00/2.92  tff(c_6463, plain, (![B_622, A_623]: (~v1_subset_1(u1_struct_0(B_622), u1_struct_0(A_623)) | v1_xboole_0(u1_struct_0(B_622)) | ~v1_zfmisc_1(u1_struct_0(A_623)) | v1_xboole_0(u1_struct_0(A_623)) | ~m1_pre_topc(B_622, A_623) | ~l1_pre_topc(A_623))), inference(resolution, [status(thm)], [c_50, c_2818])).
% 9.00/2.92  tff(c_7883, plain, (![B_701, A_702]: (v1_xboole_0(u1_struct_0(B_701)) | ~v1_zfmisc_1(u1_struct_0(A_702)) | v1_xboole_0(u1_struct_0(A_702)) | ~v1_tex_2(B_701, A_702) | ~m1_pre_topc(B_701, A_702) | ~l1_pre_topc(A_702))), inference(resolution, [status(thm)], [c_3626, c_6463])).
% 9.00/2.92  tff(c_7889, plain, (![B_701]: (v1_xboole_0(u1_struct_0(B_701)) | v1_xboole_0(u1_struct_0('#skF_7')) | ~v1_tex_2(B_701, '#skF_7') | ~m1_pre_topc(B_701, '#skF_7') | ~l1_pre_topc('#skF_7'))), inference(resolution, [status(thm)], [c_2619, c_7883])).
% 9.00/2.92  tff(c_7900, plain, (![B_701]: (v1_xboole_0(u1_struct_0(B_701)) | v1_xboole_0(u1_struct_0('#skF_7')) | ~v1_tex_2(B_701, '#skF_7') | ~m1_pre_topc(B_701, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_7889])).
% 9.00/2.92  tff(c_7903, plain, (![B_703]: (v1_xboole_0(u1_struct_0(B_703)) | ~v1_tex_2(B_703, '#skF_7') | ~m1_pre_topc(B_703, '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_2620, c_7900])).
% 9.00/2.92  tff(c_46, plain, (![A_30]: (v1_xboole_0('#skF_5'(A_30)) | ~l1_pre_topc(A_30))), inference(cnfTransformation, [status(thm)], [f_98])).
% 9.00/2.92  tff(c_2154, plain, (![A_325, B_326]: (r2_hidden('#skF_2'(A_325, B_326), A_325) | r1_tarski(A_325, B_326))), inference(cnfTransformation, [status(thm)], [f_38])).
% 9.00/2.92  tff(c_2163, plain, (![A_325, B_326]: (~v1_xboole_0(A_325) | r1_tarski(A_325, B_326))), inference(resolution, [status(thm)], [c_2154, c_2])).
% 9.00/2.92  tff(c_2247, plain, (![B_344, A_345]: (v1_subset_1(B_344, A_345) | B_344=A_345 | ~m1_subset_1(B_344, k1_zfmisc_1(A_345)))), inference(cnfTransformation, [status(thm)], [f_126])).
% 9.00/2.92  tff(c_2284, plain, (![A_352, B_353]: (v1_subset_1(A_352, B_353) | B_353=A_352 | ~r1_tarski(A_352, B_353))), inference(resolution, [status(thm)], [c_34, c_2247])).
% 9.00/2.92  tff(c_2214, plain, (![B_335, A_336]: (~v1_subset_1(B_335, A_336) | ~m1_subset_1(B_335, k1_zfmisc_1(A_336)) | ~v1_xboole_0(A_336))), inference(cnfTransformation, [status(thm)], [f_55])).
% 9.00/2.92  tff(c_2225, plain, (![A_19, B_20]: (~v1_subset_1(A_19, B_20) | ~v1_xboole_0(B_20) | ~r1_tarski(A_19, B_20))), inference(resolution, [status(thm)], [c_34, c_2214])).
% 9.00/2.92  tff(c_2302, plain, (![B_354, A_355]: (~v1_xboole_0(B_354) | B_354=A_355 | ~r1_tarski(A_355, B_354))), inference(resolution, [status(thm)], [c_2284, c_2225])).
% 9.00/2.92  tff(c_2320, plain, (![B_356, A_357]: (~v1_xboole_0(B_356) | B_356=A_357 | ~v1_xboole_0(A_357))), inference(resolution, [status(thm)], [c_2163, c_2302])).
% 9.00/2.92  tff(c_2331, plain, (![A_358, A_359]: (A_358='#skF_5'(A_359) | ~v1_xboole_0(A_358) | ~l1_pre_topc(A_359))), inference(resolution, [status(thm)], [c_46, c_2320])).
% 9.00/2.92  tff(c_2361, plain, (![A_364, A_363]: ('#skF_5'(A_364)='#skF_5'(A_363) | ~l1_pre_topc(A_363) | ~l1_pre_topc(A_364))), inference(resolution, [status(thm)], [c_46, c_2331])).
% 9.00/2.92  tff(c_2364, plain, (![A_364]: ('#skF_5'(A_364)='#skF_5'('#skF_7') | ~l1_pre_topc(A_364))), inference(resolution, [status(thm)], [c_88, c_2361])).
% 9.00/2.92  tff(c_2730, plain, ('#skF_5'(k1_tex_2('#skF_7', '#skF_8'))='#skF_5'('#skF_7')), inference(resolution, [status(thm)], [c_2721, c_2364])).
% 9.00/2.92  tff(c_2200, plain, (![A_333]: (m1_subset_1('#skF_5'(A_333), k1_zfmisc_1(u1_struct_0(A_333))) | ~l1_pre_topc(A_333))), inference(cnfTransformation, [status(thm)], [f_98])).
% 9.00/2.92  tff(c_32, plain, (![A_19, B_20]: (r1_tarski(A_19, B_20) | ~m1_subset_1(A_19, k1_zfmisc_1(B_20)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 9.00/2.92  tff(c_2208, plain, (![A_333]: (r1_tarski('#skF_5'(A_333), u1_struct_0(A_333)) | ~l1_pre_topc(A_333))), inference(resolution, [status(thm)], [c_2200, c_32])).
% 9.00/2.92  tff(c_10, plain, (![A_5, B_6]: (r2_hidden('#skF_2'(A_5, B_6), A_5) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 9.00/2.92  tff(c_2234, plain, (![C_341, B_342, A_343]: (r2_hidden(C_341, B_342) | ~r2_hidden(C_341, A_343) | ~r1_tarski(A_343, B_342))), inference(cnfTransformation, [status(thm)], [f_38])).
% 9.00/2.92  tff(c_2653, plain, (![A_399, B_400, B_401]: (r2_hidden('#skF_2'(A_399, B_400), B_401) | ~r1_tarski(A_399, B_401) | r1_tarski(A_399, B_400))), inference(resolution, [status(thm)], [c_10, c_2234])).
% 9.00/2.92  tff(c_2671, plain, (![B_402, A_403, B_404]: (~v1_xboole_0(B_402) | ~r1_tarski(A_403, B_402) | r1_tarski(A_403, B_404))), inference(resolution, [status(thm)], [c_2653, c_2])).
% 9.00/2.92  tff(c_2683, plain, (![A_333, B_404]: (~v1_xboole_0(u1_struct_0(A_333)) | r1_tarski('#skF_5'(A_333), B_404) | ~l1_pre_topc(A_333))), inference(resolution, [status(thm)], [c_2208, c_2671])).
% 9.00/2.92  tff(c_2735, plain, (![B_404]: (~v1_xboole_0(u1_struct_0(k1_tex_2('#skF_7', '#skF_8'))) | r1_tarski('#skF_5'('#skF_7'), B_404) | ~l1_pre_topc(k1_tex_2('#skF_7', '#skF_8')))), inference(superposition, [status(thm), theory('equality')], [c_2730, c_2683])).
% 9.00/2.92  tff(c_2760, plain, (![B_404]: (~v1_xboole_0(u1_struct_0(k1_tex_2('#skF_7', '#skF_8'))) | r1_tarski('#skF_5'('#skF_7'), B_404))), inference(demodulation, [status(thm), theory('equality')], [c_2721, c_2735])).
% 9.00/2.92  tff(c_2858, plain, (~v1_xboole_0(u1_struct_0(k1_tex_2('#skF_7', '#skF_8')))), inference(splitLeft, [status(thm)], [c_2760])).
% 9.00/2.92  tff(c_7921, plain, (~v1_tex_2(k1_tex_2('#skF_7', '#skF_8'), '#skF_7') | ~m1_pre_topc(k1_tex_2('#skF_7', '#skF_8'), '#skF_7')), inference(resolution, [status(thm)], [c_7903, c_2858])).
% 9.00/2.92  tff(c_7947, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2710, c_2098, c_7921])).
% 9.00/2.92  tff(c_7949, plain, (v1_xboole_0(u1_struct_0(k1_tex_2('#skF_7', '#skF_8')))), inference(splitRight, [status(thm)], [c_2760])).
% 9.00/2.92  tff(c_7981, plain, (~l1_struct_0(k1_tex_2('#skF_7', '#skF_8')) | v2_struct_0(k1_tex_2('#skF_7', '#skF_8'))), inference(resolution, [status(thm)], [c_7949, c_44])).
% 9.00/2.92  tff(c_7988, plain, (~l1_struct_0(k1_tex_2('#skF_7', '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_2566, c_7981])).
% 9.00/2.92  tff(c_7991, plain, (~l1_pre_topc(k1_tex_2('#skF_7', '#skF_8'))), inference(resolution, [status(thm)], [c_38, c_7988])).
% 9.00/2.92  tff(c_7995, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2721, c_7991])).
% 9.00/2.92  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.00/2.92  
% 9.00/2.92  Inference rules
% 9.00/2.92  ----------------------
% 9.00/2.92  #Ref     : 0
% 9.00/2.92  #Sup     : 1775
% 9.00/2.92  #Fact    : 14
% 9.00/2.92  #Define  : 0
% 9.00/2.92  #Split   : 21
% 9.00/2.92  #Chain   : 0
% 9.00/2.92  #Close   : 0
% 9.00/2.92  
% 9.00/2.92  Ordering : KBO
% 9.00/2.92  
% 9.00/2.92  Simplification rules
% 9.00/2.92  ----------------------
% 9.00/2.92  #Subsume      : 708
% 9.00/2.92  #Demod        : 497
% 9.00/2.92  #Tautology    : 416
% 9.00/2.92  #SimpNegUnit  : 246
% 9.00/2.92  #BackRed      : 32
% 9.00/2.92  
% 9.00/2.92  #Partial instantiations: 0
% 9.00/2.92  #Strategies tried      : 1
% 9.00/2.92  
% 9.00/2.92  Timing (in seconds)
% 9.00/2.92  ----------------------
% 9.00/2.92  Preprocessing        : 0.36
% 9.00/2.92  Parsing              : 0.19
% 9.00/2.92  CNF conversion       : 0.03
% 9.00/2.92  Main loop            : 1.76
% 9.00/2.92  Inferencing          : 0.61
% 9.00/2.92  Reduction            : 0.48
% 9.00/2.92  Demodulation         : 0.31
% 9.00/2.92  BG Simplification    : 0.06
% 9.00/2.92  Subsumption          : 0.46
% 9.00/2.92  Abstraction          : 0.08
% 9.00/2.92  MUC search           : 0.00
% 9.00/2.92  Cooper               : 0.00
% 9.00/2.92  Total                : 2.18
% 9.00/2.92  Index Insertion      : 0.00
% 9.00/2.92  Index Deletion       : 0.00
% 9.00/2.92  Index Matching       : 0.00
% 9.00/2.92  BG Taut test         : 0.00
%------------------------------------------------------------------------------
