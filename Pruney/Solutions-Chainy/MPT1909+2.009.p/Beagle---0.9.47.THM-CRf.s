%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:38 EST 2020

% Result     : Theorem 6.75s
% Output     : CNFRefutation 6.75s
% Verified   : 
% Statistics : Number of formulae       :  145 ( 369 expanded)
%              Number of leaves         :   50 ( 157 expanded)
%              Depth                    :   16
%              Number of atoms          :  364 (1880 expanded)
%              Number of equality atoms :   21 ( 200 expanded)
%              Maximal formula depth    :   20 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_pre_topc > v3_borsuk_1 > v1_funct_2 > v4_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_pre_topc > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k8_relset_1 > k2_enumset1 > k1_enumset1 > k6_domain_1 > k2_zfmisc_1 > k2_tarski > k2_pre_topc > k1_connsp_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v3_borsuk_1,type,(
    v3_borsuk_1: ( $i * $i * $i ) > $o )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_connsp_2,type,(
    k1_connsp_2: ( $i * $i ) > $i )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(v4_tex_2,type,(
    v4_tex_2: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v3_tdlat_3,type,(
    v3_tdlat_3: $i > $o )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v5_pre_topc,type,(
    v5_pre_topc: ( $i * $i * $i ) > $o )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_194,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & v3_tdlat_3(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & v4_tex_2(B,A)
              & m1_pre_topc(B,A) )
           => ! [C] :
                ( ( v1_funct_1(C)
                  & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                  & v5_pre_topc(C,A,B)
                  & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
               => ( v3_borsuk_1(C,A,B)
                 => ! [D] :
                      ( m1_subset_1(D,u1_struct_0(B))
                     => ! [E] :
                          ( m1_subset_1(E,u1_struct_0(A))
                         => ( D = E
                           => k8_relset_1(u1_struct_0(A),u1_struct_0(B),C,k6_domain_1(u1_struct_0(B),D)) = k2_pre_topc(A,k6_domain_1(u1_struct_0(A),E)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_tex_2)).

tff(f_70,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_77,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_117,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => r2_hidden(B,k1_connsp_2(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_connsp_2)).

tff(f_105,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => m1_subset_1(k1_connsp_2(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_connsp_2)).

tff(f_54,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_50,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(k1_tarski(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_subset_1)).

tff(f_87,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(B)))
             => m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_pre_topc)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_155,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & v3_tdlat_3(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v4_tex_2(B,A)
            & m1_pre_topc(B,A) )
         => ! [C] :
              ( ( v1_funct_1(C)
                & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                & v5_pre_topc(C,A,B)
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
             => ( v3_borsuk_1(C,A,B)
               => ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(B)))
                   => ! [E] :
                        ( m1_subset_1(E,k1_zfmisc_1(u1_struct_0(A)))
                       => ( D = E
                         => k8_relset_1(u1_struct_0(A),u1_struct_0(B),C,D) = k2_pre_topc(A,E) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_tex_2)).

tff(f_94,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(c_46,plain,(
    '#skF_5' = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_50,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_75,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_50])).

tff(c_66,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_72,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_68,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_62,plain,(
    m1_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_134,plain,(
    ! [B_139,A_140] :
      ( v2_pre_topc(B_139)
      | ~ m1_pre_topc(B_139,A_140)
      | ~ l1_pre_topc(A_140)
      | ~ v2_pre_topc(A_140) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_137,plain,
    ( v2_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_62,c_134])).

tff(c_140,plain,(
    v2_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_68,c_137])).

tff(c_105,plain,(
    ! [B_125,A_126] :
      ( l1_pre_topc(B_125)
      | ~ m1_pre_topc(B_125,A_126)
      | ~ l1_pre_topc(A_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_108,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_62,c_105])).

tff(c_111,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_108])).

tff(c_40,plain,(
    ! [B_60,A_58] :
      ( r2_hidden(B_60,k1_connsp_2(A_58,B_60))
      | ~ m1_subset_1(B_60,u1_struct_0(A_58))
      | ~ l1_pre_topc(A_58)
      | ~ v2_pre_topc(A_58)
      | v2_struct_0(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_2016,plain,(
    ! [A_479,B_480] :
      ( m1_subset_1(k1_connsp_2(A_479,B_480),k1_zfmisc_1(u1_struct_0(A_479)))
      | ~ m1_subset_1(B_480,u1_struct_0(A_479))
      | ~ l1_pre_topc(A_479)
      | ~ v2_pre_topc(A_479)
      | v2_struct_0(A_479) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_24,plain,(
    ! [A_36,B_37] :
      ( r1_tarski(A_36,B_37)
      | ~ m1_subset_1(A_36,k1_zfmisc_1(B_37)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_2030,plain,(
    ! [A_479,B_480] :
      ( r1_tarski(k1_connsp_2(A_479,B_480),u1_struct_0(A_479))
      | ~ m1_subset_1(B_480,u1_struct_0(A_479))
      | ~ l1_pre_topc(A_479)
      | ~ v2_pre_topc(A_479)
      | v2_struct_0(A_479) ) ),
    inference(resolution,[status(thm)],[c_2016,c_24])).

tff(c_117,plain,(
    ! [A_129,B_130] :
      ( m1_subset_1(k1_tarski(A_129),k1_zfmisc_1(B_130))
      | ~ r2_hidden(A_129,B_130) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_121,plain,(
    ! [A_129,B_130] :
      ( r1_tarski(k1_tarski(A_129),B_130)
      | ~ r2_hidden(A_129,B_130) ) ),
    inference(resolution,[status(thm)],[c_117,c_24])).

tff(c_26,plain,(
    ! [A_36,B_37] :
      ( m1_subset_1(A_36,k1_zfmisc_1(B_37))
      | ~ r1_tarski(A_36,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_1773,plain,(
    ! [C_431,A_432,B_433] :
      ( m1_subset_1(C_431,k1_zfmisc_1(u1_struct_0(A_432)))
      | ~ m1_subset_1(C_431,k1_zfmisc_1(u1_struct_0(B_433)))
      | ~ m1_pre_topc(B_433,A_432)
      | ~ l1_pre_topc(A_432) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_1782,plain,(
    ! [A_434,A_435,B_436] :
      ( m1_subset_1(A_434,k1_zfmisc_1(u1_struct_0(A_435)))
      | ~ m1_pre_topc(B_436,A_435)
      | ~ l1_pre_topc(A_435)
      | ~ r1_tarski(A_434,u1_struct_0(B_436)) ) ),
    inference(resolution,[status(thm)],[c_26,c_1773])).

tff(c_1784,plain,(
    ! [A_434] :
      ( m1_subset_1(A_434,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ r1_tarski(A_434,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_62,c_1782])).

tff(c_1788,plain,(
    ! [A_437] :
      ( m1_subset_1(A_437,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ r1_tarski(A_437,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_1784])).

tff(c_1803,plain,(
    ! [A_438] :
      ( r1_tarski(A_438,u1_struct_0('#skF_2'))
      | ~ r1_tarski(A_438,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_1788,c_24])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_130,plain,(
    ! [C_136,B_137,A_138] :
      ( r2_hidden(C_136,B_137)
      | ~ r2_hidden(C_136,A_138)
      | ~ r1_tarski(A_138,B_137) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1684,plain,(
    ! [A_407,B_408,B_409] :
      ( r2_hidden('#skF_1'(A_407,B_408),B_409)
      | ~ r1_tarski(A_407,B_409)
      | r1_tarski(A_407,B_408) ) ),
    inference(resolution,[status(thm)],[c_6,c_130])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1701,plain,(
    ! [A_407,B_408,B_2,B_409] :
      ( r2_hidden('#skF_1'(A_407,B_408),B_2)
      | ~ r1_tarski(B_409,B_2)
      | ~ r1_tarski(A_407,B_409)
      | r1_tarski(A_407,B_408) ) ),
    inference(resolution,[status(thm)],[c_1684,c_2])).

tff(c_2087,plain,(
    ! [A_486,B_487,A_488] :
      ( r2_hidden('#skF_1'(A_486,B_487),u1_struct_0('#skF_2'))
      | ~ r1_tarski(A_486,A_488)
      | r1_tarski(A_486,B_487)
      | ~ r1_tarski(A_488,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_1803,c_1701])).

tff(c_2812,plain,(
    ! [A_571,B_572,B_573] :
      ( r2_hidden('#skF_1'(k1_tarski(A_571),B_572),u1_struct_0('#skF_2'))
      | r1_tarski(k1_tarski(A_571),B_572)
      | ~ r1_tarski(B_573,u1_struct_0('#skF_3'))
      | ~ r2_hidden(A_571,B_573) ) ),
    inference(resolution,[status(thm)],[c_121,c_2087])).

tff(c_2818,plain,(
    ! [A_571,B_572,B_480] :
      ( r2_hidden('#skF_1'(k1_tarski(A_571),B_572),u1_struct_0('#skF_2'))
      | r1_tarski(k1_tarski(A_571),B_572)
      | ~ r2_hidden(A_571,k1_connsp_2('#skF_3',B_480))
      | ~ m1_subset_1(B_480,u1_struct_0('#skF_3'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_2030,c_2812])).

tff(c_2839,plain,(
    ! [A_571,B_572,B_480] :
      ( r2_hidden('#skF_1'(k1_tarski(A_571),B_572),u1_struct_0('#skF_2'))
      | r1_tarski(k1_tarski(A_571),B_572)
      | ~ r2_hidden(A_571,k1_connsp_2('#skF_3',B_480))
      | ~ m1_subset_1(B_480,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_111,c_2818])).

tff(c_2850,plain,(
    ! [A_574,B_575,B_576] :
      ( r2_hidden('#skF_1'(k1_tarski(A_574),B_575),u1_struct_0('#skF_2'))
      | r1_tarski(k1_tarski(A_574),B_575)
      | ~ r2_hidden(A_574,k1_connsp_2('#skF_3',B_576))
      | ~ m1_subset_1(B_576,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_2839])).

tff(c_2859,plain,(
    ! [B_60,B_575] :
      ( r2_hidden('#skF_1'(k1_tarski(B_60),B_575),u1_struct_0('#skF_2'))
      | r1_tarski(k1_tarski(B_60),B_575)
      | ~ m1_subset_1(B_60,u1_struct_0('#skF_3'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_40,c_2850])).

tff(c_2870,plain,(
    ! [B_60,B_575] :
      ( r2_hidden('#skF_1'(k1_tarski(B_60),B_575),u1_struct_0('#skF_2'))
      | r1_tarski(k1_tarski(B_60),B_575)
      | ~ m1_subset_1(B_60,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_111,c_2859])).

tff(c_2874,plain,(
    ! [B_577,B_578] :
      ( r2_hidden('#skF_1'(k1_tarski(B_577),B_578),u1_struct_0('#skF_2'))
      | r1_tarski(k1_tarski(B_577),B_578)
      | ~ m1_subset_1(B_577,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_2870])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_2894,plain,(
    ! [B_577] :
      ( r1_tarski(k1_tarski(B_577),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_577,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_2874,c_4])).

tff(c_1912,plain,(
    ! [B_456,A_457] :
      ( r2_hidden(B_456,k1_connsp_2(A_457,B_456))
      | ~ m1_subset_1(B_456,u1_struct_0(A_457))
      | ~ l1_pre_topc(A_457)
      | ~ v2_pre_topc(A_457)
      | v2_struct_0(A_457) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_2332,plain,(
    ! [B_510,B_511,A_512] :
      ( r2_hidden(B_510,B_511)
      | ~ r1_tarski(k1_connsp_2(A_512,B_510),B_511)
      | ~ m1_subset_1(B_510,u1_struct_0(A_512))
      | ~ l1_pre_topc(A_512)
      | ~ v2_pre_topc(A_512)
      | v2_struct_0(A_512) ) ),
    inference(resolution,[status(thm)],[c_1912,c_2])).

tff(c_2359,plain,(
    ! [B_480,A_479] :
      ( r2_hidden(B_480,u1_struct_0(A_479))
      | ~ m1_subset_1(B_480,u1_struct_0(A_479))
      | ~ l1_pre_topc(A_479)
      | ~ v2_pre_topc(A_479)
      | v2_struct_0(A_479) ) ),
    inference(resolution,[status(thm)],[c_2030,c_2332])).

tff(c_74,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_70,plain,(
    v3_tdlat_3('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_64,plain,(
    v4_tex_2('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_60,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_58,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_56,plain,(
    v5_pre_topc('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_52,plain,(
    v3_borsuk_1('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_54,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_2140,plain,(
    ! [A_491,B_492,C_493,E_494] :
      ( k8_relset_1(u1_struct_0(A_491),u1_struct_0(B_492),C_493,E_494) = k2_pre_topc(A_491,E_494)
      | ~ m1_subset_1(E_494,k1_zfmisc_1(u1_struct_0(A_491)))
      | ~ m1_subset_1(E_494,k1_zfmisc_1(u1_struct_0(B_492)))
      | ~ v3_borsuk_1(C_493,A_491,B_492)
      | ~ m1_subset_1(C_493,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_491),u1_struct_0(B_492))))
      | ~ v5_pre_topc(C_493,A_491,B_492)
      | ~ v1_funct_2(C_493,u1_struct_0(A_491),u1_struct_0(B_492))
      | ~ v1_funct_1(C_493)
      | ~ m1_pre_topc(B_492,A_491)
      | ~ v4_tex_2(B_492,A_491)
      | v2_struct_0(B_492)
      | ~ l1_pre_topc(A_491)
      | ~ v3_tdlat_3(A_491)
      | ~ v2_pre_topc(A_491)
      | v2_struct_0(A_491) ) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_2764,plain,(
    ! [A_564,B_565,C_566,A_567] :
      ( k8_relset_1(u1_struct_0(A_564),u1_struct_0(B_565),C_566,A_567) = k2_pre_topc(A_564,A_567)
      | ~ m1_subset_1(A_567,k1_zfmisc_1(u1_struct_0(B_565)))
      | ~ v3_borsuk_1(C_566,A_564,B_565)
      | ~ m1_subset_1(C_566,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_564),u1_struct_0(B_565))))
      | ~ v5_pre_topc(C_566,A_564,B_565)
      | ~ v1_funct_2(C_566,u1_struct_0(A_564),u1_struct_0(B_565))
      | ~ v1_funct_1(C_566)
      | ~ m1_pre_topc(B_565,A_564)
      | ~ v4_tex_2(B_565,A_564)
      | v2_struct_0(B_565)
      | ~ l1_pre_topc(A_564)
      | ~ v3_tdlat_3(A_564)
      | ~ v2_pre_topc(A_564)
      | v2_struct_0(A_564)
      | ~ r1_tarski(A_567,u1_struct_0(A_564)) ) ),
    inference(resolution,[status(thm)],[c_26,c_2140])).

tff(c_4136,plain,(
    ! [A_730,B_731,C_732,A_733] :
      ( k8_relset_1(u1_struct_0(A_730),u1_struct_0(B_731),C_732,A_733) = k2_pre_topc(A_730,A_733)
      | ~ v3_borsuk_1(C_732,A_730,B_731)
      | ~ m1_subset_1(C_732,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_730),u1_struct_0(B_731))))
      | ~ v5_pre_topc(C_732,A_730,B_731)
      | ~ v1_funct_2(C_732,u1_struct_0(A_730),u1_struct_0(B_731))
      | ~ v1_funct_1(C_732)
      | ~ m1_pre_topc(B_731,A_730)
      | ~ v4_tex_2(B_731,A_730)
      | v2_struct_0(B_731)
      | ~ l1_pre_topc(A_730)
      | ~ v3_tdlat_3(A_730)
      | ~ v2_pre_topc(A_730)
      | v2_struct_0(A_730)
      | ~ r1_tarski(A_733,u1_struct_0(A_730))
      | ~ r1_tarski(A_733,u1_struct_0(B_731)) ) ),
    inference(resolution,[status(thm)],[c_26,c_2764])).

tff(c_4141,plain,(
    ! [A_733] :
      ( k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4',A_733) = k2_pre_topc('#skF_2',A_733)
      | ~ v3_borsuk_1('#skF_4','#skF_2','#skF_3')
      | ~ v5_pre_topc('#skF_4','#skF_2','#skF_3')
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_4')
      | ~ m1_pre_topc('#skF_3','#skF_2')
      | ~ v4_tex_2('#skF_3','#skF_2')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | ~ v3_tdlat_3('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ r1_tarski(A_733,u1_struct_0('#skF_2'))
      | ~ r1_tarski(A_733,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_54,c_4136])).

tff(c_4148,plain,(
    ! [A_733] :
      ( k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4',A_733) = k2_pre_topc('#skF_2',A_733)
      | v2_struct_0('#skF_3')
      | v2_struct_0('#skF_2')
      | ~ r1_tarski(A_733,u1_struct_0('#skF_2'))
      | ~ r1_tarski(A_733,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_68,c_64,c_62,c_60,c_58,c_56,c_52,c_4141])).

tff(c_4151,plain,(
    ! [A_734] :
      ( k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4',A_734) = k2_pre_topc('#skF_2',A_734)
      | ~ r1_tarski(A_734,u1_struct_0('#skF_2'))
      | ~ r1_tarski(A_734,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_66,c_4148])).

tff(c_188,plain,(
    ! [A_161,B_162] :
      ( k6_domain_1(A_161,B_162) = k1_tarski(B_162)
      | ~ m1_subset_1(B_162,A_161)
      | v1_xboole_0(A_161) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_208,plain,
    ( k6_domain_1(u1_struct_0('#skF_3'),'#skF_6') = k1_tarski('#skF_6')
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_75,c_188])).

tff(c_907,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_208])).

tff(c_1277,plain,(
    ! [A_359,B_360] :
      ( m1_subset_1(k1_connsp_2(A_359,B_360),k1_zfmisc_1(u1_struct_0(A_359)))
      | ~ m1_subset_1(B_360,u1_struct_0(A_359))
      | ~ l1_pre_topc(A_359)
      | ~ v2_pre_topc(A_359)
      | v2_struct_0(A_359) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_1291,plain,(
    ! [A_359,B_360] :
      ( r1_tarski(k1_connsp_2(A_359,B_360),u1_struct_0(A_359))
      | ~ m1_subset_1(B_360,u1_struct_0(A_359))
      | ~ l1_pre_topc(A_359)
      | ~ v2_pre_topc(A_359)
      | v2_struct_0(A_359) ) ),
    inference(resolution,[status(thm)],[c_1277,c_24])).

tff(c_1090,plain,(
    ! [B_323,A_324] :
      ( r2_hidden(B_323,k1_connsp_2(A_324,B_323))
      | ~ m1_subset_1(B_323,u1_struct_0(A_324))
      | ~ l1_pre_topc(A_324)
      | ~ v2_pre_topc(A_324)
      | v2_struct_0(A_324) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_141,plain,(
    ! [C_141,B_142,A_143] :
      ( ~ v1_xboole_0(C_141)
      | ~ m1_subset_1(B_142,k1_zfmisc_1(C_141))
      | ~ r2_hidden(A_143,B_142) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_150,plain,(
    ! [B_37,A_143,A_36] :
      ( ~ v1_xboole_0(B_37)
      | ~ r2_hidden(A_143,A_36)
      | ~ r1_tarski(A_36,B_37) ) ),
    inference(resolution,[status(thm)],[c_26,c_141])).

tff(c_1588,plain,(
    ! [B_395,A_396,B_397] :
      ( ~ v1_xboole_0(B_395)
      | ~ r1_tarski(k1_connsp_2(A_396,B_397),B_395)
      | ~ m1_subset_1(B_397,u1_struct_0(A_396))
      | ~ l1_pre_topc(A_396)
      | ~ v2_pre_topc(A_396)
      | v2_struct_0(A_396) ) ),
    inference(resolution,[status(thm)],[c_1090,c_150])).

tff(c_1652,plain,(
    ! [A_401,B_402] :
      ( ~ v1_xboole_0(u1_struct_0(A_401))
      | ~ m1_subset_1(B_402,u1_struct_0(A_401))
      | ~ l1_pre_topc(A_401)
      | ~ v2_pre_topc(A_401)
      | v2_struct_0(A_401) ) ),
    inference(resolution,[status(thm)],[c_1291,c_1588])).

tff(c_1658,plain,
    ( ~ v1_xboole_0(u1_struct_0('#skF_3'))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_75,c_1652])).

tff(c_1665,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_111,c_907,c_1658])).

tff(c_1667,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_1665])).

tff(c_1668,plain,(
    k6_domain_1(u1_struct_0('#skF_3'),'#skF_6') = k1_tarski('#skF_6') ),
    inference(splitRight,[status(thm)],[c_208])).

tff(c_48,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_207,plain,
    ( k6_domain_1(u1_struct_0('#skF_2'),'#skF_6') = k1_tarski('#skF_6')
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_48,c_188])).

tff(c_209,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_207])).

tff(c_391,plain,(
    ! [A_209,B_210] :
      ( m1_subset_1(k1_connsp_2(A_209,B_210),k1_zfmisc_1(u1_struct_0(A_209)))
      | ~ m1_subset_1(B_210,u1_struct_0(A_209))
      | ~ l1_pre_topc(A_209)
      | ~ v2_pre_topc(A_209)
      | v2_struct_0(A_209) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_28,plain,(
    ! [C_40,B_39,A_38] :
      ( ~ v1_xboole_0(C_40)
      | ~ m1_subset_1(B_39,k1_zfmisc_1(C_40))
      | ~ r2_hidden(A_38,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_798,plain,(
    ! [A_269,A_270,B_271] :
      ( ~ v1_xboole_0(u1_struct_0(A_269))
      | ~ r2_hidden(A_270,k1_connsp_2(A_269,B_271))
      | ~ m1_subset_1(B_271,u1_struct_0(A_269))
      | ~ l1_pre_topc(A_269)
      | ~ v2_pre_topc(A_269)
      | v2_struct_0(A_269) ) ),
    inference(resolution,[status(thm)],[c_391,c_28])).

tff(c_888,plain,(
    ! [A_280,B_281] :
      ( ~ v1_xboole_0(u1_struct_0(A_280))
      | ~ m1_subset_1(B_281,u1_struct_0(A_280))
      | ~ l1_pre_topc(A_280)
      | ~ v2_pre_topc(A_280)
      | v2_struct_0(A_280) ) ),
    inference(resolution,[status(thm)],[c_40,c_798])).

tff(c_891,plain,
    ( ~ v1_xboole_0(u1_struct_0('#skF_2'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_888])).

tff(c_897,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_68,c_209,c_891])).

tff(c_899,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_897])).

tff(c_900,plain,(
    k6_domain_1(u1_struct_0('#skF_2'),'#skF_6') = k1_tarski('#skF_6') ),
    inference(splitRight,[status(thm)],[c_207])).

tff(c_44,plain,(
    k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4',k6_domain_1(u1_struct_0('#skF_3'),'#skF_5')) != k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_76,plain,(
    k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4',k6_domain_1(u1_struct_0('#skF_3'),'#skF_6')) != k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44])).

tff(c_902,plain,(
    k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4',k6_domain_1(u1_struct_0('#skF_3'),'#skF_6')) != k2_pre_topc('#skF_2',k1_tarski('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_900,c_76])).

tff(c_1759,plain,(
    k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4',k1_tarski('#skF_6')) != k2_pre_topc('#skF_2',k1_tarski('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1668,c_902])).

tff(c_4162,plain,
    ( ~ r1_tarski(k1_tarski('#skF_6'),u1_struct_0('#skF_2'))
    | ~ r1_tarski(k1_tarski('#skF_6'),u1_struct_0('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_4151,c_1759])).

tff(c_4164,plain,(
    ~ r1_tarski(k1_tarski('#skF_6'),u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_4162])).

tff(c_4178,plain,(
    ~ r2_hidden('#skF_6',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_121,c_4164])).

tff(c_4205,plain,
    ( ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3'))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_2359,c_4178])).

tff(c_4211,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_111,c_75,c_4205])).

tff(c_4213,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_4211])).

tff(c_4214,plain,(
    ~ r1_tarski(k1_tarski('#skF_6'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_4162])).

tff(c_4221,plain,(
    ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_2894,c_4214])).

tff(c_4241,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_4221])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:11:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.75/2.39  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.75/2.40  
% 6.75/2.40  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.75/2.41  %$ v5_pre_topc > v3_borsuk_1 > v1_funct_2 > v4_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_pre_topc > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k8_relset_1 > k2_enumset1 > k1_enumset1 > k6_domain_1 > k2_zfmisc_1 > k2_tarski > k2_pre_topc > k1_connsp_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 6.75/2.41  
% 6.75/2.41  %Foreground sorts:
% 6.75/2.41  
% 6.75/2.41  
% 6.75/2.41  %Background operators:
% 6.75/2.41  
% 6.75/2.41  
% 6.75/2.41  %Foreground operators:
% 6.75/2.41  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 6.75/2.41  tff(v3_borsuk_1, type, v3_borsuk_1: ($i * $i * $i) > $o).
% 6.75/2.41  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.75/2.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.75/2.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.75/2.41  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.75/2.41  tff(k1_connsp_2, type, k1_connsp_2: ($i * $i) > $i).
% 6.75/2.41  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 6.75/2.41  tff(v4_tex_2, type, v4_tex_2: ($i * $i) > $o).
% 6.75/2.41  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 6.75/2.41  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 6.75/2.41  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 6.75/2.41  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.75/2.41  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.75/2.41  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.75/2.41  tff('#skF_5', type, '#skF_5': $i).
% 6.75/2.41  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.75/2.41  tff('#skF_6', type, '#skF_6': $i).
% 6.75/2.41  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.75/2.41  tff('#skF_2', type, '#skF_2': $i).
% 6.75/2.41  tff('#skF_3', type, '#skF_3': $i).
% 6.75/2.41  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 6.75/2.41  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.75/2.41  tff(v3_tdlat_3, type, v3_tdlat_3: $i > $o).
% 6.75/2.41  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 6.75/2.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.75/2.41  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.75/2.41  tff('#skF_4', type, '#skF_4': $i).
% 6.75/2.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.75/2.41  tff(v5_pre_topc, type, v5_pre_topc: ($i * $i * $i) > $o).
% 6.75/2.41  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 6.75/2.41  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 6.75/2.41  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 6.75/2.41  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 6.75/2.41  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 6.75/2.41  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.75/2.41  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 6.75/2.41  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.75/2.41  
% 6.75/2.43  tff(f_194, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v4_tex_2(B, A)) & m1_pre_topc(B, A)) => (![C]: ((((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & v5_pre_topc(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (v3_borsuk_1(C, A, B) => (![D]: (m1_subset_1(D, u1_struct_0(B)) => (![E]: (m1_subset_1(E, u1_struct_0(A)) => ((D = E) => (k8_relset_1(u1_struct_0(A), u1_struct_0(B), C, k6_domain_1(u1_struct_0(B), D)) = k2_pre_topc(A, k6_domain_1(u1_struct_0(A), E))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_tex_2)).
% 6.75/2.43  tff(f_70, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_pre_topc)).
% 6.75/2.43  tff(f_77, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 6.75/2.43  tff(f_117, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => r2_hidden(B, k1_connsp_2(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_connsp_2)).
% 6.75/2.43  tff(f_105, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => m1_subset_1(k1_connsp_2(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_connsp_2)).
% 6.75/2.43  tff(f_54, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 6.75/2.43  tff(f_50, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(k1_tarski(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_subset_1)).
% 6.75/2.43  tff(f_87, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B))) => m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_pre_topc)).
% 6.75/2.43  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 6.75/2.43  tff(f_155, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v4_tex_2(B, A)) & m1_pre_topc(B, A)) => (![C]: ((((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & v5_pre_topc(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (v3_borsuk_1(C, A, B) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => (![E]: (m1_subset_1(E, k1_zfmisc_1(u1_struct_0(A))) => ((D = E) => (k8_relset_1(u1_struct_0(A), u1_struct_0(B), C, D) = k2_pre_topc(A, E)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t76_tex_2)).
% 6.75/2.43  tff(f_94, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 6.75/2.43  tff(f_61, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 6.75/2.43  tff(c_46, plain, ('#skF_5'='#skF_6'), inference(cnfTransformation, [status(thm)], [f_194])).
% 6.75/2.43  tff(c_50, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_194])).
% 6.75/2.43  tff(c_75, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_50])).
% 6.75/2.43  tff(c_66, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_194])).
% 6.75/2.43  tff(c_72, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_194])).
% 6.75/2.43  tff(c_68, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_194])).
% 6.75/2.43  tff(c_62, plain, (m1_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_194])).
% 6.75/2.43  tff(c_134, plain, (![B_139, A_140]: (v2_pre_topc(B_139) | ~m1_pre_topc(B_139, A_140) | ~l1_pre_topc(A_140) | ~v2_pre_topc(A_140))), inference(cnfTransformation, [status(thm)], [f_70])).
% 6.75/2.43  tff(c_137, plain, (v2_pre_topc('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_62, c_134])).
% 6.75/2.43  tff(c_140, plain, (v2_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_68, c_137])).
% 6.75/2.43  tff(c_105, plain, (![B_125, A_126]: (l1_pre_topc(B_125) | ~m1_pre_topc(B_125, A_126) | ~l1_pre_topc(A_126))), inference(cnfTransformation, [status(thm)], [f_77])).
% 6.75/2.43  tff(c_108, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_62, c_105])).
% 6.75/2.43  tff(c_111, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_108])).
% 6.75/2.43  tff(c_40, plain, (![B_60, A_58]: (r2_hidden(B_60, k1_connsp_2(A_58, B_60)) | ~m1_subset_1(B_60, u1_struct_0(A_58)) | ~l1_pre_topc(A_58) | ~v2_pre_topc(A_58) | v2_struct_0(A_58))), inference(cnfTransformation, [status(thm)], [f_117])).
% 6.75/2.43  tff(c_2016, plain, (![A_479, B_480]: (m1_subset_1(k1_connsp_2(A_479, B_480), k1_zfmisc_1(u1_struct_0(A_479))) | ~m1_subset_1(B_480, u1_struct_0(A_479)) | ~l1_pre_topc(A_479) | ~v2_pre_topc(A_479) | v2_struct_0(A_479))), inference(cnfTransformation, [status(thm)], [f_105])).
% 6.75/2.43  tff(c_24, plain, (![A_36, B_37]: (r1_tarski(A_36, B_37) | ~m1_subset_1(A_36, k1_zfmisc_1(B_37)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 6.75/2.43  tff(c_2030, plain, (![A_479, B_480]: (r1_tarski(k1_connsp_2(A_479, B_480), u1_struct_0(A_479)) | ~m1_subset_1(B_480, u1_struct_0(A_479)) | ~l1_pre_topc(A_479) | ~v2_pre_topc(A_479) | v2_struct_0(A_479))), inference(resolution, [status(thm)], [c_2016, c_24])).
% 6.75/2.43  tff(c_117, plain, (![A_129, B_130]: (m1_subset_1(k1_tarski(A_129), k1_zfmisc_1(B_130)) | ~r2_hidden(A_129, B_130))), inference(cnfTransformation, [status(thm)], [f_50])).
% 6.75/2.43  tff(c_121, plain, (![A_129, B_130]: (r1_tarski(k1_tarski(A_129), B_130) | ~r2_hidden(A_129, B_130))), inference(resolution, [status(thm)], [c_117, c_24])).
% 6.75/2.43  tff(c_26, plain, (![A_36, B_37]: (m1_subset_1(A_36, k1_zfmisc_1(B_37)) | ~r1_tarski(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_54])).
% 6.75/2.43  tff(c_1773, plain, (![C_431, A_432, B_433]: (m1_subset_1(C_431, k1_zfmisc_1(u1_struct_0(A_432))) | ~m1_subset_1(C_431, k1_zfmisc_1(u1_struct_0(B_433))) | ~m1_pre_topc(B_433, A_432) | ~l1_pre_topc(A_432))), inference(cnfTransformation, [status(thm)], [f_87])).
% 6.75/2.43  tff(c_1782, plain, (![A_434, A_435, B_436]: (m1_subset_1(A_434, k1_zfmisc_1(u1_struct_0(A_435))) | ~m1_pre_topc(B_436, A_435) | ~l1_pre_topc(A_435) | ~r1_tarski(A_434, u1_struct_0(B_436)))), inference(resolution, [status(thm)], [c_26, c_1773])).
% 6.75/2.43  tff(c_1784, plain, (![A_434]: (m1_subset_1(A_434, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~r1_tarski(A_434, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_62, c_1782])).
% 6.75/2.43  tff(c_1788, plain, (![A_437]: (m1_subset_1(A_437, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~r1_tarski(A_437, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_1784])).
% 6.75/2.43  tff(c_1803, plain, (![A_438]: (r1_tarski(A_438, u1_struct_0('#skF_2')) | ~r1_tarski(A_438, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_1788, c_24])).
% 6.75/2.43  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.75/2.43  tff(c_130, plain, (![C_136, B_137, A_138]: (r2_hidden(C_136, B_137) | ~r2_hidden(C_136, A_138) | ~r1_tarski(A_138, B_137))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.75/2.43  tff(c_1684, plain, (![A_407, B_408, B_409]: (r2_hidden('#skF_1'(A_407, B_408), B_409) | ~r1_tarski(A_407, B_409) | r1_tarski(A_407, B_408))), inference(resolution, [status(thm)], [c_6, c_130])).
% 6.75/2.43  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.75/2.43  tff(c_1701, plain, (![A_407, B_408, B_2, B_409]: (r2_hidden('#skF_1'(A_407, B_408), B_2) | ~r1_tarski(B_409, B_2) | ~r1_tarski(A_407, B_409) | r1_tarski(A_407, B_408))), inference(resolution, [status(thm)], [c_1684, c_2])).
% 6.75/2.43  tff(c_2087, plain, (![A_486, B_487, A_488]: (r2_hidden('#skF_1'(A_486, B_487), u1_struct_0('#skF_2')) | ~r1_tarski(A_486, A_488) | r1_tarski(A_486, B_487) | ~r1_tarski(A_488, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_1803, c_1701])).
% 6.75/2.43  tff(c_2812, plain, (![A_571, B_572, B_573]: (r2_hidden('#skF_1'(k1_tarski(A_571), B_572), u1_struct_0('#skF_2')) | r1_tarski(k1_tarski(A_571), B_572) | ~r1_tarski(B_573, u1_struct_0('#skF_3')) | ~r2_hidden(A_571, B_573))), inference(resolution, [status(thm)], [c_121, c_2087])).
% 6.75/2.43  tff(c_2818, plain, (![A_571, B_572, B_480]: (r2_hidden('#skF_1'(k1_tarski(A_571), B_572), u1_struct_0('#skF_2')) | r1_tarski(k1_tarski(A_571), B_572) | ~r2_hidden(A_571, k1_connsp_2('#skF_3', B_480)) | ~m1_subset_1(B_480, u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_2030, c_2812])).
% 6.75/2.43  tff(c_2839, plain, (![A_571, B_572, B_480]: (r2_hidden('#skF_1'(k1_tarski(A_571), B_572), u1_struct_0('#skF_2')) | r1_tarski(k1_tarski(A_571), B_572) | ~r2_hidden(A_571, k1_connsp_2('#skF_3', B_480)) | ~m1_subset_1(B_480, u1_struct_0('#skF_3')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_140, c_111, c_2818])).
% 6.75/2.43  tff(c_2850, plain, (![A_574, B_575, B_576]: (r2_hidden('#skF_1'(k1_tarski(A_574), B_575), u1_struct_0('#skF_2')) | r1_tarski(k1_tarski(A_574), B_575) | ~r2_hidden(A_574, k1_connsp_2('#skF_3', B_576)) | ~m1_subset_1(B_576, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_66, c_2839])).
% 6.75/2.43  tff(c_2859, plain, (![B_60, B_575]: (r2_hidden('#skF_1'(k1_tarski(B_60), B_575), u1_struct_0('#skF_2')) | r1_tarski(k1_tarski(B_60), B_575) | ~m1_subset_1(B_60, u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_40, c_2850])).
% 6.75/2.43  tff(c_2870, plain, (![B_60, B_575]: (r2_hidden('#skF_1'(k1_tarski(B_60), B_575), u1_struct_0('#skF_2')) | r1_tarski(k1_tarski(B_60), B_575) | ~m1_subset_1(B_60, u1_struct_0('#skF_3')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_140, c_111, c_2859])).
% 6.75/2.43  tff(c_2874, plain, (![B_577, B_578]: (r2_hidden('#skF_1'(k1_tarski(B_577), B_578), u1_struct_0('#skF_2')) | r1_tarski(k1_tarski(B_577), B_578) | ~m1_subset_1(B_577, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_66, c_2870])).
% 6.75/2.43  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.75/2.43  tff(c_2894, plain, (![B_577]: (r1_tarski(k1_tarski(B_577), u1_struct_0('#skF_2')) | ~m1_subset_1(B_577, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_2874, c_4])).
% 6.75/2.43  tff(c_1912, plain, (![B_456, A_457]: (r2_hidden(B_456, k1_connsp_2(A_457, B_456)) | ~m1_subset_1(B_456, u1_struct_0(A_457)) | ~l1_pre_topc(A_457) | ~v2_pre_topc(A_457) | v2_struct_0(A_457))), inference(cnfTransformation, [status(thm)], [f_117])).
% 6.75/2.43  tff(c_2332, plain, (![B_510, B_511, A_512]: (r2_hidden(B_510, B_511) | ~r1_tarski(k1_connsp_2(A_512, B_510), B_511) | ~m1_subset_1(B_510, u1_struct_0(A_512)) | ~l1_pre_topc(A_512) | ~v2_pre_topc(A_512) | v2_struct_0(A_512))), inference(resolution, [status(thm)], [c_1912, c_2])).
% 6.75/2.43  tff(c_2359, plain, (![B_480, A_479]: (r2_hidden(B_480, u1_struct_0(A_479)) | ~m1_subset_1(B_480, u1_struct_0(A_479)) | ~l1_pre_topc(A_479) | ~v2_pre_topc(A_479) | v2_struct_0(A_479))), inference(resolution, [status(thm)], [c_2030, c_2332])).
% 6.75/2.43  tff(c_74, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_194])).
% 6.75/2.43  tff(c_70, plain, (v3_tdlat_3('#skF_2')), inference(cnfTransformation, [status(thm)], [f_194])).
% 6.75/2.43  tff(c_64, plain, (v4_tex_2('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_194])).
% 6.75/2.43  tff(c_60, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_194])).
% 6.75/2.43  tff(c_58, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_194])).
% 6.75/2.43  tff(c_56, plain, (v5_pre_topc('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_194])).
% 6.75/2.43  tff(c_52, plain, (v3_borsuk_1('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_194])).
% 6.75/2.43  tff(c_54, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_194])).
% 6.75/2.43  tff(c_2140, plain, (![A_491, B_492, C_493, E_494]: (k8_relset_1(u1_struct_0(A_491), u1_struct_0(B_492), C_493, E_494)=k2_pre_topc(A_491, E_494) | ~m1_subset_1(E_494, k1_zfmisc_1(u1_struct_0(A_491))) | ~m1_subset_1(E_494, k1_zfmisc_1(u1_struct_0(B_492))) | ~v3_borsuk_1(C_493, A_491, B_492) | ~m1_subset_1(C_493, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_491), u1_struct_0(B_492)))) | ~v5_pre_topc(C_493, A_491, B_492) | ~v1_funct_2(C_493, u1_struct_0(A_491), u1_struct_0(B_492)) | ~v1_funct_1(C_493) | ~m1_pre_topc(B_492, A_491) | ~v4_tex_2(B_492, A_491) | v2_struct_0(B_492) | ~l1_pre_topc(A_491) | ~v3_tdlat_3(A_491) | ~v2_pre_topc(A_491) | v2_struct_0(A_491))), inference(cnfTransformation, [status(thm)], [f_155])).
% 6.75/2.43  tff(c_2764, plain, (![A_564, B_565, C_566, A_567]: (k8_relset_1(u1_struct_0(A_564), u1_struct_0(B_565), C_566, A_567)=k2_pre_topc(A_564, A_567) | ~m1_subset_1(A_567, k1_zfmisc_1(u1_struct_0(B_565))) | ~v3_borsuk_1(C_566, A_564, B_565) | ~m1_subset_1(C_566, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_564), u1_struct_0(B_565)))) | ~v5_pre_topc(C_566, A_564, B_565) | ~v1_funct_2(C_566, u1_struct_0(A_564), u1_struct_0(B_565)) | ~v1_funct_1(C_566) | ~m1_pre_topc(B_565, A_564) | ~v4_tex_2(B_565, A_564) | v2_struct_0(B_565) | ~l1_pre_topc(A_564) | ~v3_tdlat_3(A_564) | ~v2_pre_topc(A_564) | v2_struct_0(A_564) | ~r1_tarski(A_567, u1_struct_0(A_564)))), inference(resolution, [status(thm)], [c_26, c_2140])).
% 6.75/2.43  tff(c_4136, plain, (![A_730, B_731, C_732, A_733]: (k8_relset_1(u1_struct_0(A_730), u1_struct_0(B_731), C_732, A_733)=k2_pre_topc(A_730, A_733) | ~v3_borsuk_1(C_732, A_730, B_731) | ~m1_subset_1(C_732, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_730), u1_struct_0(B_731)))) | ~v5_pre_topc(C_732, A_730, B_731) | ~v1_funct_2(C_732, u1_struct_0(A_730), u1_struct_0(B_731)) | ~v1_funct_1(C_732) | ~m1_pre_topc(B_731, A_730) | ~v4_tex_2(B_731, A_730) | v2_struct_0(B_731) | ~l1_pre_topc(A_730) | ~v3_tdlat_3(A_730) | ~v2_pre_topc(A_730) | v2_struct_0(A_730) | ~r1_tarski(A_733, u1_struct_0(A_730)) | ~r1_tarski(A_733, u1_struct_0(B_731)))), inference(resolution, [status(thm)], [c_26, c_2764])).
% 6.75/2.43  tff(c_4141, plain, (![A_733]: (k8_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4', A_733)=k2_pre_topc('#skF_2', A_733) | ~v3_borsuk_1('#skF_4', '#skF_2', '#skF_3') | ~v5_pre_topc('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_2') | ~v4_tex_2('#skF_3', '#skF_2') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v3_tdlat_3('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~r1_tarski(A_733, u1_struct_0('#skF_2')) | ~r1_tarski(A_733, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_54, c_4136])).
% 6.75/2.43  tff(c_4148, plain, (![A_733]: (k8_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4', A_733)=k2_pre_topc('#skF_2', A_733) | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | ~r1_tarski(A_733, u1_struct_0('#skF_2')) | ~r1_tarski(A_733, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_68, c_64, c_62, c_60, c_58, c_56, c_52, c_4141])).
% 6.75/2.43  tff(c_4151, plain, (![A_734]: (k8_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4', A_734)=k2_pre_topc('#skF_2', A_734) | ~r1_tarski(A_734, u1_struct_0('#skF_2')) | ~r1_tarski(A_734, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_74, c_66, c_4148])).
% 6.75/2.43  tff(c_188, plain, (![A_161, B_162]: (k6_domain_1(A_161, B_162)=k1_tarski(B_162) | ~m1_subset_1(B_162, A_161) | v1_xboole_0(A_161))), inference(cnfTransformation, [status(thm)], [f_94])).
% 6.75/2.43  tff(c_208, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_6')=k1_tarski('#skF_6') | v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_75, c_188])).
% 6.75/2.43  tff(c_907, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_208])).
% 6.75/2.43  tff(c_1277, plain, (![A_359, B_360]: (m1_subset_1(k1_connsp_2(A_359, B_360), k1_zfmisc_1(u1_struct_0(A_359))) | ~m1_subset_1(B_360, u1_struct_0(A_359)) | ~l1_pre_topc(A_359) | ~v2_pre_topc(A_359) | v2_struct_0(A_359))), inference(cnfTransformation, [status(thm)], [f_105])).
% 6.75/2.43  tff(c_1291, plain, (![A_359, B_360]: (r1_tarski(k1_connsp_2(A_359, B_360), u1_struct_0(A_359)) | ~m1_subset_1(B_360, u1_struct_0(A_359)) | ~l1_pre_topc(A_359) | ~v2_pre_topc(A_359) | v2_struct_0(A_359))), inference(resolution, [status(thm)], [c_1277, c_24])).
% 6.75/2.43  tff(c_1090, plain, (![B_323, A_324]: (r2_hidden(B_323, k1_connsp_2(A_324, B_323)) | ~m1_subset_1(B_323, u1_struct_0(A_324)) | ~l1_pre_topc(A_324) | ~v2_pre_topc(A_324) | v2_struct_0(A_324))), inference(cnfTransformation, [status(thm)], [f_117])).
% 6.75/2.43  tff(c_141, plain, (![C_141, B_142, A_143]: (~v1_xboole_0(C_141) | ~m1_subset_1(B_142, k1_zfmisc_1(C_141)) | ~r2_hidden(A_143, B_142))), inference(cnfTransformation, [status(thm)], [f_61])).
% 6.75/2.43  tff(c_150, plain, (![B_37, A_143, A_36]: (~v1_xboole_0(B_37) | ~r2_hidden(A_143, A_36) | ~r1_tarski(A_36, B_37))), inference(resolution, [status(thm)], [c_26, c_141])).
% 6.75/2.43  tff(c_1588, plain, (![B_395, A_396, B_397]: (~v1_xboole_0(B_395) | ~r1_tarski(k1_connsp_2(A_396, B_397), B_395) | ~m1_subset_1(B_397, u1_struct_0(A_396)) | ~l1_pre_topc(A_396) | ~v2_pre_topc(A_396) | v2_struct_0(A_396))), inference(resolution, [status(thm)], [c_1090, c_150])).
% 6.75/2.43  tff(c_1652, plain, (![A_401, B_402]: (~v1_xboole_0(u1_struct_0(A_401)) | ~m1_subset_1(B_402, u1_struct_0(A_401)) | ~l1_pre_topc(A_401) | ~v2_pre_topc(A_401) | v2_struct_0(A_401))), inference(resolution, [status(thm)], [c_1291, c_1588])).
% 6.75/2.43  tff(c_1658, plain, (~v1_xboole_0(u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_75, c_1652])).
% 6.75/2.43  tff(c_1665, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_140, c_111, c_907, c_1658])).
% 6.75/2.43  tff(c_1667, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_1665])).
% 6.75/2.43  tff(c_1668, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_6')=k1_tarski('#skF_6')), inference(splitRight, [status(thm)], [c_208])).
% 6.75/2.43  tff(c_48, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_194])).
% 6.75/2.43  tff(c_207, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_6')=k1_tarski('#skF_6') | v1_xboole_0(u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_48, c_188])).
% 6.75/2.43  tff(c_209, plain, (v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_207])).
% 6.75/2.43  tff(c_391, plain, (![A_209, B_210]: (m1_subset_1(k1_connsp_2(A_209, B_210), k1_zfmisc_1(u1_struct_0(A_209))) | ~m1_subset_1(B_210, u1_struct_0(A_209)) | ~l1_pre_topc(A_209) | ~v2_pre_topc(A_209) | v2_struct_0(A_209))), inference(cnfTransformation, [status(thm)], [f_105])).
% 6.75/2.43  tff(c_28, plain, (![C_40, B_39, A_38]: (~v1_xboole_0(C_40) | ~m1_subset_1(B_39, k1_zfmisc_1(C_40)) | ~r2_hidden(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_61])).
% 6.75/2.43  tff(c_798, plain, (![A_269, A_270, B_271]: (~v1_xboole_0(u1_struct_0(A_269)) | ~r2_hidden(A_270, k1_connsp_2(A_269, B_271)) | ~m1_subset_1(B_271, u1_struct_0(A_269)) | ~l1_pre_topc(A_269) | ~v2_pre_topc(A_269) | v2_struct_0(A_269))), inference(resolution, [status(thm)], [c_391, c_28])).
% 6.75/2.43  tff(c_888, plain, (![A_280, B_281]: (~v1_xboole_0(u1_struct_0(A_280)) | ~m1_subset_1(B_281, u1_struct_0(A_280)) | ~l1_pre_topc(A_280) | ~v2_pre_topc(A_280) | v2_struct_0(A_280))), inference(resolution, [status(thm)], [c_40, c_798])).
% 6.75/2.43  tff(c_891, plain, (~v1_xboole_0(u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_48, c_888])).
% 6.75/2.43  tff(c_897, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_68, c_209, c_891])).
% 6.75/2.43  tff(c_899, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_897])).
% 6.75/2.43  tff(c_900, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_6')=k1_tarski('#skF_6')), inference(splitRight, [status(thm)], [c_207])).
% 6.75/2.43  tff(c_44, plain, (k8_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4', k6_domain_1(u1_struct_0('#skF_3'), '#skF_5'))!=k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_194])).
% 6.75/2.43  tff(c_76, plain, (k8_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4', k6_domain_1(u1_struct_0('#skF_3'), '#skF_6'))!=k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44])).
% 6.75/2.43  tff(c_902, plain, (k8_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4', k6_domain_1(u1_struct_0('#skF_3'), '#skF_6'))!=k2_pre_topc('#skF_2', k1_tarski('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_900, c_76])).
% 6.75/2.43  tff(c_1759, plain, (k8_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4', k1_tarski('#skF_6'))!=k2_pre_topc('#skF_2', k1_tarski('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_1668, c_902])).
% 6.75/2.43  tff(c_4162, plain, (~r1_tarski(k1_tarski('#skF_6'), u1_struct_0('#skF_2')) | ~r1_tarski(k1_tarski('#skF_6'), u1_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_4151, c_1759])).
% 6.75/2.43  tff(c_4164, plain, (~r1_tarski(k1_tarski('#skF_6'), u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_4162])).
% 6.75/2.43  tff(c_4178, plain, (~r2_hidden('#skF_6', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_121, c_4164])).
% 6.75/2.43  tff(c_4205, plain, (~m1_subset_1('#skF_6', u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_2359, c_4178])).
% 6.75/2.43  tff(c_4211, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_140, c_111, c_75, c_4205])).
% 6.75/2.43  tff(c_4213, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_4211])).
% 6.75/2.43  tff(c_4214, plain, (~r1_tarski(k1_tarski('#skF_6'), u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_4162])).
% 6.75/2.43  tff(c_4221, plain, (~m1_subset_1('#skF_6', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_2894, c_4214])).
% 6.75/2.43  tff(c_4241, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_75, c_4221])).
% 6.75/2.43  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.75/2.43  
% 6.75/2.43  Inference rules
% 6.75/2.43  ----------------------
% 6.75/2.43  #Ref     : 0
% 6.75/2.43  #Sup     : 1025
% 6.75/2.43  #Fact    : 0
% 6.75/2.43  #Define  : 0
% 6.75/2.43  #Split   : 31
% 6.75/2.43  #Chain   : 0
% 6.75/2.43  #Close   : 0
% 6.75/2.43  
% 6.75/2.43  Ordering : KBO
% 6.75/2.43  
% 6.75/2.43  Simplification rules
% 6.75/2.43  ----------------------
% 6.75/2.43  #Subsume      : 438
% 6.75/2.43  #Demod        : 156
% 6.75/2.43  #Tautology    : 94
% 6.75/2.43  #SimpNegUnit  : 58
% 6.75/2.43  #BackRed      : 2
% 6.75/2.43  
% 6.75/2.43  #Partial instantiations: 0
% 6.75/2.43  #Strategies tried      : 1
% 6.75/2.43  
% 6.75/2.43  Timing (in seconds)
% 6.75/2.43  ----------------------
% 6.75/2.44  Preprocessing        : 0.38
% 6.75/2.44  Parsing              : 0.20
% 6.75/2.44  CNF conversion       : 0.03
% 6.75/2.44  Main loop            : 1.23
% 6.75/2.44  Inferencing          : 0.41
% 6.75/2.44  Reduction            : 0.35
% 6.75/2.44  Demodulation         : 0.24
% 6.75/2.44  BG Simplification    : 0.04
% 6.75/2.44  Subsumption          : 0.34
% 6.75/2.44  Abstraction          : 0.05
% 6.75/2.44  MUC search           : 0.00
% 6.75/2.44  Cooper               : 0.00
% 6.75/2.44  Total                : 1.66
% 6.75/2.44  Index Insertion      : 0.00
% 6.75/2.44  Index Deletion       : 0.00
% 6.75/2.44  Index Matching       : 0.00
% 6.75/2.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
