%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:12 EST 2020

% Result     : Theorem 4.63s
% Output     : CNFRefutation 4.89s
% Verified   : 
% Statistics : Number of formulae       :  124 ( 423 expanded)
%              Number of leaves         :   31 ( 152 expanded)
%              Depth                    :   15
%              Number of atoms          :  319 (1365 expanded)
%              Number of equality atoms :   28 ( 102 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_tex_2 > v2_tex_2 > v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_tdlat_3 > l1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_3 > #skF_5 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(v1_tdlat_3,type,(
    v1_tdlat_3: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v3_tex_2,type,(
    v3_tex_2: ( $i * $i ) > $o )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

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

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_132,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & v1_tdlat_3(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v3_tex_2(B,A)
            <=> ~ v1_subset_1(B,u1_struct_0(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_tex_2)).

tff(f_46,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( ! [D] :
                ( m1_subset_1(D,A)
               => ( r2_hidden(D,B)
                 => r2_hidden(D,C) ) )
           => r1_tarski(B,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_subset_1)).

tff(f_75,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

tff(f_71,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_114,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & v1_tdlat_3(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => v2_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_tex_2)).

tff(f_82,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( v1_subset_1(B,A)
      <=> B != A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).

tff(f_100,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_tex_2(B,A)
          <=> ( v2_tex_2(B,A)
              & ! [C] :
                  ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
                 => ( ( v2_tex_2(C,A)
                      & r1_tarski(B,C) )
                   => B = C ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_tex_2)).

tff(f_60,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( ! [D] :
                ( m1_subset_1(D,A)
               => ( r2_hidden(D,B)
                <=> r2_hidden(D,C) ) )
           => B = C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_subset_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(c_46,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_6,plain,(
    ! [A_5,B_6,C_10] :
      ( r2_hidden('#skF_1'(A_5,B_6,C_10),B_6)
      | r1_tarski(B_6,C_10)
      | ~ m1_subset_1(C_10,k1_zfmisc_1(A_5))
      | ~ m1_subset_1(B_6,k1_zfmisc_1(A_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1870,plain,(
    ! [A_298,B_299,C_300] :
      ( ~ r2_hidden('#skF_1'(A_298,B_299,C_300),C_300)
      | r1_tarski(B_299,C_300)
      | ~ m1_subset_1(C_300,k1_zfmisc_1(A_298))
      | ~ m1_subset_1(B_299,k1_zfmisc_1(A_298)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1876,plain,(
    ! [B_301,A_302] :
      ( r1_tarski(B_301,B_301)
      | ~ m1_subset_1(B_301,k1_zfmisc_1(A_302)) ) ),
    inference(resolution,[status(thm)],[c_6,c_1870])).

tff(c_1893,plain,(
    r1_tarski('#skF_5','#skF_5') ),
    inference(resolution,[status(thm)],[c_46,c_1876])).

tff(c_54,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_48,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_52,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_50,plain,(
    v1_tdlat_3('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_26,plain,(
    ! [A_24] :
      ( m1_pre_topc(A_24,A_24)
      | ~ l1_pre_topc(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_24,plain,(
    ! [B_23,A_21] :
      ( m1_subset_1(u1_struct_0(B_23),k1_zfmisc_1(u1_struct_0(A_21)))
      | ~ m1_pre_topc(B_23,A_21)
      | ~ l1_pre_topc(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1927,plain,(
    ! [B_307,A_308] :
      ( r1_tarski(u1_struct_0(B_307),u1_struct_0(B_307))
      | ~ m1_pre_topc(B_307,A_308)
      | ~ l1_pre_topc(A_308) ) ),
    inference(resolution,[status(thm)],[c_24,c_1876])).

tff(c_1931,plain,(
    ! [A_309] :
      ( r1_tarski(u1_struct_0(A_309),u1_struct_0(A_309))
      | ~ l1_pre_topc(A_309) ) ),
    inference(resolution,[status(thm)],[c_26,c_1927])).

tff(c_22,plain,(
    ! [A_19,B_20] :
      ( m1_subset_1(A_19,k1_zfmisc_1(B_20))
      | ~ r1_tarski(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_1773,plain,(
    ! [B_282,A_283] :
      ( v2_tex_2(B_282,A_283)
      | ~ m1_subset_1(B_282,k1_zfmisc_1(u1_struct_0(A_283)))
      | ~ l1_pre_topc(A_283)
      | ~ v1_tdlat_3(A_283)
      | ~ v2_pre_topc(A_283)
      | v2_struct_0(A_283) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_1790,plain,(
    ! [A_19,A_283] :
      ( v2_tex_2(A_19,A_283)
      | ~ l1_pre_topc(A_283)
      | ~ v1_tdlat_3(A_283)
      | ~ v2_pre_topc(A_283)
      | v2_struct_0(A_283)
      | ~ r1_tarski(A_19,u1_struct_0(A_283)) ) ),
    inference(resolution,[status(thm)],[c_22,c_1773])).

tff(c_1945,plain,(
    ! [A_309] :
      ( v2_tex_2(u1_struct_0(A_309),A_309)
      | ~ v1_tdlat_3(A_309)
      | ~ v2_pre_topc(A_309)
      | v2_struct_0(A_309)
      | ~ l1_pre_topc(A_309) ) ),
    inference(resolution,[status(thm)],[c_1931,c_1790])).

tff(c_62,plain,
    ( v3_tex_2('#skF_5','#skF_4')
    | ~ v1_subset_1('#skF_5',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_65,plain,(
    ~ v1_subset_1('#skF_5',u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_56,plain,
    ( v1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ v3_tex_2('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_66,plain,(
    ~ v3_tex_2('#skF_5','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_65,c_56])).

tff(c_83,plain,(
    ! [B_48,A_49] :
      ( v1_subset_1(B_48,A_49)
      | B_48 = A_49
      | ~ m1_subset_1(B_48,k1_zfmisc_1(A_49)) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_89,plain,
    ( v1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | u1_struct_0('#skF_4') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_46,c_83])).

tff(c_93,plain,(
    u1_struct_0('#skF_4') = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_65,c_89])).

tff(c_97,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_46])).

tff(c_333,plain,(
    ! [B_83,A_84] :
      ( v2_tex_2(B_83,A_84)
      | ~ m1_subset_1(B_83,k1_zfmisc_1(u1_struct_0(A_84)))
      | ~ l1_pre_topc(A_84)
      | ~ v1_tdlat_3(A_84)
      | ~ v2_pre_topc(A_84)
      | v2_struct_0(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_346,plain,(
    ! [B_83] :
      ( v2_tex_2(B_83,'#skF_4')
      | ~ m1_subset_1(B_83,k1_zfmisc_1('#skF_5'))
      | ~ l1_pre_topc('#skF_4')
      | ~ v1_tdlat_3('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_93,c_333])).

tff(c_355,plain,(
    ! [B_83] :
      ( v2_tex_2(B_83,'#skF_4')
      | ~ m1_subset_1(B_83,k1_zfmisc_1('#skF_5'))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_346])).

tff(c_358,plain,(
    ! [B_85] :
      ( v2_tex_2(B_85,'#skF_4')
      | ~ m1_subset_1(B_85,k1_zfmisc_1('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_355])).

tff(c_375,plain,(
    v2_tex_2('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_97,c_358])).

tff(c_793,plain,(
    ! [A_141,B_142] :
      ( m1_subset_1('#skF_3'(A_141,B_142),k1_zfmisc_1(u1_struct_0(A_141)))
      | v3_tex_2(B_142,A_141)
      | ~ v2_tex_2(B_142,A_141)
      | ~ m1_subset_1(B_142,k1_zfmisc_1(u1_struct_0(A_141)))
      | ~ l1_pre_topc(A_141) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_817,plain,(
    ! [B_142] :
      ( m1_subset_1('#skF_3'('#skF_4',B_142),k1_zfmisc_1('#skF_5'))
      | v3_tex_2(B_142,'#skF_4')
      | ~ v2_tex_2(B_142,'#skF_4')
      | ~ m1_subset_1(B_142,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_93,c_793])).

tff(c_829,plain,(
    ! [B_143] :
      ( m1_subset_1('#skF_3'('#skF_4',B_143),k1_zfmisc_1('#skF_5'))
      | v3_tex_2(B_143,'#skF_4')
      | ~ v2_tex_2(B_143,'#skF_4')
      | ~ m1_subset_1(B_143,k1_zfmisc_1('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_93,c_817])).

tff(c_20,plain,(
    ! [A_19,B_20] :
      ( r1_tarski(A_19,B_20)
      | ~ m1_subset_1(A_19,k1_zfmisc_1(B_20)) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_848,plain,(
    ! [B_143] :
      ( r1_tarski('#skF_3'('#skF_4',B_143),'#skF_5')
      | v3_tex_2(B_143,'#skF_4')
      | ~ v2_tex_2(B_143,'#skF_4')
      | ~ m1_subset_1(B_143,k1_zfmisc_1('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_829,c_20])).

tff(c_471,plain,(
    ! [A_106,B_107] :
      ( '#skF_3'(A_106,B_107) != B_107
      | v3_tex_2(B_107,A_106)
      | ~ v2_tex_2(B_107,A_106)
      | ~ m1_subset_1(B_107,k1_zfmisc_1(u1_struct_0(A_106)))
      | ~ l1_pre_topc(A_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_484,plain,(
    ! [B_107] :
      ( '#skF_3'('#skF_4',B_107) != B_107
      | v3_tex_2(B_107,'#skF_4')
      | ~ v2_tex_2(B_107,'#skF_4')
      | ~ m1_subset_1(B_107,k1_zfmisc_1('#skF_5'))
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_93,c_471])).

tff(c_521,plain,(
    ! [B_111] :
      ( '#skF_3'('#skF_4',B_111) != B_111
      | v3_tex_2(B_111,'#skF_4')
      | ~ v2_tex_2(B_111,'#skF_4')
      | ~ m1_subset_1(B_111,k1_zfmisc_1('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_484])).

tff(c_531,plain,
    ( '#skF_3'('#skF_4','#skF_5') != '#skF_5'
    | v3_tex_2('#skF_5','#skF_4')
    | ~ v2_tex_2('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_97,c_521])).

tff(c_540,plain,
    ( '#skF_3'('#skF_4','#skF_5') != '#skF_5'
    | v3_tex_2('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_375,c_531])).

tff(c_541,plain,(
    '#skF_3'('#skF_4','#skF_5') != '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_540])).

tff(c_408,plain,(
    ! [A_98,B_99,C_100] :
      ( ~ r2_hidden('#skF_1'(A_98,B_99,C_100),C_100)
      | r1_tarski(B_99,C_100)
      | ~ m1_subset_1(C_100,k1_zfmisc_1(A_98))
      | ~ m1_subset_1(B_99,k1_zfmisc_1(A_98)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_414,plain,(
    ! [B_101,A_102] :
      ( r1_tarski(B_101,B_101)
      | ~ m1_subset_1(B_101,k1_zfmisc_1(A_102)) ) ),
    inference(resolution,[status(thm)],[c_6,c_408])).

tff(c_495,plain,(
    ! [B_108,A_109] :
      ( r1_tarski(u1_struct_0(B_108),u1_struct_0(B_108))
      | ~ m1_pre_topc(B_108,A_109)
      | ~ l1_pre_topc(A_109) ) ),
    inference(resolution,[status(thm)],[c_24,c_414])).

tff(c_498,plain,(
    ! [A_24] :
      ( r1_tarski(u1_struct_0(A_24),u1_struct_0(A_24))
      | ~ l1_pre_topc(A_24) ) ),
    inference(resolution,[status(thm)],[c_26,c_495])).

tff(c_717,plain,(
    ! [B_128,A_129] :
      ( r1_tarski(B_128,'#skF_3'(A_129,B_128))
      | v3_tex_2(B_128,A_129)
      | ~ v2_tex_2(B_128,A_129)
      | ~ m1_subset_1(B_128,k1_zfmisc_1(u1_struct_0(A_129)))
      | ~ l1_pre_topc(A_129) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_751,plain,(
    ! [A_135,A_136] :
      ( r1_tarski(A_135,'#skF_3'(A_136,A_135))
      | v3_tex_2(A_135,A_136)
      | ~ v2_tex_2(A_135,A_136)
      | ~ l1_pre_topc(A_136)
      | ~ r1_tarski(A_135,u1_struct_0(A_136)) ) ),
    inference(resolution,[status(thm)],[c_22,c_717])).

tff(c_773,plain,(
    ! [A_140] :
      ( r1_tarski(u1_struct_0(A_140),'#skF_3'(A_140,u1_struct_0(A_140)))
      | v3_tex_2(u1_struct_0(A_140),A_140)
      | ~ v2_tex_2(u1_struct_0(A_140),A_140)
      | ~ l1_pre_topc(A_140) ) ),
    inference(resolution,[status(thm)],[c_498,c_751])).

tff(c_778,plain,
    ( r1_tarski('#skF_5','#skF_3'('#skF_4',u1_struct_0('#skF_4')))
    | v3_tex_2(u1_struct_0('#skF_4'),'#skF_4')
    | ~ v2_tex_2(u1_struct_0('#skF_4'),'#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_93,c_773])).

tff(c_784,plain,
    ( r1_tarski('#skF_5','#skF_3'('#skF_4','#skF_5'))
    | v3_tex_2('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_375,c_93,c_93,c_93,c_778])).

tff(c_785,plain,(
    r1_tarski('#skF_5','#skF_3'('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_784])).

tff(c_939,plain,(
    ! [A_155,B_156,C_157] :
      ( r2_hidden('#skF_2'(A_155,B_156,C_157),B_156)
      | r2_hidden('#skF_2'(A_155,B_156,C_157),C_157)
      | C_157 = B_156
      | ~ m1_subset_1(C_157,k1_zfmisc_1(A_155))
      | ~ m1_subset_1(B_156,k1_zfmisc_1(A_155)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_2,plain,(
    ! [C_4,A_1,B_2] :
      ( r2_hidden(C_4,A_1)
      | ~ r2_hidden(C_4,B_2)
      | ~ m1_subset_1(B_2,k1_zfmisc_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_945,plain,(
    ! [A_155,B_156,C_157,A_1] :
      ( r2_hidden('#skF_2'(A_155,B_156,C_157),A_1)
      | ~ m1_subset_1(C_157,k1_zfmisc_1(A_1))
      | r2_hidden('#skF_2'(A_155,B_156,C_157),B_156)
      | C_157 = B_156
      | ~ m1_subset_1(C_157,k1_zfmisc_1(A_155))
      | ~ m1_subset_1(B_156,k1_zfmisc_1(A_155)) ) ),
    inference(resolution,[status(thm)],[c_939,c_2])).

tff(c_1308,plain,(
    ! [C_157,B_156,A_155] :
      ( ~ m1_subset_1(C_157,k1_zfmisc_1(B_156))
      | C_157 = B_156
      | ~ m1_subset_1(C_157,k1_zfmisc_1(A_155))
      | ~ m1_subset_1(B_156,k1_zfmisc_1(A_155))
      | r2_hidden('#skF_2'(A_155,B_156,C_157),B_156) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_945])).

tff(c_1409,plain,(
    ! [C_226,B_227,A_228] :
      ( ~ m1_subset_1(C_226,k1_zfmisc_1(B_227))
      | C_226 = B_227
      | ~ m1_subset_1(C_226,k1_zfmisc_1(A_228))
      | ~ m1_subset_1(B_227,k1_zfmisc_1(A_228))
      | r2_hidden('#skF_2'(A_228,B_227,C_226),B_227) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_945])).

tff(c_1419,plain,(
    ! [A_232,B_233,C_234,A_235] :
      ( r2_hidden('#skF_2'(A_232,B_233,C_234),A_235)
      | ~ m1_subset_1(B_233,k1_zfmisc_1(A_235))
      | ~ m1_subset_1(C_234,k1_zfmisc_1(B_233))
      | C_234 = B_233
      | ~ m1_subset_1(C_234,k1_zfmisc_1(A_232))
      | ~ m1_subset_1(B_233,k1_zfmisc_1(A_232)) ) ),
    inference(resolution,[status(thm)],[c_1409,c_2])).

tff(c_12,plain,(
    ! [A_12,B_13,C_17] :
      ( ~ r2_hidden('#skF_2'(A_12,B_13,C_17),C_17)
      | ~ r2_hidden('#skF_2'(A_12,B_13,C_17),B_13)
      | C_17 = B_13
      | ~ m1_subset_1(C_17,k1_zfmisc_1(A_12))
      | ~ m1_subset_1(B_13,k1_zfmisc_1(A_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_1427,plain,(
    ! [A_236,B_237,A_238] :
      ( ~ r2_hidden('#skF_2'(A_236,B_237,A_238),B_237)
      | ~ m1_subset_1(B_237,k1_zfmisc_1(A_238))
      | ~ m1_subset_1(A_238,k1_zfmisc_1(B_237))
      | B_237 = A_238
      | ~ m1_subset_1(A_238,k1_zfmisc_1(A_236))
      | ~ m1_subset_1(B_237,k1_zfmisc_1(A_236)) ) ),
    inference(resolution,[status(thm)],[c_1419,c_12])).

tff(c_1449,plain,(
    ! [B_239,C_240,A_241] :
      ( ~ m1_subset_1(B_239,k1_zfmisc_1(C_240))
      | ~ m1_subset_1(C_240,k1_zfmisc_1(B_239))
      | C_240 = B_239
      | ~ m1_subset_1(C_240,k1_zfmisc_1(A_241))
      | ~ m1_subset_1(B_239,k1_zfmisc_1(A_241)) ) ),
    inference(resolution,[status(thm)],[c_1308,c_1427])).

tff(c_1516,plain,(
    ! [B_246,A_247,A_248] :
      ( ~ m1_subset_1(B_246,k1_zfmisc_1(A_247))
      | B_246 = A_247
      | ~ m1_subset_1(B_246,k1_zfmisc_1(A_248))
      | ~ m1_subset_1(A_247,k1_zfmisc_1(A_248))
      | ~ r1_tarski(A_247,B_246) ) ),
    inference(resolution,[status(thm)],[c_22,c_1449])).

tff(c_1549,plain,(
    ! [B_249,A_250,A_251] :
      ( B_249 = A_250
      | ~ m1_subset_1(A_250,k1_zfmisc_1(A_251))
      | ~ m1_subset_1(B_249,k1_zfmisc_1(A_251))
      | ~ r1_tarski(B_249,A_250)
      | ~ r1_tarski(A_250,B_249) ) ),
    inference(resolution,[status(thm)],[c_22,c_1516])).

tff(c_1579,plain,(
    ! [B_252] :
      ( B_252 = '#skF_5'
      | ~ m1_subset_1(B_252,k1_zfmisc_1('#skF_5'))
      | ~ r1_tarski(B_252,'#skF_5')
      | ~ r1_tarski('#skF_5',B_252) ) ),
    inference(resolution,[status(thm)],[c_97,c_1549])).

tff(c_1610,plain,(
    ! [A_253] :
      ( A_253 = '#skF_5'
      | ~ r1_tarski('#skF_5',A_253)
      | ~ r1_tarski(A_253,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_22,c_1579])).

tff(c_1615,plain,
    ( '#skF_3'('#skF_4','#skF_5') = '#skF_5'
    | ~ r1_tarski('#skF_3'('#skF_4','#skF_5'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_785,c_1610])).

tff(c_1634,plain,(
    ~ r1_tarski('#skF_3'('#skF_4','#skF_5'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_541,c_1615])).

tff(c_1651,plain,
    ( v3_tex_2('#skF_5','#skF_4')
    | ~ v2_tex_2('#skF_5','#skF_4')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_848,c_1634])).

tff(c_1654,plain,(
    v3_tex_2('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_375,c_1651])).

tff(c_1656,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_1654])).

tff(c_1657,plain,(
    v3_tex_2('#skF_5','#skF_4') ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_1668,plain,(
    ! [A_257,B_258] :
      ( r1_tarski(A_257,B_258)
      | ~ m1_subset_1(A_257,k1_zfmisc_1(B_258)) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_1676,plain,(
    r1_tarski('#skF_5',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_46,c_1668])).

tff(c_2138,plain,(
    ! [C_344,B_345,A_346] :
      ( C_344 = B_345
      | ~ r1_tarski(B_345,C_344)
      | ~ v2_tex_2(C_344,A_346)
      | ~ m1_subset_1(C_344,k1_zfmisc_1(u1_struct_0(A_346)))
      | ~ v3_tex_2(B_345,A_346)
      | ~ m1_subset_1(B_345,k1_zfmisc_1(u1_struct_0(A_346)))
      | ~ l1_pre_topc(A_346) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_2171,plain,(
    ! [A_346] :
      ( u1_struct_0('#skF_4') = '#skF_5'
      | ~ v2_tex_2(u1_struct_0('#skF_4'),A_346)
      | ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0(A_346)))
      | ~ v3_tex_2('#skF_5',A_346)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0(A_346)))
      | ~ l1_pre_topc(A_346) ) ),
    inference(resolution,[status(thm)],[c_1676,c_2138])).

tff(c_2190,plain,(
    ! [A_354] :
      ( ~ v2_tex_2(u1_struct_0('#skF_4'),A_354)
      | ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0(A_354)))
      | ~ v3_tex_2('#skF_5',A_354)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0(A_354)))
      | ~ l1_pre_topc(A_354) ) ),
    inference(splitLeft,[status(thm)],[c_2171])).

tff(c_2201,plain,(
    ! [A_357] :
      ( ~ v2_tex_2(u1_struct_0('#skF_4'),A_357)
      | ~ v3_tex_2('#skF_5',A_357)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0(A_357)))
      | ~ m1_pre_topc('#skF_4',A_357)
      | ~ l1_pre_topc(A_357) ) ),
    inference(resolution,[status(thm)],[c_24,c_2190])).

tff(c_2207,plain,
    ( ~ v2_tex_2(u1_struct_0('#skF_4'),'#skF_4')
    | ~ v3_tex_2('#skF_5','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_2201])).

tff(c_2211,plain,
    ( ~ v2_tex_2(u1_struct_0('#skF_4'),'#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_1657,c_2207])).

tff(c_2212,plain,(
    ~ m1_pre_topc('#skF_4','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_2211])).

tff(c_2215,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_26,c_2212])).

tff(c_2219,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_2215])).

tff(c_2220,plain,(
    ~ v2_tex_2(u1_struct_0('#skF_4'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_2211])).

tff(c_2229,plain,
    ( ~ v1_tdlat_3('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_1945,c_2220])).

tff(c_2235,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_52,c_50,c_2229])).

tff(c_2237,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_2235])).

tff(c_2238,plain,(
    u1_struct_0('#skF_4') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_2171])).

tff(c_1658,plain,(
    v1_subset_1('#skF_5',u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_2240,plain,(
    v1_subset_1('#skF_5','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2238,c_1658])).

tff(c_1659,plain,(
    ! [A_254,B_255] :
      ( m1_subset_1(A_254,k1_zfmisc_1(B_255))
      | ~ r1_tarski(A_254,B_255) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_30,plain,(
    ! [B_26] :
      ( ~ v1_subset_1(B_26,B_26)
      | ~ m1_subset_1(B_26,k1_zfmisc_1(B_26)) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_1664,plain,(
    ! [B_255] :
      ( ~ v1_subset_1(B_255,B_255)
      | ~ r1_tarski(B_255,B_255) ) ),
    inference(resolution,[status(thm)],[c_1659,c_30])).

tff(c_2397,plain,(
    ~ r1_tarski('#skF_5','#skF_5') ),
    inference(resolution,[status(thm)],[c_2240,c_1664])).

tff(c_2401,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1893,c_2397])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.01/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:07:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.63/1.87  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.63/1.88  
% 4.63/1.88  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.63/1.88  %$ v3_tex_2 > v2_tex_2 > v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_tdlat_3 > l1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_3 > #skF_5 > #skF_2 > #skF_4
% 4.63/1.88  
% 4.63/1.88  %Foreground sorts:
% 4.63/1.88  
% 4.63/1.88  
% 4.63/1.88  %Background operators:
% 4.63/1.88  
% 4.63/1.88  
% 4.63/1.88  %Foreground operators:
% 4.63/1.88  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.63/1.88  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 4.63/1.88  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.63/1.88  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.63/1.88  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 4.63/1.88  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.63/1.88  tff(v1_tdlat_3, type, v1_tdlat_3: $i > $o).
% 4.63/1.88  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.63/1.88  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.63/1.88  tff('#skF_5', type, '#skF_5': $i).
% 4.63/1.88  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 4.63/1.88  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 4.63/1.88  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.63/1.88  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.63/1.88  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.63/1.88  tff('#skF_4', type, '#skF_4': $i).
% 4.63/1.88  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.63/1.88  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 4.63/1.88  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.63/1.88  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.63/1.88  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.63/1.88  
% 4.89/1.90  tff(f_132, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v1_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tex_2(B, A) <=> ~v1_subset_1(B, u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_tex_2)).
% 4.89/1.90  tff(f_46, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((![D]: (m1_subset_1(D, A) => (r2_hidden(D, B) => r2_hidden(D, C)))) => r1_tarski(B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_subset_1)).
% 4.89/1.90  tff(f_75, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tsep_1)).
% 4.89/1.90  tff(f_71, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 4.89/1.90  tff(f_64, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 4.89/1.90  tff(f_114, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v1_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => v2_tex_2(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_tex_2)).
% 4.89/1.90  tff(f_82, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (v1_subset_1(B, A) <=> ~(B = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_subset_1)).
% 4.89/1.90  tff(f_100, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tex_2(B, A) <=> (v2_tex_2(B, A) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v2_tex_2(C, A) & r1_tarski(B, C)) => (B = C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_tex_2)).
% 4.89/1.90  tff(f_60, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((![D]: (m1_subset_1(D, A) => (r2_hidden(D, B) <=> r2_hidden(D, C)))) => (B = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_subset_1)).
% 4.89/1.90  tff(f_32, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 4.89/1.90  tff(c_46, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_132])).
% 4.89/1.90  tff(c_6, plain, (![A_5, B_6, C_10]: (r2_hidden('#skF_1'(A_5, B_6, C_10), B_6) | r1_tarski(B_6, C_10) | ~m1_subset_1(C_10, k1_zfmisc_1(A_5)) | ~m1_subset_1(B_6, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.89/1.90  tff(c_1870, plain, (![A_298, B_299, C_300]: (~r2_hidden('#skF_1'(A_298, B_299, C_300), C_300) | r1_tarski(B_299, C_300) | ~m1_subset_1(C_300, k1_zfmisc_1(A_298)) | ~m1_subset_1(B_299, k1_zfmisc_1(A_298)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.89/1.90  tff(c_1876, plain, (![B_301, A_302]: (r1_tarski(B_301, B_301) | ~m1_subset_1(B_301, k1_zfmisc_1(A_302)))), inference(resolution, [status(thm)], [c_6, c_1870])).
% 4.89/1.90  tff(c_1893, plain, (r1_tarski('#skF_5', '#skF_5')), inference(resolution, [status(thm)], [c_46, c_1876])).
% 4.89/1.90  tff(c_54, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_132])).
% 4.89/1.90  tff(c_48, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_132])).
% 4.89/1.90  tff(c_52, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_132])).
% 4.89/1.90  tff(c_50, plain, (v1_tdlat_3('#skF_4')), inference(cnfTransformation, [status(thm)], [f_132])).
% 4.89/1.90  tff(c_26, plain, (![A_24]: (m1_pre_topc(A_24, A_24) | ~l1_pre_topc(A_24))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.89/1.90  tff(c_24, plain, (![B_23, A_21]: (m1_subset_1(u1_struct_0(B_23), k1_zfmisc_1(u1_struct_0(A_21))) | ~m1_pre_topc(B_23, A_21) | ~l1_pre_topc(A_21))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.89/1.90  tff(c_1927, plain, (![B_307, A_308]: (r1_tarski(u1_struct_0(B_307), u1_struct_0(B_307)) | ~m1_pre_topc(B_307, A_308) | ~l1_pre_topc(A_308))), inference(resolution, [status(thm)], [c_24, c_1876])).
% 4.89/1.90  tff(c_1931, plain, (![A_309]: (r1_tarski(u1_struct_0(A_309), u1_struct_0(A_309)) | ~l1_pre_topc(A_309))), inference(resolution, [status(thm)], [c_26, c_1927])).
% 4.89/1.90  tff(c_22, plain, (![A_19, B_20]: (m1_subset_1(A_19, k1_zfmisc_1(B_20)) | ~r1_tarski(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.89/1.90  tff(c_1773, plain, (![B_282, A_283]: (v2_tex_2(B_282, A_283) | ~m1_subset_1(B_282, k1_zfmisc_1(u1_struct_0(A_283))) | ~l1_pre_topc(A_283) | ~v1_tdlat_3(A_283) | ~v2_pre_topc(A_283) | v2_struct_0(A_283))), inference(cnfTransformation, [status(thm)], [f_114])).
% 4.89/1.90  tff(c_1790, plain, (![A_19, A_283]: (v2_tex_2(A_19, A_283) | ~l1_pre_topc(A_283) | ~v1_tdlat_3(A_283) | ~v2_pre_topc(A_283) | v2_struct_0(A_283) | ~r1_tarski(A_19, u1_struct_0(A_283)))), inference(resolution, [status(thm)], [c_22, c_1773])).
% 4.89/1.90  tff(c_1945, plain, (![A_309]: (v2_tex_2(u1_struct_0(A_309), A_309) | ~v1_tdlat_3(A_309) | ~v2_pre_topc(A_309) | v2_struct_0(A_309) | ~l1_pre_topc(A_309))), inference(resolution, [status(thm)], [c_1931, c_1790])).
% 4.89/1.90  tff(c_62, plain, (v3_tex_2('#skF_5', '#skF_4') | ~v1_subset_1('#skF_5', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_132])).
% 4.89/1.90  tff(c_65, plain, (~v1_subset_1('#skF_5', u1_struct_0('#skF_4'))), inference(splitLeft, [status(thm)], [c_62])).
% 4.89/1.90  tff(c_56, plain, (v1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~v3_tex_2('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_132])).
% 4.89/1.90  tff(c_66, plain, (~v3_tex_2('#skF_5', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_65, c_56])).
% 4.89/1.90  tff(c_83, plain, (![B_48, A_49]: (v1_subset_1(B_48, A_49) | B_48=A_49 | ~m1_subset_1(B_48, k1_zfmisc_1(A_49)))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.89/1.90  tff(c_89, plain, (v1_subset_1('#skF_5', u1_struct_0('#skF_4')) | u1_struct_0('#skF_4')='#skF_5'), inference(resolution, [status(thm)], [c_46, c_83])).
% 4.89/1.90  tff(c_93, plain, (u1_struct_0('#skF_4')='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_65, c_89])).
% 4.89/1.90  tff(c_97, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_93, c_46])).
% 4.89/1.90  tff(c_333, plain, (![B_83, A_84]: (v2_tex_2(B_83, A_84) | ~m1_subset_1(B_83, k1_zfmisc_1(u1_struct_0(A_84))) | ~l1_pre_topc(A_84) | ~v1_tdlat_3(A_84) | ~v2_pre_topc(A_84) | v2_struct_0(A_84))), inference(cnfTransformation, [status(thm)], [f_114])).
% 4.89/1.90  tff(c_346, plain, (![B_83]: (v2_tex_2(B_83, '#skF_4') | ~m1_subset_1(B_83, k1_zfmisc_1('#skF_5')) | ~l1_pre_topc('#skF_4') | ~v1_tdlat_3('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_93, c_333])).
% 4.89/1.90  tff(c_355, plain, (![B_83]: (v2_tex_2(B_83, '#skF_4') | ~m1_subset_1(B_83, k1_zfmisc_1('#skF_5')) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_346])).
% 4.89/1.90  tff(c_358, plain, (![B_85]: (v2_tex_2(B_85, '#skF_4') | ~m1_subset_1(B_85, k1_zfmisc_1('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_54, c_355])).
% 4.89/1.90  tff(c_375, plain, (v2_tex_2('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_97, c_358])).
% 4.89/1.90  tff(c_793, plain, (![A_141, B_142]: (m1_subset_1('#skF_3'(A_141, B_142), k1_zfmisc_1(u1_struct_0(A_141))) | v3_tex_2(B_142, A_141) | ~v2_tex_2(B_142, A_141) | ~m1_subset_1(B_142, k1_zfmisc_1(u1_struct_0(A_141))) | ~l1_pre_topc(A_141))), inference(cnfTransformation, [status(thm)], [f_100])).
% 4.89/1.90  tff(c_817, plain, (![B_142]: (m1_subset_1('#skF_3'('#skF_4', B_142), k1_zfmisc_1('#skF_5')) | v3_tex_2(B_142, '#skF_4') | ~v2_tex_2(B_142, '#skF_4') | ~m1_subset_1(B_142, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_93, c_793])).
% 4.89/1.90  tff(c_829, plain, (![B_143]: (m1_subset_1('#skF_3'('#skF_4', B_143), k1_zfmisc_1('#skF_5')) | v3_tex_2(B_143, '#skF_4') | ~v2_tex_2(B_143, '#skF_4') | ~m1_subset_1(B_143, k1_zfmisc_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_93, c_817])).
% 4.89/1.90  tff(c_20, plain, (![A_19, B_20]: (r1_tarski(A_19, B_20) | ~m1_subset_1(A_19, k1_zfmisc_1(B_20)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.89/1.90  tff(c_848, plain, (![B_143]: (r1_tarski('#skF_3'('#skF_4', B_143), '#skF_5') | v3_tex_2(B_143, '#skF_4') | ~v2_tex_2(B_143, '#skF_4') | ~m1_subset_1(B_143, k1_zfmisc_1('#skF_5')))), inference(resolution, [status(thm)], [c_829, c_20])).
% 4.89/1.90  tff(c_471, plain, (![A_106, B_107]: ('#skF_3'(A_106, B_107)!=B_107 | v3_tex_2(B_107, A_106) | ~v2_tex_2(B_107, A_106) | ~m1_subset_1(B_107, k1_zfmisc_1(u1_struct_0(A_106))) | ~l1_pre_topc(A_106))), inference(cnfTransformation, [status(thm)], [f_100])).
% 4.89/1.90  tff(c_484, plain, (![B_107]: ('#skF_3'('#skF_4', B_107)!=B_107 | v3_tex_2(B_107, '#skF_4') | ~v2_tex_2(B_107, '#skF_4') | ~m1_subset_1(B_107, k1_zfmisc_1('#skF_5')) | ~l1_pre_topc('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_93, c_471])).
% 4.89/1.90  tff(c_521, plain, (![B_111]: ('#skF_3'('#skF_4', B_111)!=B_111 | v3_tex_2(B_111, '#skF_4') | ~v2_tex_2(B_111, '#skF_4') | ~m1_subset_1(B_111, k1_zfmisc_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_484])).
% 4.89/1.90  tff(c_531, plain, ('#skF_3'('#skF_4', '#skF_5')!='#skF_5' | v3_tex_2('#skF_5', '#skF_4') | ~v2_tex_2('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_97, c_521])).
% 4.89/1.90  tff(c_540, plain, ('#skF_3'('#skF_4', '#skF_5')!='#skF_5' | v3_tex_2('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_375, c_531])).
% 4.89/1.90  tff(c_541, plain, ('#skF_3'('#skF_4', '#skF_5')!='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_66, c_540])).
% 4.89/1.90  tff(c_408, plain, (![A_98, B_99, C_100]: (~r2_hidden('#skF_1'(A_98, B_99, C_100), C_100) | r1_tarski(B_99, C_100) | ~m1_subset_1(C_100, k1_zfmisc_1(A_98)) | ~m1_subset_1(B_99, k1_zfmisc_1(A_98)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.89/1.90  tff(c_414, plain, (![B_101, A_102]: (r1_tarski(B_101, B_101) | ~m1_subset_1(B_101, k1_zfmisc_1(A_102)))), inference(resolution, [status(thm)], [c_6, c_408])).
% 4.89/1.90  tff(c_495, plain, (![B_108, A_109]: (r1_tarski(u1_struct_0(B_108), u1_struct_0(B_108)) | ~m1_pre_topc(B_108, A_109) | ~l1_pre_topc(A_109))), inference(resolution, [status(thm)], [c_24, c_414])).
% 4.89/1.90  tff(c_498, plain, (![A_24]: (r1_tarski(u1_struct_0(A_24), u1_struct_0(A_24)) | ~l1_pre_topc(A_24))), inference(resolution, [status(thm)], [c_26, c_495])).
% 4.89/1.90  tff(c_717, plain, (![B_128, A_129]: (r1_tarski(B_128, '#skF_3'(A_129, B_128)) | v3_tex_2(B_128, A_129) | ~v2_tex_2(B_128, A_129) | ~m1_subset_1(B_128, k1_zfmisc_1(u1_struct_0(A_129))) | ~l1_pre_topc(A_129))), inference(cnfTransformation, [status(thm)], [f_100])).
% 4.89/1.90  tff(c_751, plain, (![A_135, A_136]: (r1_tarski(A_135, '#skF_3'(A_136, A_135)) | v3_tex_2(A_135, A_136) | ~v2_tex_2(A_135, A_136) | ~l1_pre_topc(A_136) | ~r1_tarski(A_135, u1_struct_0(A_136)))), inference(resolution, [status(thm)], [c_22, c_717])).
% 4.89/1.90  tff(c_773, plain, (![A_140]: (r1_tarski(u1_struct_0(A_140), '#skF_3'(A_140, u1_struct_0(A_140))) | v3_tex_2(u1_struct_0(A_140), A_140) | ~v2_tex_2(u1_struct_0(A_140), A_140) | ~l1_pre_topc(A_140))), inference(resolution, [status(thm)], [c_498, c_751])).
% 4.89/1.90  tff(c_778, plain, (r1_tarski('#skF_5', '#skF_3'('#skF_4', u1_struct_0('#skF_4'))) | v3_tex_2(u1_struct_0('#skF_4'), '#skF_4') | ~v2_tex_2(u1_struct_0('#skF_4'), '#skF_4') | ~l1_pre_topc('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_93, c_773])).
% 4.89/1.90  tff(c_784, plain, (r1_tarski('#skF_5', '#skF_3'('#skF_4', '#skF_5')) | v3_tex_2('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_375, c_93, c_93, c_93, c_778])).
% 4.89/1.90  tff(c_785, plain, (r1_tarski('#skF_5', '#skF_3'('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_66, c_784])).
% 4.89/1.90  tff(c_939, plain, (![A_155, B_156, C_157]: (r2_hidden('#skF_2'(A_155, B_156, C_157), B_156) | r2_hidden('#skF_2'(A_155, B_156, C_157), C_157) | C_157=B_156 | ~m1_subset_1(C_157, k1_zfmisc_1(A_155)) | ~m1_subset_1(B_156, k1_zfmisc_1(A_155)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.89/1.90  tff(c_2, plain, (![C_4, A_1, B_2]: (r2_hidden(C_4, A_1) | ~r2_hidden(C_4, B_2) | ~m1_subset_1(B_2, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.89/1.90  tff(c_945, plain, (![A_155, B_156, C_157, A_1]: (r2_hidden('#skF_2'(A_155, B_156, C_157), A_1) | ~m1_subset_1(C_157, k1_zfmisc_1(A_1)) | r2_hidden('#skF_2'(A_155, B_156, C_157), B_156) | C_157=B_156 | ~m1_subset_1(C_157, k1_zfmisc_1(A_155)) | ~m1_subset_1(B_156, k1_zfmisc_1(A_155)))), inference(resolution, [status(thm)], [c_939, c_2])).
% 4.89/1.90  tff(c_1308, plain, (![C_157, B_156, A_155]: (~m1_subset_1(C_157, k1_zfmisc_1(B_156)) | C_157=B_156 | ~m1_subset_1(C_157, k1_zfmisc_1(A_155)) | ~m1_subset_1(B_156, k1_zfmisc_1(A_155)) | r2_hidden('#skF_2'(A_155, B_156, C_157), B_156))), inference(factorization, [status(thm), theory('equality')], [c_945])).
% 4.89/1.90  tff(c_1409, plain, (![C_226, B_227, A_228]: (~m1_subset_1(C_226, k1_zfmisc_1(B_227)) | C_226=B_227 | ~m1_subset_1(C_226, k1_zfmisc_1(A_228)) | ~m1_subset_1(B_227, k1_zfmisc_1(A_228)) | r2_hidden('#skF_2'(A_228, B_227, C_226), B_227))), inference(factorization, [status(thm), theory('equality')], [c_945])).
% 4.89/1.90  tff(c_1419, plain, (![A_232, B_233, C_234, A_235]: (r2_hidden('#skF_2'(A_232, B_233, C_234), A_235) | ~m1_subset_1(B_233, k1_zfmisc_1(A_235)) | ~m1_subset_1(C_234, k1_zfmisc_1(B_233)) | C_234=B_233 | ~m1_subset_1(C_234, k1_zfmisc_1(A_232)) | ~m1_subset_1(B_233, k1_zfmisc_1(A_232)))), inference(resolution, [status(thm)], [c_1409, c_2])).
% 4.89/1.90  tff(c_12, plain, (![A_12, B_13, C_17]: (~r2_hidden('#skF_2'(A_12, B_13, C_17), C_17) | ~r2_hidden('#skF_2'(A_12, B_13, C_17), B_13) | C_17=B_13 | ~m1_subset_1(C_17, k1_zfmisc_1(A_12)) | ~m1_subset_1(B_13, k1_zfmisc_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.89/1.90  tff(c_1427, plain, (![A_236, B_237, A_238]: (~r2_hidden('#skF_2'(A_236, B_237, A_238), B_237) | ~m1_subset_1(B_237, k1_zfmisc_1(A_238)) | ~m1_subset_1(A_238, k1_zfmisc_1(B_237)) | B_237=A_238 | ~m1_subset_1(A_238, k1_zfmisc_1(A_236)) | ~m1_subset_1(B_237, k1_zfmisc_1(A_236)))), inference(resolution, [status(thm)], [c_1419, c_12])).
% 4.89/1.90  tff(c_1449, plain, (![B_239, C_240, A_241]: (~m1_subset_1(B_239, k1_zfmisc_1(C_240)) | ~m1_subset_1(C_240, k1_zfmisc_1(B_239)) | C_240=B_239 | ~m1_subset_1(C_240, k1_zfmisc_1(A_241)) | ~m1_subset_1(B_239, k1_zfmisc_1(A_241)))), inference(resolution, [status(thm)], [c_1308, c_1427])).
% 4.89/1.90  tff(c_1516, plain, (![B_246, A_247, A_248]: (~m1_subset_1(B_246, k1_zfmisc_1(A_247)) | B_246=A_247 | ~m1_subset_1(B_246, k1_zfmisc_1(A_248)) | ~m1_subset_1(A_247, k1_zfmisc_1(A_248)) | ~r1_tarski(A_247, B_246))), inference(resolution, [status(thm)], [c_22, c_1449])).
% 4.89/1.90  tff(c_1549, plain, (![B_249, A_250, A_251]: (B_249=A_250 | ~m1_subset_1(A_250, k1_zfmisc_1(A_251)) | ~m1_subset_1(B_249, k1_zfmisc_1(A_251)) | ~r1_tarski(B_249, A_250) | ~r1_tarski(A_250, B_249))), inference(resolution, [status(thm)], [c_22, c_1516])).
% 4.89/1.90  tff(c_1579, plain, (![B_252]: (B_252='#skF_5' | ~m1_subset_1(B_252, k1_zfmisc_1('#skF_5')) | ~r1_tarski(B_252, '#skF_5') | ~r1_tarski('#skF_5', B_252))), inference(resolution, [status(thm)], [c_97, c_1549])).
% 4.89/1.90  tff(c_1610, plain, (![A_253]: (A_253='#skF_5' | ~r1_tarski('#skF_5', A_253) | ~r1_tarski(A_253, '#skF_5'))), inference(resolution, [status(thm)], [c_22, c_1579])).
% 4.89/1.90  tff(c_1615, plain, ('#skF_3'('#skF_4', '#skF_5')='#skF_5' | ~r1_tarski('#skF_3'('#skF_4', '#skF_5'), '#skF_5')), inference(resolution, [status(thm)], [c_785, c_1610])).
% 4.89/1.90  tff(c_1634, plain, (~r1_tarski('#skF_3'('#skF_4', '#skF_5'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_541, c_1615])).
% 4.89/1.90  tff(c_1651, plain, (v3_tex_2('#skF_5', '#skF_4') | ~v2_tex_2('#skF_5', '#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_5'))), inference(resolution, [status(thm)], [c_848, c_1634])).
% 4.89/1.90  tff(c_1654, plain, (v3_tex_2('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_97, c_375, c_1651])).
% 4.89/1.90  tff(c_1656, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_1654])).
% 4.89/1.90  tff(c_1657, plain, (v3_tex_2('#skF_5', '#skF_4')), inference(splitRight, [status(thm)], [c_62])).
% 4.89/1.90  tff(c_1668, plain, (![A_257, B_258]: (r1_tarski(A_257, B_258) | ~m1_subset_1(A_257, k1_zfmisc_1(B_258)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.89/1.90  tff(c_1676, plain, (r1_tarski('#skF_5', u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_46, c_1668])).
% 4.89/1.90  tff(c_2138, plain, (![C_344, B_345, A_346]: (C_344=B_345 | ~r1_tarski(B_345, C_344) | ~v2_tex_2(C_344, A_346) | ~m1_subset_1(C_344, k1_zfmisc_1(u1_struct_0(A_346))) | ~v3_tex_2(B_345, A_346) | ~m1_subset_1(B_345, k1_zfmisc_1(u1_struct_0(A_346))) | ~l1_pre_topc(A_346))), inference(cnfTransformation, [status(thm)], [f_100])).
% 4.89/1.90  tff(c_2171, plain, (![A_346]: (u1_struct_0('#skF_4')='#skF_5' | ~v2_tex_2(u1_struct_0('#skF_4'), A_346) | ~m1_subset_1(u1_struct_0('#skF_4'), k1_zfmisc_1(u1_struct_0(A_346))) | ~v3_tex_2('#skF_5', A_346) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0(A_346))) | ~l1_pre_topc(A_346))), inference(resolution, [status(thm)], [c_1676, c_2138])).
% 4.89/1.90  tff(c_2190, plain, (![A_354]: (~v2_tex_2(u1_struct_0('#skF_4'), A_354) | ~m1_subset_1(u1_struct_0('#skF_4'), k1_zfmisc_1(u1_struct_0(A_354))) | ~v3_tex_2('#skF_5', A_354) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0(A_354))) | ~l1_pre_topc(A_354))), inference(splitLeft, [status(thm)], [c_2171])).
% 4.89/1.90  tff(c_2201, plain, (![A_357]: (~v2_tex_2(u1_struct_0('#skF_4'), A_357) | ~v3_tex_2('#skF_5', A_357) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0(A_357))) | ~m1_pre_topc('#skF_4', A_357) | ~l1_pre_topc(A_357))), inference(resolution, [status(thm)], [c_24, c_2190])).
% 4.89/1.90  tff(c_2207, plain, (~v2_tex_2(u1_struct_0('#skF_4'), '#skF_4') | ~v3_tex_2('#skF_5', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_46, c_2201])).
% 4.89/1.90  tff(c_2211, plain, (~v2_tex_2(u1_struct_0('#skF_4'), '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_1657, c_2207])).
% 4.89/1.90  tff(c_2212, plain, (~m1_pre_topc('#skF_4', '#skF_4')), inference(splitLeft, [status(thm)], [c_2211])).
% 4.89/1.90  tff(c_2215, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_26, c_2212])).
% 4.89/1.90  tff(c_2219, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_2215])).
% 4.89/1.90  tff(c_2220, plain, (~v2_tex_2(u1_struct_0('#skF_4'), '#skF_4')), inference(splitRight, [status(thm)], [c_2211])).
% 4.89/1.90  tff(c_2229, plain, (~v1_tdlat_3('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_1945, c_2220])).
% 4.89/1.90  tff(c_2235, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_52, c_50, c_2229])).
% 4.89/1.90  tff(c_2237, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_2235])).
% 4.89/1.90  tff(c_2238, plain, (u1_struct_0('#skF_4')='#skF_5'), inference(splitRight, [status(thm)], [c_2171])).
% 4.89/1.90  tff(c_1658, plain, (v1_subset_1('#skF_5', u1_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_62])).
% 4.89/1.90  tff(c_2240, plain, (v1_subset_1('#skF_5', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_2238, c_1658])).
% 4.89/1.90  tff(c_1659, plain, (![A_254, B_255]: (m1_subset_1(A_254, k1_zfmisc_1(B_255)) | ~r1_tarski(A_254, B_255))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.89/1.90  tff(c_30, plain, (![B_26]: (~v1_subset_1(B_26, B_26) | ~m1_subset_1(B_26, k1_zfmisc_1(B_26)))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.89/1.90  tff(c_1664, plain, (![B_255]: (~v1_subset_1(B_255, B_255) | ~r1_tarski(B_255, B_255))), inference(resolution, [status(thm)], [c_1659, c_30])).
% 4.89/1.90  tff(c_2397, plain, (~r1_tarski('#skF_5', '#skF_5')), inference(resolution, [status(thm)], [c_2240, c_1664])).
% 4.89/1.90  tff(c_2401, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1893, c_2397])).
% 4.89/1.90  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.89/1.90  
% 4.89/1.90  Inference rules
% 4.89/1.90  ----------------------
% 4.89/1.90  #Ref     : 0
% 4.89/1.90  #Sup     : 508
% 4.89/1.90  #Fact    : 6
% 4.89/1.91  #Define  : 0
% 4.89/1.91  #Split   : 3
% 4.89/1.91  #Chain   : 0
% 4.89/1.91  #Close   : 0
% 4.89/1.91  
% 4.89/1.91  Ordering : KBO
% 4.89/1.91  
% 4.89/1.91  Simplification rules
% 4.89/1.91  ----------------------
% 4.89/1.91  #Subsume      : 108
% 4.89/1.91  #Demod        : 293
% 4.89/1.91  #Tautology    : 99
% 4.89/1.91  #SimpNegUnit  : 33
% 4.89/1.91  #BackRed      : 6
% 4.89/1.91  
% 4.89/1.91  #Partial instantiations: 0
% 4.89/1.91  #Strategies tried      : 1
% 4.89/1.91  
% 4.89/1.91  Timing (in seconds)
% 4.89/1.91  ----------------------
% 4.89/1.91  Preprocessing        : 0.31
% 4.89/1.91  Parsing              : 0.17
% 4.89/1.91  CNF conversion       : 0.02
% 4.89/1.91  Main loop            : 0.77
% 4.89/1.91  Inferencing          : 0.29
% 4.89/1.91  Reduction            : 0.19
% 4.89/1.91  Demodulation         : 0.11
% 4.89/1.91  BG Simplification    : 0.03
% 4.89/1.91  Subsumption          : 0.20
% 4.89/1.91  Abstraction          : 0.03
% 4.89/1.91  MUC search           : 0.00
% 4.89/1.91  Cooper               : 0.00
% 4.89/1.91  Total                : 1.12
% 4.89/1.91  Index Insertion      : 0.00
% 4.89/1.91  Index Deletion       : 0.00
% 4.89/1.91  Index Matching       : 0.00
% 4.89/1.91  BG Taut test         : 0.00
%------------------------------------------------------------------------------
