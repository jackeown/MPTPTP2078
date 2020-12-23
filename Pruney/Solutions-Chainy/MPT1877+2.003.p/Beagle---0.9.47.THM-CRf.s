%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:57 EST 2020

% Result     : Theorem 16.84s
% Output     : CNFRefutation 16.84s
% Verified   : 
% Statistics : Number of formulae       :  170 ( 883 expanded)
%              Number of leaves         :   28 ( 302 expanded)
%              Depth                    :   23
%              Number of atoms          :  637 (3282 expanded)
%              Number of equality atoms :   66 ( 895 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_tex_2 > v3_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > l1_pre_topc > k9_subset_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(g1_pre_topc,type,(
    g1_pre_topc: ( $i * $i ) > $i )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

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

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_106,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( l1_pre_topc(B)
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(B)))
                   => ( ( g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) = g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))
                        & C = D
                        & v3_tex_2(C,A) )
                     => v3_tex_2(D,B) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_tex_2)).

tff(f_68,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tex_2(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ~ ( r1_tarski(C,B)
                    & ! [D] :
                        ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                       => ~ ( v3_pre_topc(D,A)
                            & k9_subset_1(u1_struct_0(A),B,D) = C ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tex_2)).

tff(f_38,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_subset_1(u1_pre_topc(A),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ! [C,D] :
          ( g1_pre_topc(A,B) = g1_pre_topc(C,D)
         => ( A = C
            & B = D ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',free_g1_pre_topc)).

tff(f_86,axiom,(
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

tff(f_34,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_pre_topc(B,A)
          <=> r2_hidden(B,u1_pre_topc(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_pre_topc)).

tff(c_40,plain,(
    '#skF_7' = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_36,plain,(
    ~ v3_tex_2('#skF_7','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_52,plain,(
    ~ v3_tex_2('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_36])).

tff(c_46,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_48,plain,(
    l1_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_44,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_51,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_44])).

tff(c_128,plain,(
    ! [A_74,B_75] :
      ( r1_tarski('#skF_2'(A_74,B_75),B_75)
      | v2_tex_2(B_75,A_74)
      | ~ m1_subset_1(B_75,k1_zfmisc_1(u1_struct_0(A_74)))
      | ~ l1_pre_topc(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_132,plain,
    ( r1_tarski('#skF_2'('#skF_5','#skF_6'),'#skF_6')
    | v2_tex_2('#skF_6','#skF_5')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_51,c_128])).

tff(c_138,plain,
    ( r1_tarski('#skF_2'('#skF_5','#skF_6'),'#skF_6')
    | v2_tex_2('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_132])).

tff(c_139,plain,(
    v2_tex_2('#skF_6','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_138])).

tff(c_50,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_38,plain,(
    v3_tex_2('#skF_6','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_6,plain,(
    ! [A_4] :
      ( m1_subset_1(u1_pre_topc(A_4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_4))))
      | ~ l1_pre_topc(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_42,plain,(
    g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')) = g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_79,plain,(
    ! [C_60,A_61,D_62,B_63] :
      ( C_60 = A_61
      | g1_pre_topc(C_60,D_62) != g1_pre_topc(A_61,B_63)
      | ~ m1_subset_1(B_63,k1_zfmisc_1(k1_zfmisc_1(A_61))) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_121,plain,(
    ! [A_72,B_73] :
      ( u1_struct_0('#skF_5') = A_72
      | g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')) != g1_pre_topc(A_72,B_73)
      | ~ m1_subset_1(B_73,k1_zfmisc_1(k1_zfmisc_1(A_72))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_79])).

tff(c_125,plain,(
    ! [A_4] :
      ( u1_struct_0(A_4) = u1_struct_0('#skF_5')
      | g1_pre_topc(u1_struct_0(A_4),u1_pre_topc(A_4)) != g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))
      | ~ l1_pre_topc(A_4) ) ),
    inference(resolution,[status(thm)],[c_6,c_121])).

tff(c_163,plain,
    ( u1_struct_0('#skF_5') = u1_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_125])).

tff(c_165,plain,(
    u1_struct_0('#skF_5') = u1_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_163])).

tff(c_523,plain,(
    ! [A_104,B_105] :
      ( m1_subset_1('#skF_3'(A_104,B_105),k1_zfmisc_1(u1_struct_0(A_104)))
      | v3_tex_2(B_105,A_104)
      | ~ v2_tex_2(B_105,A_104)
      | ~ m1_subset_1(B_105,k1_zfmisc_1(u1_struct_0(A_104)))
      | ~ l1_pre_topc(A_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_570,plain,(
    ! [B_105] :
      ( m1_subset_1('#skF_3'('#skF_5',B_105),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v3_tex_2(B_105,'#skF_5')
      | ~ v2_tex_2(B_105,'#skF_5')
      | ~ m1_subset_1(B_105,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_165,c_523])).

tff(c_600,plain,(
    ! [B_105] :
      ( m1_subset_1('#skF_3'('#skF_5',B_105),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v3_tex_2(B_105,'#skF_5')
      | ~ v2_tex_2(B_105,'#skF_5')
      | ~ m1_subset_1(B_105,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_165,c_570])).

tff(c_281,plain,(
    ! [A_85,B_86] :
      ( '#skF_3'(A_85,B_86) != B_86
      | v3_tex_2(B_86,A_85)
      | ~ v2_tex_2(B_86,A_85)
      | ~ m1_subset_1(B_86,k1_zfmisc_1(u1_struct_0(A_85)))
      | ~ l1_pre_topc(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_284,plain,(
    ! [B_86] :
      ( '#skF_3'('#skF_5',B_86) != B_86
      | v3_tex_2(B_86,'#skF_5')
      | ~ v2_tex_2(B_86,'#skF_5')
      | ~ m1_subset_1(B_86,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_165,c_281])).

tff(c_342,plain,(
    ! [B_88] :
      ( '#skF_3'('#skF_5',B_88) != B_88
      | v3_tex_2(B_88,'#skF_5')
      | ~ v2_tex_2(B_88,'#skF_5')
      | ~ m1_subset_1(B_88,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_284])).

tff(c_352,plain,
    ( '#skF_3'('#skF_5','#skF_6') != '#skF_6'
    | v3_tex_2('#skF_6','#skF_5')
    | ~ v2_tex_2('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_46,c_342])).

tff(c_359,plain,
    ( '#skF_3'('#skF_5','#skF_6') != '#skF_6'
    | v3_tex_2('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_352])).

tff(c_360,plain,(
    '#skF_3'('#skF_5','#skF_6') != '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_359])).

tff(c_410,plain,(
    ! [B_94,A_95] :
      ( r1_tarski(B_94,'#skF_3'(A_95,B_94))
      | v3_tex_2(B_94,A_95)
      | ~ v2_tex_2(B_94,A_95)
      | ~ m1_subset_1(B_94,k1_zfmisc_1(u1_struct_0(A_95)))
      | ~ l1_pre_topc(A_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_414,plain,(
    ! [B_94] :
      ( r1_tarski(B_94,'#skF_3'('#skF_5',B_94))
      | v3_tex_2(B_94,'#skF_5')
      | ~ v2_tex_2(B_94,'#skF_5')
      | ~ m1_subset_1(B_94,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_165,c_410])).

tff(c_470,plain,(
    ! [B_100] :
      ( r1_tarski(B_100,'#skF_3'('#skF_5',B_100))
      | v3_tex_2(B_100,'#skF_5')
      | ~ v2_tex_2(B_100,'#skF_5')
      | ~ m1_subset_1(B_100,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_414])).

tff(c_477,plain,
    ( r1_tarski('#skF_6','#skF_3'('#skF_5','#skF_6'))
    | v3_tex_2('#skF_6','#skF_5')
    | ~ v2_tex_2('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_46,c_470])).

tff(c_484,plain,
    ( r1_tarski('#skF_6','#skF_3'('#skF_5','#skF_6'))
    | v3_tex_2('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_477])).

tff(c_485,plain,(
    r1_tarski('#skF_6','#skF_3'('#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_484])).

tff(c_765,plain,(
    ! [C_113,B_114,A_115] :
      ( C_113 = B_114
      | ~ r1_tarski(B_114,C_113)
      | ~ v2_tex_2(C_113,A_115)
      | ~ m1_subset_1(C_113,k1_zfmisc_1(u1_struct_0(A_115)))
      | ~ v3_tex_2(B_114,A_115)
      | ~ m1_subset_1(B_114,k1_zfmisc_1(u1_struct_0(A_115)))
      | ~ l1_pre_topc(A_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_767,plain,(
    ! [A_115] :
      ( '#skF_3'('#skF_5','#skF_6') = '#skF_6'
      | ~ v2_tex_2('#skF_3'('#skF_5','#skF_6'),A_115)
      | ~ m1_subset_1('#skF_3'('#skF_5','#skF_6'),k1_zfmisc_1(u1_struct_0(A_115)))
      | ~ v3_tex_2('#skF_6',A_115)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0(A_115)))
      | ~ l1_pre_topc(A_115) ) ),
    inference(resolution,[status(thm)],[c_485,c_765])).

tff(c_810,plain,(
    ! [A_119] :
      ( ~ v2_tex_2('#skF_3'('#skF_5','#skF_6'),A_119)
      | ~ m1_subset_1('#skF_3'('#skF_5','#skF_6'),k1_zfmisc_1(u1_struct_0(A_119)))
      | ~ v3_tex_2('#skF_6',A_119)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0(A_119)))
      | ~ l1_pre_topc(A_119) ) ),
    inference(negUnitSimplification,[status(thm)],[c_360,c_767])).

tff(c_814,plain,
    ( ~ v2_tex_2('#skF_3'('#skF_5','#skF_6'),'#skF_4')
    | ~ v3_tex_2('#skF_6','#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | v3_tex_2('#skF_6','#skF_5')
    | ~ v2_tex_2('#skF_6','#skF_5')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(resolution,[status(thm)],[c_600,c_810])).

tff(c_824,plain,
    ( ~ v2_tex_2('#skF_3'('#skF_5','#skF_6'),'#skF_4')
    | v3_tex_2('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_139,c_50,c_38,c_814])).

tff(c_825,plain,(
    ~ v2_tex_2('#skF_3'('#skF_5','#skF_6'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_824])).

tff(c_486,plain,(
    ! [A_101,B_102] :
      ( v2_tex_2('#skF_3'(A_101,B_102),A_101)
      | v3_tex_2(B_102,A_101)
      | ~ v2_tex_2(B_102,A_101)
      | ~ m1_subset_1(B_102,k1_zfmisc_1(u1_struct_0(A_101)))
      | ~ l1_pre_topc(A_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_490,plain,(
    ! [B_102] :
      ( v2_tex_2('#skF_3'('#skF_5',B_102),'#skF_5')
      | v3_tex_2(B_102,'#skF_5')
      | ~ v2_tex_2(B_102,'#skF_5')
      | ~ m1_subset_1(B_102,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_165,c_486])).

tff(c_504,plain,(
    ! [B_103] :
      ( v2_tex_2('#skF_3'('#skF_5',B_103),'#skF_5')
      | v3_tex_2(B_103,'#skF_5')
      | ~ v2_tex_2(B_103,'#skF_5')
      | ~ m1_subset_1(B_103,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_490])).

tff(c_514,plain,
    ( v2_tex_2('#skF_3'('#skF_5','#skF_6'),'#skF_5')
    | v3_tex_2('#skF_6','#skF_5')
    | ~ v2_tex_2('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_46,c_504])).

tff(c_521,plain,
    ( v2_tex_2('#skF_3'('#skF_5','#skF_6'),'#skF_5')
    | v3_tex_2('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_514])).

tff(c_522,plain,(
    v2_tex_2('#skF_3'('#skF_5','#skF_6'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_521])).

tff(c_605,plain,(
    ! [B_106] :
      ( m1_subset_1('#skF_3'('#skF_5',B_106),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v3_tex_2(B_106,'#skF_5')
      | ~ v2_tex_2(B_106,'#skF_5')
      | ~ m1_subset_1(B_106,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_165,c_570])).

tff(c_14,plain,(
    ! [A_11,B_25] :
      ( r1_tarski('#skF_2'(A_11,B_25),B_25)
      | v2_tex_2(B_25,A_11)
      | ~ m1_subset_1(B_25,k1_zfmisc_1(u1_struct_0(A_11)))
      | ~ l1_pre_topc(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_633,plain,(
    ! [B_106] :
      ( r1_tarski('#skF_2'('#skF_4','#skF_3'('#skF_5',B_106)),'#skF_3'('#skF_5',B_106))
      | v2_tex_2('#skF_3'('#skF_5',B_106),'#skF_4')
      | ~ l1_pre_topc('#skF_4')
      | v3_tex_2(B_106,'#skF_5')
      | ~ v2_tex_2(B_106,'#skF_5')
      | ~ m1_subset_1(B_106,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_605,c_14])).

tff(c_661,plain,(
    ! [B_106] :
      ( r1_tarski('#skF_2'('#skF_4','#skF_3'('#skF_5',B_106)),'#skF_3'('#skF_5',B_106))
      | v2_tex_2('#skF_3'('#skF_5',B_106),'#skF_4')
      | v3_tex_2(B_106,'#skF_5')
      | ~ v2_tex_2(B_106,'#skF_5')
      | ~ m1_subset_1(B_106,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_633])).

tff(c_16,plain,(
    ! [A_11,B_25] :
      ( m1_subset_1('#skF_2'(A_11,B_25),k1_zfmisc_1(u1_struct_0(A_11)))
      | v2_tex_2(B_25,A_11)
      | ~ m1_subset_1(B_25,k1_zfmisc_1(u1_struct_0(A_11)))
      | ~ l1_pre_topc(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_869,plain,(
    ! [A_122,B_123,C_124] :
      ( v3_pre_topc('#skF_1'(A_122,B_123,C_124),A_122)
      | ~ r1_tarski(C_124,B_123)
      | ~ m1_subset_1(C_124,k1_zfmisc_1(u1_struct_0(A_122)))
      | ~ v2_tex_2(B_123,A_122)
      | ~ m1_subset_1(B_123,k1_zfmisc_1(u1_struct_0(A_122)))
      | ~ l1_pre_topc(A_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_877,plain,(
    ! [B_123,C_124] :
      ( v3_pre_topc('#skF_1'('#skF_5',B_123,C_124),'#skF_5')
      | ~ r1_tarski(C_124,B_123)
      | ~ m1_subset_1(C_124,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ v2_tex_2(B_123,'#skF_5')
      | ~ m1_subset_1(B_123,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_165,c_869])).

tff(c_1077,plain,(
    ! [B_141,C_142] :
      ( v3_pre_topc('#skF_1'('#skF_5',B_141,C_142),'#skF_5')
      | ~ r1_tarski(C_142,B_141)
      | ~ m1_subset_1(C_142,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ v2_tex_2(B_141,'#skF_5')
      | ~ m1_subset_1(B_141,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_165,c_877])).

tff(c_1087,plain,(
    ! [B_141,B_25] :
      ( v3_pre_topc('#skF_1'('#skF_5',B_141,'#skF_2'('#skF_4',B_25)),'#skF_5')
      | ~ r1_tarski('#skF_2'('#skF_4',B_25),B_141)
      | ~ v2_tex_2(B_141,'#skF_5')
      | ~ m1_subset_1(B_141,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_tex_2(B_25,'#skF_4')
      | ~ m1_subset_1(B_25,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_16,c_1077])).

tff(c_1097,plain,(
    ! [B_141,B_25] :
      ( v3_pre_topc('#skF_1'('#skF_5',B_141,'#skF_2'('#skF_4',B_25)),'#skF_5')
      | ~ r1_tarski('#skF_2'('#skF_4',B_25),B_141)
      | ~ v2_tex_2(B_141,'#skF_5')
      | ~ m1_subset_1(B_141,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_tex_2(B_25,'#skF_4')
      | ~ m1_subset_1(B_25,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_1087])).

tff(c_1129,plain,(
    ! [A_145,B_146,C_147] :
      ( m1_subset_1('#skF_1'(A_145,B_146,C_147),k1_zfmisc_1(u1_struct_0(A_145)))
      | ~ r1_tarski(C_147,B_146)
      | ~ m1_subset_1(C_147,k1_zfmisc_1(u1_struct_0(A_145)))
      | ~ v2_tex_2(B_146,A_145)
      | ~ m1_subset_1(B_146,k1_zfmisc_1(u1_struct_0(A_145)))
      | ~ l1_pre_topc(A_145) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_1225,plain,(
    ! [B_146,C_147] :
      ( m1_subset_1('#skF_1'('#skF_5',B_146,C_147),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r1_tarski(C_147,B_146)
      | ~ m1_subset_1(C_147,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ v2_tex_2(B_146,'#skF_5')
      | ~ m1_subset_1(B_146,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_165,c_1129])).

tff(c_1571,plain,(
    ! [B_172,C_173] :
      ( m1_subset_1('#skF_1'('#skF_5',B_172,C_173),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r1_tarski(C_173,B_172)
      | ~ m1_subset_1(C_173,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ v2_tex_2(B_172,'#skF_5')
      | ~ m1_subset_1(B_172,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_165,c_165,c_1225])).

tff(c_196,plain,
    ( m1_subset_1(u1_pre_topc('#skF_5'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))
    | ~ l1_pre_topc('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_165,c_6])).

tff(c_210,plain,(
    m1_subset_1(u1_pre_topc('#skF_5'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_196])).

tff(c_88,plain,(
    ! [D_64,B_65,C_66,A_67] :
      ( D_64 = B_65
      | g1_pre_topc(C_66,D_64) != g1_pre_topc(A_67,B_65)
      | ~ m1_subset_1(B_65,k1_zfmisc_1(k1_zfmisc_1(A_67))) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_92,plain,(
    ! [D_64,C_66] :
      ( u1_pre_topc('#skF_5') = D_64
      | g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')) != g1_pre_topc(C_66,D_64)
      | ~ m1_subset_1(u1_pre_topc('#skF_5'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_5')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_88])).

tff(c_362,plain,(
    ! [D_64,C_66] :
      ( u1_pre_topc('#skF_5') = D_64
      | g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')) != g1_pre_topc(C_66,D_64) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_210,c_165,c_92])).

tff(c_365,plain,(
    u1_pre_topc('#skF_5') = u1_pre_topc('#skF_4') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_362])).

tff(c_4,plain,(
    ! [B_3,A_1] :
      ( r2_hidden(B_3,u1_pre_topc(A_1))
      | ~ v3_pre_topc(B_3,A_1)
      | ~ m1_subset_1(B_3,k1_zfmisc_1(u1_struct_0(A_1)))
      | ~ l1_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_187,plain,(
    ! [B_3] :
      ( r2_hidden(B_3,u1_pre_topc('#skF_5'))
      | ~ v3_pre_topc(B_3,'#skF_5')
      | ~ m1_subset_1(B_3,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_165,c_4])).

tff(c_204,plain,(
    ! [B_3] :
      ( r2_hidden(B_3,u1_pre_topc('#skF_5'))
      | ~ v3_pre_topc(B_3,'#skF_5')
      | ~ m1_subset_1(B_3,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_187])).

tff(c_373,plain,(
    ! [B_3] :
      ( r2_hidden(B_3,u1_pre_topc('#skF_4'))
      | ~ v3_pre_topc(B_3,'#skF_5')
      | ~ m1_subset_1(B_3,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_365,c_204])).

tff(c_2183,plain,(
    ! [B_250,C_251] :
      ( r2_hidden('#skF_1'('#skF_5',B_250,C_251),u1_pre_topc('#skF_4'))
      | ~ v3_pre_topc('#skF_1'('#skF_5',B_250,C_251),'#skF_5')
      | ~ r1_tarski(C_251,B_250)
      | ~ m1_subset_1(C_251,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ v2_tex_2(B_250,'#skF_5')
      | ~ m1_subset_1(B_250,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_1571,c_373])).

tff(c_2,plain,(
    ! [B_3,A_1] :
      ( v3_pre_topc(B_3,A_1)
      | ~ r2_hidden(B_3,u1_pre_topc(A_1))
      | ~ m1_subset_1(B_3,k1_zfmisc_1(u1_struct_0(A_1)))
      | ~ l1_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_1658,plain,(
    ! [B_172,C_173] :
      ( v3_pre_topc('#skF_1'('#skF_5',B_172,C_173),'#skF_4')
      | ~ r2_hidden('#skF_1'('#skF_5',B_172,C_173),u1_pre_topc('#skF_4'))
      | ~ l1_pre_topc('#skF_4')
      | ~ r1_tarski(C_173,B_172)
      | ~ m1_subset_1(C_173,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ v2_tex_2(B_172,'#skF_5')
      | ~ m1_subset_1(B_172,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_1571,c_2])).

tff(c_1709,plain,(
    ! [B_172,C_173] :
      ( v3_pre_topc('#skF_1'('#skF_5',B_172,C_173),'#skF_4')
      | ~ r2_hidden('#skF_1'('#skF_5',B_172,C_173),u1_pre_topc('#skF_4'))
      | ~ r1_tarski(C_173,B_172)
      | ~ m1_subset_1(C_173,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ v2_tex_2(B_172,'#skF_5')
      | ~ m1_subset_1(B_172,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_1658])).

tff(c_2188,plain,(
    ! [B_252,C_253] :
      ( v3_pre_topc('#skF_1'('#skF_5',B_252,C_253),'#skF_4')
      | ~ v3_pre_topc('#skF_1'('#skF_5',B_252,C_253),'#skF_5')
      | ~ r1_tarski(C_253,B_252)
      | ~ m1_subset_1(C_253,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ v2_tex_2(B_252,'#skF_5')
      | ~ m1_subset_1(B_252,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_2183,c_1709])).

tff(c_2779,plain,(
    ! [B_379,B_380] :
      ( v3_pre_topc('#skF_1'('#skF_5',B_379,'#skF_2'('#skF_4',B_380)),'#skF_4')
      | ~ m1_subset_1('#skF_2'('#skF_4',B_380),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r1_tarski('#skF_2'('#skF_4',B_380),B_379)
      | ~ v2_tex_2(B_379,'#skF_5')
      | ~ m1_subset_1(B_379,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_tex_2(B_380,'#skF_4')
      | ~ m1_subset_1(B_380,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_1097,c_2188])).

tff(c_2782,plain,(
    ! [B_379,B_25] :
      ( v3_pre_topc('#skF_1'('#skF_5',B_379,'#skF_2'('#skF_4',B_25)),'#skF_4')
      | ~ r1_tarski('#skF_2'('#skF_4',B_25),B_379)
      | ~ v2_tex_2(B_379,'#skF_5')
      | ~ m1_subset_1(B_379,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_tex_2(B_25,'#skF_4')
      | ~ m1_subset_1(B_25,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_16,c_2779])).

tff(c_2785,plain,(
    ! [B_379,B_25] :
      ( v3_pre_topc('#skF_1'('#skF_5',B_379,'#skF_2'('#skF_4',B_25)),'#skF_4')
      | ~ r1_tarski('#skF_2'('#skF_4',B_25),B_379)
      | ~ v2_tex_2(B_379,'#skF_5')
      | ~ m1_subset_1(B_379,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_tex_2(B_25,'#skF_4')
      | ~ m1_subset_1(B_25,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_2782])).

tff(c_1292,plain,(
    ! [B_146,C_147] :
      ( m1_subset_1('#skF_1'('#skF_5',B_146,C_147),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r1_tarski(C_147,B_146)
      | ~ m1_subset_1(C_147,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ v2_tex_2(B_146,'#skF_5')
      | ~ m1_subset_1(B_146,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_165,c_165,c_1225])).

tff(c_1355,plain,(
    ! [A_156,B_157,C_158] :
      ( k9_subset_1(u1_struct_0(A_156),B_157,'#skF_1'(A_156,B_157,C_158)) = C_158
      | ~ r1_tarski(C_158,B_157)
      | ~ m1_subset_1(C_158,k1_zfmisc_1(u1_struct_0(A_156)))
      | ~ v2_tex_2(B_157,A_156)
      | ~ m1_subset_1(B_157,k1_zfmisc_1(u1_struct_0(A_156)))
      | ~ l1_pre_topc(A_156) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_1365,plain,(
    ! [B_157,C_158] :
      ( k9_subset_1(u1_struct_0('#skF_5'),B_157,'#skF_1'('#skF_5',B_157,C_158)) = C_158
      | ~ r1_tarski(C_158,B_157)
      | ~ m1_subset_1(C_158,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ v2_tex_2(B_157,'#skF_5')
      | ~ m1_subset_1(B_157,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_165,c_1355])).

tff(c_1715,plain,(
    ! [B_178,C_179] :
      ( k9_subset_1(u1_struct_0('#skF_4'),B_178,'#skF_1'('#skF_5',B_178,C_179)) = C_179
      | ~ r1_tarski(C_179,B_178)
      | ~ m1_subset_1(C_179,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ v2_tex_2(B_178,'#skF_5')
      | ~ m1_subset_1(B_178,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_165,c_165,c_1365])).

tff(c_1730,plain,(
    ! [B_178,B_25] :
      ( k9_subset_1(u1_struct_0('#skF_4'),B_178,'#skF_1'('#skF_5',B_178,'#skF_2'('#skF_4',B_25))) = '#skF_2'('#skF_4',B_25)
      | ~ r1_tarski('#skF_2'('#skF_4',B_25),B_178)
      | ~ v2_tex_2(B_178,'#skF_5')
      | ~ m1_subset_1(B_178,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_tex_2(B_25,'#skF_4')
      | ~ m1_subset_1(B_25,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_16,c_1715])).

tff(c_2588,plain,(
    ! [B_333,B_334] :
      ( k9_subset_1(u1_struct_0('#skF_4'),B_333,'#skF_1'('#skF_5',B_333,'#skF_2'('#skF_4',B_334))) = '#skF_2'('#skF_4',B_334)
      | ~ r1_tarski('#skF_2'('#skF_4',B_334),B_333)
      | ~ v2_tex_2(B_333,'#skF_5')
      | ~ m1_subset_1(B_333,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_tex_2(B_334,'#skF_4')
      | ~ m1_subset_1(B_334,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_1730])).

tff(c_12,plain,(
    ! [A_11,B_25,D_35] :
      ( k9_subset_1(u1_struct_0(A_11),B_25,D_35) != '#skF_2'(A_11,B_25)
      | ~ v3_pre_topc(D_35,A_11)
      | ~ m1_subset_1(D_35,k1_zfmisc_1(u1_struct_0(A_11)))
      | v2_tex_2(B_25,A_11)
      | ~ m1_subset_1(B_25,k1_zfmisc_1(u1_struct_0(A_11)))
      | ~ l1_pre_topc(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_2595,plain,(
    ! [B_334,B_333] :
      ( '#skF_2'('#skF_4',B_334) != '#skF_2'('#skF_4',B_333)
      | ~ v3_pre_topc('#skF_1'('#skF_5',B_333,'#skF_2'('#skF_4',B_334)),'#skF_4')
      | ~ m1_subset_1('#skF_1'('#skF_5',B_333,'#skF_2'('#skF_4',B_334)),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_tex_2(B_333,'#skF_4')
      | ~ m1_subset_1(B_333,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4')
      | ~ r1_tarski('#skF_2'('#skF_4',B_334),B_333)
      | ~ v2_tex_2(B_333,'#skF_5')
      | ~ m1_subset_1(B_333,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_tex_2(B_334,'#skF_4')
      | ~ m1_subset_1(B_334,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2588,c_12])).

tff(c_3758,plain,(
    ! [B_628,B_627] :
      ( '#skF_2'('#skF_4',B_628) != '#skF_2'('#skF_4',B_627)
      | ~ v3_pre_topc('#skF_1'('#skF_5',B_628,'#skF_2'('#skF_4',B_627)),'#skF_4')
      | ~ m1_subset_1('#skF_1'('#skF_5',B_628,'#skF_2'('#skF_4',B_627)),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_tex_2(B_628,'#skF_4')
      | ~ r1_tarski('#skF_2'('#skF_4',B_627),B_628)
      | ~ v2_tex_2(B_628,'#skF_5')
      | ~ m1_subset_1(B_628,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_tex_2(B_627,'#skF_4')
      | ~ m1_subset_1(B_627,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_2595])).

tff(c_3764,plain,(
    ! [B_630,B_629] :
      ( '#skF_2'('#skF_4',B_630) != '#skF_2'('#skF_4',B_629)
      | ~ v3_pre_topc('#skF_1'('#skF_5',B_630,'#skF_2'('#skF_4',B_629)),'#skF_4')
      | v2_tex_2(B_630,'#skF_4')
      | v2_tex_2(B_629,'#skF_4')
      | ~ m1_subset_1(B_629,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r1_tarski('#skF_2'('#skF_4',B_629),B_630)
      | ~ m1_subset_1('#skF_2'('#skF_4',B_629),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ v2_tex_2(B_630,'#skF_5')
      | ~ m1_subset_1(B_630,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_1292,c_3758])).

tff(c_3768,plain,(
    ! [B_632,B_631] :
      ( '#skF_2'('#skF_4',B_632) != '#skF_2'('#skF_4',B_631)
      | v2_tex_2(B_631,'#skF_4')
      | ~ m1_subset_1('#skF_2'('#skF_4',B_632),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r1_tarski('#skF_2'('#skF_4',B_632),B_631)
      | ~ v2_tex_2(B_631,'#skF_5')
      | ~ m1_subset_1(B_631,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_tex_2(B_632,'#skF_4')
      | ~ m1_subset_1(B_632,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_2785,c_3764])).

tff(c_3771,plain,(
    ! [B_631,B_25] :
      ( '#skF_2'('#skF_4',B_631) != '#skF_2'('#skF_4',B_25)
      | v2_tex_2(B_631,'#skF_4')
      | ~ r1_tarski('#skF_2'('#skF_4',B_25),B_631)
      | ~ v2_tex_2(B_631,'#skF_5')
      | ~ m1_subset_1(B_631,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_tex_2(B_25,'#skF_4')
      | ~ m1_subset_1(B_25,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_16,c_3768])).

tff(c_3775,plain,(
    ! [B_634,B_633] :
      ( '#skF_2'('#skF_4',B_634) != '#skF_2'('#skF_4',B_633)
      | v2_tex_2(B_633,'#skF_4')
      | ~ r1_tarski('#skF_2'('#skF_4',B_634),B_633)
      | ~ v2_tex_2(B_633,'#skF_5')
      | ~ m1_subset_1(B_633,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_tex_2(B_634,'#skF_4')
      | ~ m1_subset_1(B_634,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_3771])).

tff(c_3925,plain,(
    ! [B_648] :
      ( ~ v2_tex_2('#skF_3'('#skF_5',B_648),'#skF_5')
      | ~ m1_subset_1('#skF_3'('#skF_5',B_648),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_tex_2('#skF_3'('#skF_5',B_648),'#skF_4')
      | v3_tex_2(B_648,'#skF_5')
      | ~ v2_tex_2(B_648,'#skF_5')
      | ~ m1_subset_1(B_648,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_661,c_3775])).

tff(c_3948,plain,(
    ! [B_653] :
      ( ~ v2_tex_2('#skF_3'('#skF_5',B_653),'#skF_5')
      | v2_tex_2('#skF_3'('#skF_5',B_653),'#skF_4')
      | v3_tex_2(B_653,'#skF_5')
      | ~ v2_tex_2(B_653,'#skF_5')
      | ~ m1_subset_1(B_653,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_600,c_3925])).

tff(c_3972,plain,
    ( ~ v2_tex_2('#skF_3'('#skF_5','#skF_6'),'#skF_5')
    | v2_tex_2('#skF_3'('#skF_5','#skF_6'),'#skF_4')
    | v3_tex_2('#skF_6','#skF_5')
    | ~ v2_tex_2('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_46,c_3948])).

tff(c_3987,plain,
    ( v2_tex_2('#skF_3'('#skF_5','#skF_6'),'#skF_4')
    | v3_tex_2('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_522,c_3972])).

tff(c_3989,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_825,c_3987])).

tff(c_3991,plain,(
    ~ v2_tex_2('#skF_6','#skF_5') ),
    inference(splitRight,[status(thm)],[c_138])).

tff(c_62,plain,(
    ! [B_58,A_59] :
      ( v2_tex_2(B_58,A_59)
      | ~ v3_tex_2(B_58,A_59)
      | ~ m1_subset_1(B_58,k1_zfmisc_1(u1_struct_0(A_59)))
      | ~ l1_pre_topc(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_65,plain,
    ( v2_tex_2('#skF_6','#skF_4')
    | ~ v3_tex_2('#skF_6','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_62])).

tff(c_71,plain,(
    v2_tex_2('#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_38,c_65])).

tff(c_3990,plain,(
    r1_tarski('#skF_2'('#skF_5','#skF_6'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_138])).

tff(c_3999,plain,
    ( u1_struct_0('#skF_5') = u1_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_125])).

tff(c_4001,plain,(
    u1_struct_0('#skF_5') = u1_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_3999])).

tff(c_4070,plain,(
    ! [A_658,B_659] :
      ( m1_subset_1('#skF_2'(A_658,B_659),k1_zfmisc_1(u1_struct_0(A_658)))
      | v2_tex_2(B_659,A_658)
      | ~ m1_subset_1(B_659,k1_zfmisc_1(u1_struct_0(A_658)))
      | ~ l1_pre_topc(A_658) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_4088,plain,(
    ! [B_659] :
      ( m1_subset_1('#skF_2'('#skF_5',B_659),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_tex_2(B_659,'#skF_5')
      | ~ m1_subset_1(B_659,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4001,c_4070])).

tff(c_4097,plain,(
    ! [B_659] :
      ( m1_subset_1('#skF_2'('#skF_5',B_659),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_tex_2(B_659,'#skF_5')
      | ~ m1_subset_1(B_659,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_4001,c_4088])).

tff(c_4605,plain,(
    ! [A_694,B_695,C_696] :
      ( v3_pre_topc('#skF_1'(A_694,B_695,C_696),A_694)
      | ~ r1_tarski(C_696,B_695)
      | ~ m1_subset_1(C_696,k1_zfmisc_1(u1_struct_0(A_694)))
      | ~ v2_tex_2(B_695,A_694)
      | ~ m1_subset_1(B_695,k1_zfmisc_1(u1_struct_0(A_694)))
      | ~ l1_pre_topc(A_694) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_4611,plain,(
    ! [B_695,B_659] :
      ( v3_pre_topc('#skF_1'('#skF_4',B_695,'#skF_2'('#skF_5',B_659)),'#skF_4')
      | ~ r1_tarski('#skF_2'('#skF_5',B_659),B_695)
      | ~ v2_tex_2(B_695,'#skF_4')
      | ~ m1_subset_1(B_695,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4')
      | v2_tex_2(B_659,'#skF_5')
      | ~ m1_subset_1(B_659,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_4097,c_4605])).

tff(c_4624,plain,(
    ! [B_695,B_659] :
      ( v3_pre_topc('#skF_1'('#skF_4',B_695,'#skF_2'('#skF_5',B_659)),'#skF_4')
      | ~ r1_tarski('#skF_2'('#skF_5',B_659),B_695)
      | ~ v2_tex_2(B_695,'#skF_4')
      | ~ m1_subset_1(B_695,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_tex_2(B_659,'#skF_5')
      | ~ m1_subset_1(B_659,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_4611])).

tff(c_4714,plain,(
    ! [A_705,B_706,C_707] :
      ( m1_subset_1('#skF_1'(A_705,B_706,C_707),k1_zfmisc_1(u1_struct_0(A_705)))
      | ~ r1_tarski(C_707,B_706)
      | ~ m1_subset_1(C_707,k1_zfmisc_1(u1_struct_0(A_705)))
      | ~ v2_tex_2(B_706,A_705)
      | ~ m1_subset_1(B_706,k1_zfmisc_1(u1_struct_0(A_705)))
      | ~ l1_pre_topc(A_705) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_4832,plain,(
    ! [A_705,B_706,C_707] :
      ( r2_hidden('#skF_1'(A_705,B_706,C_707),u1_pre_topc(A_705))
      | ~ v3_pre_topc('#skF_1'(A_705,B_706,C_707),A_705)
      | ~ r1_tarski(C_707,B_706)
      | ~ m1_subset_1(C_707,k1_zfmisc_1(u1_struct_0(A_705)))
      | ~ v2_tex_2(B_706,A_705)
      | ~ m1_subset_1(B_706,k1_zfmisc_1(u1_struct_0(A_705)))
      | ~ l1_pre_topc(A_705) ) ),
    inference(resolution,[status(thm)],[c_4714,c_4])).

tff(c_4029,plain,
    ( m1_subset_1(u1_pre_topc('#skF_5'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))
    | ~ l1_pre_topc('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_4001,c_6])).

tff(c_4041,plain,(
    m1_subset_1(u1_pre_topc('#skF_5'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_4029])).

tff(c_4012,plain,(
    g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_5')) = g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4001,c_42])).

tff(c_8,plain,(
    ! [D_10,B_6,C_9,A_5] :
      ( D_10 = B_6
      | g1_pre_topc(C_9,D_10) != g1_pre_topc(A_5,B_6)
      | ~ m1_subset_1(B_6,k1_zfmisc_1(k1_zfmisc_1(A_5))) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_4052,plain,(
    ! [D_10,C_9] :
      ( u1_pre_topc('#skF_5') = D_10
      | g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')) != g1_pre_topc(C_9,D_10)
      | ~ m1_subset_1(u1_pre_topc('#skF_5'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4012,c_8])).

tff(c_4060,plain,(
    ! [D_10,C_9] :
      ( u1_pre_topc('#skF_5') = D_10
      | g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')) != g1_pre_topc(C_9,D_10) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4041,c_4052])).

tff(c_4100,plain,(
    u1_pre_topc('#skF_5') = u1_pre_topc('#skF_4') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_4060])).

tff(c_4023,plain,(
    ! [B_3] :
      ( v3_pre_topc(B_3,'#skF_5')
      | ~ r2_hidden(B_3,u1_pre_topc('#skF_5'))
      | ~ m1_subset_1(B_3,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4001,c_2])).

tff(c_4037,plain,(
    ! [B_3] :
      ( v3_pre_topc(B_3,'#skF_5')
      | ~ r2_hidden(B_3,u1_pre_topc('#skF_5'))
      | ~ m1_subset_1(B_3,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_4023])).

tff(c_4147,plain,(
    ! [B_3] :
      ( v3_pre_topc(B_3,'#skF_5')
      | ~ r2_hidden(B_3,u1_pre_topc('#skF_4'))
      | ~ m1_subset_1(B_3,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4100,c_4037])).

tff(c_4765,plain,(
    ! [B_706,C_707] :
      ( v3_pre_topc('#skF_1'('#skF_4',B_706,C_707),'#skF_5')
      | ~ r2_hidden('#skF_1'('#skF_4',B_706,C_707),u1_pre_topc('#skF_4'))
      | ~ r1_tarski(C_707,B_706)
      | ~ m1_subset_1(C_707,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ v2_tex_2(B_706,'#skF_4')
      | ~ m1_subset_1(B_706,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_4714,c_4147])).

tff(c_5967,plain,(
    ! [B_825,C_826] :
      ( v3_pre_topc('#skF_1'('#skF_4',B_825,C_826),'#skF_5')
      | ~ r2_hidden('#skF_1'('#skF_4',B_825,C_826),u1_pre_topc('#skF_4'))
      | ~ r1_tarski(C_826,B_825)
      | ~ m1_subset_1(C_826,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ v2_tex_2(B_825,'#skF_4')
      | ~ m1_subset_1(B_825,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_4765])).

tff(c_5971,plain,(
    ! [B_706,C_707] :
      ( v3_pre_topc('#skF_1'('#skF_4',B_706,C_707),'#skF_5')
      | ~ v3_pre_topc('#skF_1'('#skF_4',B_706,C_707),'#skF_4')
      | ~ r1_tarski(C_707,B_706)
      | ~ m1_subset_1(C_707,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ v2_tex_2(B_706,'#skF_4')
      | ~ m1_subset_1(B_706,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_4832,c_5967])).

tff(c_5975,plain,(
    ! [B_827,C_828] :
      ( v3_pre_topc('#skF_1'('#skF_4',B_827,C_828),'#skF_5')
      | ~ v3_pre_topc('#skF_1'('#skF_4',B_827,C_828),'#skF_4')
      | ~ r1_tarski(C_828,B_827)
      | ~ m1_subset_1(C_828,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ v2_tex_2(B_827,'#skF_4')
      | ~ m1_subset_1(B_827,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_5971])).

tff(c_6001,plain,(
    ! [B_827,B_659] :
      ( v3_pre_topc('#skF_1'('#skF_4',B_827,'#skF_2'('#skF_5',B_659)),'#skF_5')
      | ~ v3_pre_topc('#skF_1'('#skF_4',B_827,'#skF_2'('#skF_5',B_659)),'#skF_4')
      | ~ r1_tarski('#skF_2'('#skF_5',B_659),B_827)
      | ~ v2_tex_2(B_827,'#skF_4')
      | ~ m1_subset_1(B_827,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_tex_2(B_659,'#skF_5')
      | ~ m1_subset_1(B_659,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_4097,c_5975])).

tff(c_22,plain,(
    ! [A_11,B_25,C_32] :
      ( m1_subset_1('#skF_1'(A_11,B_25,C_32),k1_zfmisc_1(u1_struct_0(A_11)))
      | ~ r1_tarski(C_32,B_25)
      | ~ m1_subset_1(C_32,k1_zfmisc_1(u1_struct_0(A_11)))
      | ~ v2_tex_2(B_25,A_11)
      | ~ m1_subset_1(B_25,k1_zfmisc_1(u1_struct_0(A_11)))
      | ~ l1_pre_topc(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_5152,plain,(
    ! [A_731,B_732,C_733] :
      ( k9_subset_1(u1_struct_0(A_731),B_732,'#skF_1'(A_731,B_732,C_733)) = C_733
      | ~ r1_tarski(C_733,B_732)
      | ~ m1_subset_1(C_733,k1_zfmisc_1(u1_struct_0(A_731)))
      | ~ v2_tex_2(B_732,A_731)
      | ~ m1_subset_1(B_732,k1_zfmisc_1(u1_struct_0(A_731)))
      | ~ l1_pre_topc(A_731) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_5160,plain,(
    ! [B_732,B_659] :
      ( k9_subset_1(u1_struct_0('#skF_4'),B_732,'#skF_1'('#skF_4',B_732,'#skF_2'('#skF_5',B_659))) = '#skF_2'('#skF_5',B_659)
      | ~ r1_tarski('#skF_2'('#skF_5',B_659),B_732)
      | ~ v2_tex_2(B_732,'#skF_4')
      | ~ m1_subset_1(B_732,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4')
      | v2_tex_2(B_659,'#skF_5')
      | ~ m1_subset_1(B_659,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_4097,c_5152])).

tff(c_6372,plain,(
    ! [B_908,B_909] :
      ( k9_subset_1(u1_struct_0('#skF_4'),B_908,'#skF_1'('#skF_4',B_908,'#skF_2'('#skF_5',B_909))) = '#skF_2'('#skF_5',B_909)
      | ~ r1_tarski('#skF_2'('#skF_5',B_909),B_908)
      | ~ v2_tex_2(B_908,'#skF_4')
      | ~ m1_subset_1(B_908,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_tex_2(B_909,'#skF_5')
      | ~ m1_subset_1(B_909,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_5160])).

tff(c_5079,plain,(
    ! [A_719,B_720,D_721] :
      ( k9_subset_1(u1_struct_0(A_719),B_720,D_721) != '#skF_2'(A_719,B_720)
      | ~ v3_pre_topc(D_721,A_719)
      | ~ m1_subset_1(D_721,k1_zfmisc_1(u1_struct_0(A_719)))
      | v2_tex_2(B_720,A_719)
      | ~ m1_subset_1(B_720,k1_zfmisc_1(u1_struct_0(A_719)))
      | ~ l1_pre_topc(A_719) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_5081,plain,(
    ! [B_720,D_721] :
      ( k9_subset_1(u1_struct_0('#skF_4'),B_720,D_721) != '#skF_2'('#skF_5',B_720)
      | ~ v3_pre_topc(D_721,'#skF_5')
      | ~ m1_subset_1(D_721,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | v2_tex_2(B_720,'#skF_5')
      | ~ m1_subset_1(B_720,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4001,c_5079])).

tff(c_5083,plain,(
    ! [B_720,D_721] :
      ( k9_subset_1(u1_struct_0('#skF_4'),B_720,D_721) != '#skF_2'('#skF_5',B_720)
      | ~ v3_pre_topc(D_721,'#skF_5')
      | ~ m1_subset_1(D_721,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_tex_2(B_720,'#skF_5')
      | ~ m1_subset_1(B_720,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_4001,c_4001,c_5081])).

tff(c_8655,plain,(
    ! [B_1406,B_1405] :
      ( '#skF_2'('#skF_5',B_1406) != '#skF_2'('#skF_5',B_1405)
      | ~ v3_pre_topc('#skF_1'('#skF_4',B_1406,'#skF_2'('#skF_5',B_1405)),'#skF_5')
      | ~ m1_subset_1('#skF_1'('#skF_4',B_1406,'#skF_2'('#skF_5',B_1405)),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_tex_2(B_1406,'#skF_5')
      | ~ m1_subset_1(B_1406,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r1_tarski('#skF_2'('#skF_5',B_1405),B_1406)
      | ~ v2_tex_2(B_1406,'#skF_4')
      | ~ m1_subset_1(B_1406,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_tex_2(B_1405,'#skF_5')
      | ~ m1_subset_1(B_1405,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6372,c_5083])).

tff(c_8659,plain,(
    ! [B_25,B_1405] :
      ( '#skF_2'('#skF_5',B_25) != '#skF_2'('#skF_5',B_1405)
      | ~ v3_pre_topc('#skF_1'('#skF_4',B_25,'#skF_2'('#skF_5',B_1405)),'#skF_5')
      | v2_tex_2(B_25,'#skF_5')
      | v2_tex_2(B_1405,'#skF_5')
      | ~ m1_subset_1(B_1405,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r1_tarski('#skF_2'('#skF_5',B_1405),B_25)
      | ~ m1_subset_1('#skF_2'('#skF_5',B_1405),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ v2_tex_2(B_25,'#skF_4')
      | ~ m1_subset_1(B_25,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_22,c_8655])).

tff(c_8663,plain,(
    ! [B_1408,B_1407] :
      ( '#skF_2'('#skF_5',B_1408) != '#skF_2'('#skF_5',B_1407)
      | ~ v3_pre_topc('#skF_1'('#skF_4',B_1407,'#skF_2'('#skF_5',B_1408)),'#skF_5')
      | v2_tex_2(B_1407,'#skF_5')
      | v2_tex_2(B_1408,'#skF_5')
      | ~ m1_subset_1(B_1408,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r1_tarski('#skF_2'('#skF_5',B_1408),B_1407)
      | ~ m1_subset_1('#skF_2'('#skF_5',B_1408),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ v2_tex_2(B_1407,'#skF_4')
      | ~ m1_subset_1(B_1407,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_8659])).

tff(c_8667,plain,(
    ! [B_1410,B_1409] :
      ( '#skF_2'('#skF_5',B_1410) != '#skF_2'('#skF_5',B_1409)
      | v2_tex_2(B_1409,'#skF_5')
      | ~ m1_subset_1('#skF_2'('#skF_5',B_1410),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ v3_pre_topc('#skF_1'('#skF_4',B_1409,'#skF_2'('#skF_5',B_1410)),'#skF_4')
      | ~ r1_tarski('#skF_2'('#skF_5',B_1410),B_1409)
      | ~ v2_tex_2(B_1409,'#skF_4')
      | ~ m1_subset_1(B_1409,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_tex_2(B_1410,'#skF_5')
      | ~ m1_subset_1(B_1410,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_6001,c_8663])).

tff(c_8671,plain,(
    ! [B_1412,B_1411] :
      ( '#skF_2'('#skF_5',B_1412) != '#skF_2'('#skF_5',B_1411)
      | v2_tex_2(B_1412,'#skF_5')
      | ~ v3_pre_topc('#skF_1'('#skF_4',B_1412,'#skF_2'('#skF_5',B_1411)),'#skF_4')
      | ~ r1_tarski('#skF_2'('#skF_5',B_1411),B_1412)
      | ~ v2_tex_2(B_1412,'#skF_4')
      | ~ m1_subset_1(B_1412,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_tex_2(B_1411,'#skF_5')
      | ~ m1_subset_1(B_1411,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_4097,c_8667])).

tff(c_8676,plain,(
    ! [B_1414,B_1413] :
      ( '#skF_2'('#skF_5',B_1414) != '#skF_2'('#skF_5',B_1413)
      | v2_tex_2(B_1413,'#skF_5')
      | ~ r1_tarski('#skF_2'('#skF_5',B_1414),B_1413)
      | ~ v2_tex_2(B_1413,'#skF_4')
      | ~ m1_subset_1(B_1413,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_tex_2(B_1414,'#skF_5')
      | ~ m1_subset_1(B_1414,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_4624,c_8671])).

tff(c_8701,plain,
    ( ~ v2_tex_2('#skF_6','#skF_4')
    | v2_tex_2('#skF_6','#skF_5')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(resolution,[status(thm)],[c_3990,c_8676])).

tff(c_8720,plain,(
    v2_tex_2('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_71,c_8701])).

tff(c_8722,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3991,c_8720])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:17:34 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 16.84/8.67  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 16.84/8.69  
% 16.84/8.69  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 16.84/8.69  %$ v3_tex_2 > v3_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > l1_pre_topc > k9_subset_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2
% 16.84/8.69  
% 16.84/8.69  %Foreground sorts:
% 16.84/8.69  
% 16.84/8.69  
% 16.84/8.69  %Background operators:
% 16.84/8.69  
% 16.84/8.69  
% 16.84/8.69  %Foreground operators:
% 16.84/8.69  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 16.84/8.69  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 16.84/8.69  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 16.84/8.69  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 16.84/8.69  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 16.84/8.69  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 16.84/8.69  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 16.84/8.69  tff('#skF_7', type, '#skF_7': $i).
% 16.84/8.69  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 16.84/8.69  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 16.84/8.69  tff('#skF_5', type, '#skF_5': $i).
% 16.84/8.69  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 16.84/8.69  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 16.84/8.69  tff('#skF_6', type, '#skF_6': $i).
% 16.84/8.69  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 16.84/8.69  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 16.84/8.69  tff('#skF_4', type, '#skF_4': $i).
% 16.84/8.69  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 16.84/8.69  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 16.84/8.69  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 16.84/8.69  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 16.84/8.69  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 16.84/8.69  
% 16.84/8.72  tff(f_106, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => ((((g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)) = g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))) & (C = D)) & v3_tex_2(C, A)) => v3_tex_2(D, B)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_tex_2)).
% 16.84/8.72  tff(f_68, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r1_tarski(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(v3_pre_topc(D, A) & (k9_subset_1(u1_struct_0(A), B, D) = C)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_tex_2)).
% 16.84/8.72  tff(f_38, axiom, (![A]: (l1_pre_topc(A) => m1_subset_1(u1_pre_topc(A), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 16.84/8.72  tff(f_47, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C, D]: ((g1_pre_topc(A, B) = g1_pre_topc(C, D)) => ((A = C) & (B = D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', free_g1_pre_topc)).
% 16.84/8.72  tff(f_86, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tex_2(B, A) <=> (v2_tex_2(B, A) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v2_tex_2(C, A) & r1_tarski(B, C)) => (B = C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_tex_2)).
% 16.84/8.72  tff(f_34, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> r2_hidden(B, u1_pre_topc(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_pre_topc)).
% 16.84/8.72  tff(c_40, plain, ('#skF_7'='#skF_6'), inference(cnfTransformation, [status(thm)], [f_106])).
% 16.84/8.72  tff(c_36, plain, (~v3_tex_2('#skF_7', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_106])).
% 16.84/8.72  tff(c_52, plain, (~v3_tex_2('#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_36])).
% 16.84/8.72  tff(c_46, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_106])).
% 16.84/8.72  tff(c_48, plain, (l1_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_106])).
% 16.84/8.72  tff(c_44, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(cnfTransformation, [status(thm)], [f_106])).
% 16.84/8.72  tff(c_51, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_44])).
% 16.84/8.72  tff(c_128, plain, (![A_74, B_75]: (r1_tarski('#skF_2'(A_74, B_75), B_75) | v2_tex_2(B_75, A_74) | ~m1_subset_1(B_75, k1_zfmisc_1(u1_struct_0(A_74))) | ~l1_pre_topc(A_74))), inference(cnfTransformation, [status(thm)], [f_68])).
% 16.84/8.72  tff(c_132, plain, (r1_tarski('#skF_2'('#skF_5', '#skF_6'), '#skF_6') | v2_tex_2('#skF_6', '#skF_5') | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_51, c_128])).
% 16.84/8.72  tff(c_138, plain, (r1_tarski('#skF_2'('#skF_5', '#skF_6'), '#skF_6') | v2_tex_2('#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_132])).
% 16.84/8.72  tff(c_139, plain, (v2_tex_2('#skF_6', '#skF_5')), inference(splitLeft, [status(thm)], [c_138])).
% 16.84/8.72  tff(c_50, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_106])).
% 16.84/8.72  tff(c_38, plain, (v3_tex_2('#skF_6', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_106])).
% 16.84/8.72  tff(c_6, plain, (![A_4]: (m1_subset_1(u1_pre_topc(A_4), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_4)))) | ~l1_pre_topc(A_4))), inference(cnfTransformation, [status(thm)], [f_38])).
% 16.84/8.72  tff(c_42, plain, (g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5'))=g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_106])).
% 16.84/8.72  tff(c_79, plain, (![C_60, A_61, D_62, B_63]: (C_60=A_61 | g1_pre_topc(C_60, D_62)!=g1_pre_topc(A_61, B_63) | ~m1_subset_1(B_63, k1_zfmisc_1(k1_zfmisc_1(A_61))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 16.84/8.72  tff(c_121, plain, (![A_72, B_73]: (u1_struct_0('#skF_5')=A_72 | g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))!=g1_pre_topc(A_72, B_73) | ~m1_subset_1(B_73, k1_zfmisc_1(k1_zfmisc_1(A_72))))), inference(superposition, [status(thm), theory('equality')], [c_42, c_79])).
% 16.84/8.72  tff(c_125, plain, (![A_4]: (u1_struct_0(A_4)=u1_struct_0('#skF_5') | g1_pre_topc(u1_struct_0(A_4), u1_pre_topc(A_4))!=g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')) | ~l1_pre_topc(A_4))), inference(resolution, [status(thm)], [c_6, c_121])).
% 16.84/8.72  tff(c_163, plain, (u1_struct_0('#skF_5')=u1_struct_0('#skF_4') | ~l1_pre_topc('#skF_4')), inference(reflexivity, [status(thm), theory('equality')], [c_125])).
% 16.84/8.72  tff(c_165, plain, (u1_struct_0('#skF_5')=u1_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_163])).
% 16.84/8.72  tff(c_523, plain, (![A_104, B_105]: (m1_subset_1('#skF_3'(A_104, B_105), k1_zfmisc_1(u1_struct_0(A_104))) | v3_tex_2(B_105, A_104) | ~v2_tex_2(B_105, A_104) | ~m1_subset_1(B_105, k1_zfmisc_1(u1_struct_0(A_104))) | ~l1_pre_topc(A_104))), inference(cnfTransformation, [status(thm)], [f_86])).
% 16.84/8.72  tff(c_570, plain, (![B_105]: (m1_subset_1('#skF_3'('#skF_5', B_105), k1_zfmisc_1(u1_struct_0('#skF_4'))) | v3_tex_2(B_105, '#skF_5') | ~v2_tex_2(B_105, '#skF_5') | ~m1_subset_1(B_105, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_165, c_523])).
% 16.84/8.72  tff(c_600, plain, (![B_105]: (m1_subset_1('#skF_3'('#skF_5', B_105), k1_zfmisc_1(u1_struct_0('#skF_4'))) | v3_tex_2(B_105, '#skF_5') | ~v2_tex_2(B_105, '#skF_5') | ~m1_subset_1(B_105, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_165, c_570])).
% 16.84/8.72  tff(c_281, plain, (![A_85, B_86]: ('#skF_3'(A_85, B_86)!=B_86 | v3_tex_2(B_86, A_85) | ~v2_tex_2(B_86, A_85) | ~m1_subset_1(B_86, k1_zfmisc_1(u1_struct_0(A_85))) | ~l1_pre_topc(A_85))), inference(cnfTransformation, [status(thm)], [f_86])).
% 16.84/8.72  tff(c_284, plain, (![B_86]: ('#skF_3'('#skF_5', B_86)!=B_86 | v3_tex_2(B_86, '#skF_5') | ~v2_tex_2(B_86, '#skF_5') | ~m1_subset_1(B_86, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_165, c_281])).
% 16.84/8.72  tff(c_342, plain, (![B_88]: ('#skF_3'('#skF_5', B_88)!=B_88 | v3_tex_2(B_88, '#skF_5') | ~v2_tex_2(B_88, '#skF_5') | ~m1_subset_1(B_88, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_284])).
% 16.84/8.72  tff(c_352, plain, ('#skF_3'('#skF_5', '#skF_6')!='#skF_6' | v3_tex_2('#skF_6', '#skF_5') | ~v2_tex_2('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_46, c_342])).
% 16.84/8.72  tff(c_359, plain, ('#skF_3'('#skF_5', '#skF_6')!='#skF_6' | v3_tex_2('#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_139, c_352])).
% 16.84/8.72  tff(c_360, plain, ('#skF_3'('#skF_5', '#skF_6')!='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_52, c_359])).
% 16.84/8.72  tff(c_410, plain, (![B_94, A_95]: (r1_tarski(B_94, '#skF_3'(A_95, B_94)) | v3_tex_2(B_94, A_95) | ~v2_tex_2(B_94, A_95) | ~m1_subset_1(B_94, k1_zfmisc_1(u1_struct_0(A_95))) | ~l1_pre_topc(A_95))), inference(cnfTransformation, [status(thm)], [f_86])).
% 16.84/8.72  tff(c_414, plain, (![B_94]: (r1_tarski(B_94, '#skF_3'('#skF_5', B_94)) | v3_tex_2(B_94, '#skF_5') | ~v2_tex_2(B_94, '#skF_5') | ~m1_subset_1(B_94, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_165, c_410])).
% 16.84/8.72  tff(c_470, plain, (![B_100]: (r1_tarski(B_100, '#skF_3'('#skF_5', B_100)) | v3_tex_2(B_100, '#skF_5') | ~v2_tex_2(B_100, '#skF_5') | ~m1_subset_1(B_100, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_414])).
% 16.84/8.72  tff(c_477, plain, (r1_tarski('#skF_6', '#skF_3'('#skF_5', '#skF_6')) | v3_tex_2('#skF_6', '#skF_5') | ~v2_tex_2('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_46, c_470])).
% 16.84/8.72  tff(c_484, plain, (r1_tarski('#skF_6', '#skF_3'('#skF_5', '#skF_6')) | v3_tex_2('#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_139, c_477])).
% 16.84/8.72  tff(c_485, plain, (r1_tarski('#skF_6', '#skF_3'('#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_52, c_484])).
% 16.84/8.72  tff(c_765, plain, (![C_113, B_114, A_115]: (C_113=B_114 | ~r1_tarski(B_114, C_113) | ~v2_tex_2(C_113, A_115) | ~m1_subset_1(C_113, k1_zfmisc_1(u1_struct_0(A_115))) | ~v3_tex_2(B_114, A_115) | ~m1_subset_1(B_114, k1_zfmisc_1(u1_struct_0(A_115))) | ~l1_pre_topc(A_115))), inference(cnfTransformation, [status(thm)], [f_86])).
% 16.84/8.72  tff(c_767, plain, (![A_115]: ('#skF_3'('#skF_5', '#skF_6')='#skF_6' | ~v2_tex_2('#skF_3'('#skF_5', '#skF_6'), A_115) | ~m1_subset_1('#skF_3'('#skF_5', '#skF_6'), k1_zfmisc_1(u1_struct_0(A_115))) | ~v3_tex_2('#skF_6', A_115) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0(A_115))) | ~l1_pre_topc(A_115))), inference(resolution, [status(thm)], [c_485, c_765])).
% 16.84/8.72  tff(c_810, plain, (![A_119]: (~v2_tex_2('#skF_3'('#skF_5', '#skF_6'), A_119) | ~m1_subset_1('#skF_3'('#skF_5', '#skF_6'), k1_zfmisc_1(u1_struct_0(A_119))) | ~v3_tex_2('#skF_6', A_119) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0(A_119))) | ~l1_pre_topc(A_119))), inference(negUnitSimplification, [status(thm)], [c_360, c_767])).
% 16.84/8.72  tff(c_814, plain, (~v2_tex_2('#skF_3'('#skF_5', '#skF_6'), '#skF_4') | ~v3_tex_2('#skF_6', '#skF_4') | ~l1_pre_topc('#skF_4') | v3_tex_2('#skF_6', '#skF_5') | ~v2_tex_2('#skF_6', '#skF_5') | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_600, c_810])).
% 16.84/8.72  tff(c_824, plain, (~v2_tex_2('#skF_3'('#skF_5', '#skF_6'), '#skF_4') | v3_tex_2('#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_139, c_50, c_38, c_814])).
% 16.84/8.72  tff(c_825, plain, (~v2_tex_2('#skF_3'('#skF_5', '#skF_6'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_52, c_824])).
% 16.84/8.72  tff(c_486, plain, (![A_101, B_102]: (v2_tex_2('#skF_3'(A_101, B_102), A_101) | v3_tex_2(B_102, A_101) | ~v2_tex_2(B_102, A_101) | ~m1_subset_1(B_102, k1_zfmisc_1(u1_struct_0(A_101))) | ~l1_pre_topc(A_101))), inference(cnfTransformation, [status(thm)], [f_86])).
% 16.84/8.72  tff(c_490, plain, (![B_102]: (v2_tex_2('#skF_3'('#skF_5', B_102), '#skF_5') | v3_tex_2(B_102, '#skF_5') | ~v2_tex_2(B_102, '#skF_5') | ~m1_subset_1(B_102, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_165, c_486])).
% 16.84/8.72  tff(c_504, plain, (![B_103]: (v2_tex_2('#skF_3'('#skF_5', B_103), '#skF_5') | v3_tex_2(B_103, '#skF_5') | ~v2_tex_2(B_103, '#skF_5') | ~m1_subset_1(B_103, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_490])).
% 16.84/8.72  tff(c_514, plain, (v2_tex_2('#skF_3'('#skF_5', '#skF_6'), '#skF_5') | v3_tex_2('#skF_6', '#skF_5') | ~v2_tex_2('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_46, c_504])).
% 16.84/8.72  tff(c_521, plain, (v2_tex_2('#skF_3'('#skF_5', '#skF_6'), '#skF_5') | v3_tex_2('#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_139, c_514])).
% 16.84/8.72  tff(c_522, plain, (v2_tex_2('#skF_3'('#skF_5', '#skF_6'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_52, c_521])).
% 16.84/8.72  tff(c_605, plain, (![B_106]: (m1_subset_1('#skF_3'('#skF_5', B_106), k1_zfmisc_1(u1_struct_0('#skF_4'))) | v3_tex_2(B_106, '#skF_5') | ~v2_tex_2(B_106, '#skF_5') | ~m1_subset_1(B_106, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_165, c_570])).
% 16.84/8.72  tff(c_14, plain, (![A_11, B_25]: (r1_tarski('#skF_2'(A_11, B_25), B_25) | v2_tex_2(B_25, A_11) | ~m1_subset_1(B_25, k1_zfmisc_1(u1_struct_0(A_11))) | ~l1_pre_topc(A_11))), inference(cnfTransformation, [status(thm)], [f_68])).
% 16.84/8.72  tff(c_633, plain, (![B_106]: (r1_tarski('#skF_2'('#skF_4', '#skF_3'('#skF_5', B_106)), '#skF_3'('#skF_5', B_106)) | v2_tex_2('#skF_3'('#skF_5', B_106), '#skF_4') | ~l1_pre_topc('#skF_4') | v3_tex_2(B_106, '#skF_5') | ~v2_tex_2(B_106, '#skF_5') | ~m1_subset_1(B_106, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_605, c_14])).
% 16.84/8.72  tff(c_661, plain, (![B_106]: (r1_tarski('#skF_2'('#skF_4', '#skF_3'('#skF_5', B_106)), '#skF_3'('#skF_5', B_106)) | v2_tex_2('#skF_3'('#skF_5', B_106), '#skF_4') | v3_tex_2(B_106, '#skF_5') | ~v2_tex_2(B_106, '#skF_5') | ~m1_subset_1(B_106, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_633])).
% 16.84/8.72  tff(c_16, plain, (![A_11, B_25]: (m1_subset_1('#skF_2'(A_11, B_25), k1_zfmisc_1(u1_struct_0(A_11))) | v2_tex_2(B_25, A_11) | ~m1_subset_1(B_25, k1_zfmisc_1(u1_struct_0(A_11))) | ~l1_pre_topc(A_11))), inference(cnfTransformation, [status(thm)], [f_68])).
% 16.84/8.72  tff(c_869, plain, (![A_122, B_123, C_124]: (v3_pre_topc('#skF_1'(A_122, B_123, C_124), A_122) | ~r1_tarski(C_124, B_123) | ~m1_subset_1(C_124, k1_zfmisc_1(u1_struct_0(A_122))) | ~v2_tex_2(B_123, A_122) | ~m1_subset_1(B_123, k1_zfmisc_1(u1_struct_0(A_122))) | ~l1_pre_topc(A_122))), inference(cnfTransformation, [status(thm)], [f_68])).
% 16.84/8.72  tff(c_877, plain, (![B_123, C_124]: (v3_pre_topc('#skF_1'('#skF_5', B_123, C_124), '#skF_5') | ~r1_tarski(C_124, B_123) | ~m1_subset_1(C_124, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~v2_tex_2(B_123, '#skF_5') | ~m1_subset_1(B_123, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_165, c_869])).
% 16.84/8.72  tff(c_1077, plain, (![B_141, C_142]: (v3_pre_topc('#skF_1'('#skF_5', B_141, C_142), '#skF_5') | ~r1_tarski(C_142, B_141) | ~m1_subset_1(C_142, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~v2_tex_2(B_141, '#skF_5') | ~m1_subset_1(B_141, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_165, c_877])).
% 16.84/8.72  tff(c_1087, plain, (![B_141, B_25]: (v3_pre_topc('#skF_1'('#skF_5', B_141, '#skF_2'('#skF_4', B_25)), '#skF_5') | ~r1_tarski('#skF_2'('#skF_4', B_25), B_141) | ~v2_tex_2(B_141, '#skF_5') | ~m1_subset_1(B_141, k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_tex_2(B_25, '#skF_4') | ~m1_subset_1(B_25, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4'))), inference(resolution, [status(thm)], [c_16, c_1077])).
% 16.84/8.72  tff(c_1097, plain, (![B_141, B_25]: (v3_pre_topc('#skF_1'('#skF_5', B_141, '#skF_2'('#skF_4', B_25)), '#skF_5') | ~r1_tarski('#skF_2'('#skF_4', B_25), B_141) | ~v2_tex_2(B_141, '#skF_5') | ~m1_subset_1(B_141, k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_tex_2(B_25, '#skF_4') | ~m1_subset_1(B_25, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_1087])).
% 16.84/8.72  tff(c_1129, plain, (![A_145, B_146, C_147]: (m1_subset_1('#skF_1'(A_145, B_146, C_147), k1_zfmisc_1(u1_struct_0(A_145))) | ~r1_tarski(C_147, B_146) | ~m1_subset_1(C_147, k1_zfmisc_1(u1_struct_0(A_145))) | ~v2_tex_2(B_146, A_145) | ~m1_subset_1(B_146, k1_zfmisc_1(u1_struct_0(A_145))) | ~l1_pre_topc(A_145))), inference(cnfTransformation, [status(thm)], [f_68])).
% 16.84/8.72  tff(c_1225, plain, (![B_146, C_147]: (m1_subset_1('#skF_1'('#skF_5', B_146, C_147), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r1_tarski(C_147, B_146) | ~m1_subset_1(C_147, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~v2_tex_2(B_146, '#skF_5') | ~m1_subset_1(B_146, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_165, c_1129])).
% 16.84/8.72  tff(c_1571, plain, (![B_172, C_173]: (m1_subset_1('#skF_1'('#skF_5', B_172, C_173), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r1_tarski(C_173, B_172) | ~m1_subset_1(C_173, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~v2_tex_2(B_172, '#skF_5') | ~m1_subset_1(B_172, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_165, c_165, c_1225])).
% 16.84/8.72  tff(c_196, plain, (m1_subset_1(u1_pre_topc('#skF_5'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) | ~l1_pre_topc('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_165, c_6])).
% 16.84/8.72  tff(c_210, plain, (m1_subset_1(u1_pre_topc('#skF_5'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_196])).
% 16.84/8.72  tff(c_88, plain, (![D_64, B_65, C_66, A_67]: (D_64=B_65 | g1_pre_topc(C_66, D_64)!=g1_pre_topc(A_67, B_65) | ~m1_subset_1(B_65, k1_zfmisc_1(k1_zfmisc_1(A_67))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 16.84/8.72  tff(c_92, plain, (![D_64, C_66]: (u1_pre_topc('#skF_5')=D_64 | g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))!=g1_pre_topc(C_66, D_64) | ~m1_subset_1(u1_pre_topc('#skF_5'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_5')))))), inference(superposition, [status(thm), theory('equality')], [c_42, c_88])).
% 16.84/8.72  tff(c_362, plain, (![D_64, C_66]: (u1_pre_topc('#skF_5')=D_64 | g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))!=g1_pre_topc(C_66, D_64))), inference(demodulation, [status(thm), theory('equality')], [c_210, c_165, c_92])).
% 16.84/8.72  tff(c_365, plain, (u1_pre_topc('#skF_5')=u1_pre_topc('#skF_4')), inference(reflexivity, [status(thm), theory('equality')], [c_362])).
% 16.84/8.72  tff(c_4, plain, (![B_3, A_1]: (r2_hidden(B_3, u1_pre_topc(A_1)) | ~v3_pre_topc(B_3, A_1) | ~m1_subset_1(B_3, k1_zfmisc_1(u1_struct_0(A_1))) | ~l1_pre_topc(A_1))), inference(cnfTransformation, [status(thm)], [f_34])).
% 16.84/8.72  tff(c_187, plain, (![B_3]: (r2_hidden(B_3, u1_pre_topc('#skF_5')) | ~v3_pre_topc(B_3, '#skF_5') | ~m1_subset_1(B_3, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_165, c_4])).
% 16.84/8.72  tff(c_204, plain, (![B_3]: (r2_hidden(B_3, u1_pre_topc('#skF_5')) | ~v3_pre_topc(B_3, '#skF_5') | ~m1_subset_1(B_3, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_187])).
% 16.84/8.72  tff(c_373, plain, (![B_3]: (r2_hidden(B_3, u1_pre_topc('#skF_4')) | ~v3_pre_topc(B_3, '#skF_5') | ~m1_subset_1(B_3, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_365, c_204])).
% 16.84/8.72  tff(c_2183, plain, (![B_250, C_251]: (r2_hidden('#skF_1'('#skF_5', B_250, C_251), u1_pre_topc('#skF_4')) | ~v3_pre_topc('#skF_1'('#skF_5', B_250, C_251), '#skF_5') | ~r1_tarski(C_251, B_250) | ~m1_subset_1(C_251, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~v2_tex_2(B_250, '#skF_5') | ~m1_subset_1(B_250, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_1571, c_373])).
% 16.84/8.72  tff(c_2, plain, (![B_3, A_1]: (v3_pre_topc(B_3, A_1) | ~r2_hidden(B_3, u1_pre_topc(A_1)) | ~m1_subset_1(B_3, k1_zfmisc_1(u1_struct_0(A_1))) | ~l1_pre_topc(A_1))), inference(cnfTransformation, [status(thm)], [f_34])).
% 16.84/8.72  tff(c_1658, plain, (![B_172, C_173]: (v3_pre_topc('#skF_1'('#skF_5', B_172, C_173), '#skF_4') | ~r2_hidden('#skF_1'('#skF_5', B_172, C_173), u1_pre_topc('#skF_4')) | ~l1_pre_topc('#skF_4') | ~r1_tarski(C_173, B_172) | ~m1_subset_1(C_173, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~v2_tex_2(B_172, '#skF_5') | ~m1_subset_1(B_172, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_1571, c_2])).
% 16.84/8.72  tff(c_1709, plain, (![B_172, C_173]: (v3_pre_topc('#skF_1'('#skF_5', B_172, C_173), '#skF_4') | ~r2_hidden('#skF_1'('#skF_5', B_172, C_173), u1_pre_topc('#skF_4')) | ~r1_tarski(C_173, B_172) | ~m1_subset_1(C_173, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~v2_tex_2(B_172, '#skF_5') | ~m1_subset_1(B_172, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_1658])).
% 16.84/8.72  tff(c_2188, plain, (![B_252, C_253]: (v3_pre_topc('#skF_1'('#skF_5', B_252, C_253), '#skF_4') | ~v3_pre_topc('#skF_1'('#skF_5', B_252, C_253), '#skF_5') | ~r1_tarski(C_253, B_252) | ~m1_subset_1(C_253, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~v2_tex_2(B_252, '#skF_5') | ~m1_subset_1(B_252, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_2183, c_1709])).
% 16.84/8.72  tff(c_2779, plain, (![B_379, B_380]: (v3_pre_topc('#skF_1'('#skF_5', B_379, '#skF_2'('#skF_4', B_380)), '#skF_4') | ~m1_subset_1('#skF_2'('#skF_4', B_380), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r1_tarski('#skF_2'('#skF_4', B_380), B_379) | ~v2_tex_2(B_379, '#skF_5') | ~m1_subset_1(B_379, k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_tex_2(B_380, '#skF_4') | ~m1_subset_1(B_380, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_1097, c_2188])).
% 16.84/8.72  tff(c_2782, plain, (![B_379, B_25]: (v3_pre_topc('#skF_1'('#skF_5', B_379, '#skF_2'('#skF_4', B_25)), '#skF_4') | ~r1_tarski('#skF_2'('#skF_4', B_25), B_379) | ~v2_tex_2(B_379, '#skF_5') | ~m1_subset_1(B_379, k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_tex_2(B_25, '#skF_4') | ~m1_subset_1(B_25, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4'))), inference(resolution, [status(thm)], [c_16, c_2779])).
% 16.84/8.72  tff(c_2785, plain, (![B_379, B_25]: (v3_pre_topc('#skF_1'('#skF_5', B_379, '#skF_2'('#skF_4', B_25)), '#skF_4') | ~r1_tarski('#skF_2'('#skF_4', B_25), B_379) | ~v2_tex_2(B_379, '#skF_5') | ~m1_subset_1(B_379, k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_tex_2(B_25, '#skF_4') | ~m1_subset_1(B_25, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_2782])).
% 16.84/8.72  tff(c_1292, plain, (![B_146, C_147]: (m1_subset_1('#skF_1'('#skF_5', B_146, C_147), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r1_tarski(C_147, B_146) | ~m1_subset_1(C_147, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~v2_tex_2(B_146, '#skF_5') | ~m1_subset_1(B_146, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_165, c_165, c_1225])).
% 16.84/8.72  tff(c_1355, plain, (![A_156, B_157, C_158]: (k9_subset_1(u1_struct_0(A_156), B_157, '#skF_1'(A_156, B_157, C_158))=C_158 | ~r1_tarski(C_158, B_157) | ~m1_subset_1(C_158, k1_zfmisc_1(u1_struct_0(A_156))) | ~v2_tex_2(B_157, A_156) | ~m1_subset_1(B_157, k1_zfmisc_1(u1_struct_0(A_156))) | ~l1_pre_topc(A_156))), inference(cnfTransformation, [status(thm)], [f_68])).
% 16.84/8.72  tff(c_1365, plain, (![B_157, C_158]: (k9_subset_1(u1_struct_0('#skF_5'), B_157, '#skF_1'('#skF_5', B_157, C_158))=C_158 | ~r1_tarski(C_158, B_157) | ~m1_subset_1(C_158, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~v2_tex_2(B_157, '#skF_5') | ~m1_subset_1(B_157, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_165, c_1355])).
% 16.84/8.72  tff(c_1715, plain, (![B_178, C_179]: (k9_subset_1(u1_struct_0('#skF_4'), B_178, '#skF_1'('#skF_5', B_178, C_179))=C_179 | ~r1_tarski(C_179, B_178) | ~m1_subset_1(C_179, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~v2_tex_2(B_178, '#skF_5') | ~m1_subset_1(B_178, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_165, c_165, c_1365])).
% 16.84/8.72  tff(c_1730, plain, (![B_178, B_25]: (k9_subset_1(u1_struct_0('#skF_4'), B_178, '#skF_1'('#skF_5', B_178, '#skF_2'('#skF_4', B_25)))='#skF_2'('#skF_4', B_25) | ~r1_tarski('#skF_2'('#skF_4', B_25), B_178) | ~v2_tex_2(B_178, '#skF_5') | ~m1_subset_1(B_178, k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_tex_2(B_25, '#skF_4') | ~m1_subset_1(B_25, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4'))), inference(resolution, [status(thm)], [c_16, c_1715])).
% 16.84/8.72  tff(c_2588, plain, (![B_333, B_334]: (k9_subset_1(u1_struct_0('#skF_4'), B_333, '#skF_1'('#skF_5', B_333, '#skF_2'('#skF_4', B_334)))='#skF_2'('#skF_4', B_334) | ~r1_tarski('#skF_2'('#skF_4', B_334), B_333) | ~v2_tex_2(B_333, '#skF_5') | ~m1_subset_1(B_333, k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_tex_2(B_334, '#skF_4') | ~m1_subset_1(B_334, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_1730])).
% 16.84/8.72  tff(c_12, plain, (![A_11, B_25, D_35]: (k9_subset_1(u1_struct_0(A_11), B_25, D_35)!='#skF_2'(A_11, B_25) | ~v3_pre_topc(D_35, A_11) | ~m1_subset_1(D_35, k1_zfmisc_1(u1_struct_0(A_11))) | v2_tex_2(B_25, A_11) | ~m1_subset_1(B_25, k1_zfmisc_1(u1_struct_0(A_11))) | ~l1_pre_topc(A_11))), inference(cnfTransformation, [status(thm)], [f_68])).
% 16.84/8.72  tff(c_2595, plain, (![B_334, B_333]: ('#skF_2'('#skF_4', B_334)!='#skF_2'('#skF_4', B_333) | ~v3_pre_topc('#skF_1'('#skF_5', B_333, '#skF_2'('#skF_4', B_334)), '#skF_4') | ~m1_subset_1('#skF_1'('#skF_5', B_333, '#skF_2'('#skF_4', B_334)), k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_tex_2(B_333, '#skF_4') | ~m1_subset_1(B_333, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4') | ~r1_tarski('#skF_2'('#skF_4', B_334), B_333) | ~v2_tex_2(B_333, '#skF_5') | ~m1_subset_1(B_333, k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_tex_2(B_334, '#skF_4') | ~m1_subset_1(B_334, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(superposition, [status(thm), theory('equality')], [c_2588, c_12])).
% 16.84/8.72  tff(c_3758, plain, (![B_628, B_627]: ('#skF_2'('#skF_4', B_628)!='#skF_2'('#skF_4', B_627) | ~v3_pre_topc('#skF_1'('#skF_5', B_628, '#skF_2'('#skF_4', B_627)), '#skF_4') | ~m1_subset_1('#skF_1'('#skF_5', B_628, '#skF_2'('#skF_4', B_627)), k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_tex_2(B_628, '#skF_4') | ~r1_tarski('#skF_2'('#skF_4', B_627), B_628) | ~v2_tex_2(B_628, '#skF_5') | ~m1_subset_1(B_628, k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_tex_2(B_627, '#skF_4') | ~m1_subset_1(B_627, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_2595])).
% 16.84/8.72  tff(c_3764, plain, (![B_630, B_629]: ('#skF_2'('#skF_4', B_630)!='#skF_2'('#skF_4', B_629) | ~v3_pre_topc('#skF_1'('#skF_5', B_630, '#skF_2'('#skF_4', B_629)), '#skF_4') | v2_tex_2(B_630, '#skF_4') | v2_tex_2(B_629, '#skF_4') | ~m1_subset_1(B_629, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r1_tarski('#skF_2'('#skF_4', B_629), B_630) | ~m1_subset_1('#skF_2'('#skF_4', B_629), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~v2_tex_2(B_630, '#skF_5') | ~m1_subset_1(B_630, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_1292, c_3758])).
% 16.84/8.72  tff(c_3768, plain, (![B_632, B_631]: ('#skF_2'('#skF_4', B_632)!='#skF_2'('#skF_4', B_631) | v2_tex_2(B_631, '#skF_4') | ~m1_subset_1('#skF_2'('#skF_4', B_632), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r1_tarski('#skF_2'('#skF_4', B_632), B_631) | ~v2_tex_2(B_631, '#skF_5') | ~m1_subset_1(B_631, k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_tex_2(B_632, '#skF_4') | ~m1_subset_1(B_632, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_2785, c_3764])).
% 16.84/8.72  tff(c_3771, plain, (![B_631, B_25]: ('#skF_2'('#skF_4', B_631)!='#skF_2'('#skF_4', B_25) | v2_tex_2(B_631, '#skF_4') | ~r1_tarski('#skF_2'('#skF_4', B_25), B_631) | ~v2_tex_2(B_631, '#skF_5') | ~m1_subset_1(B_631, k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_tex_2(B_25, '#skF_4') | ~m1_subset_1(B_25, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4'))), inference(resolution, [status(thm)], [c_16, c_3768])).
% 16.84/8.72  tff(c_3775, plain, (![B_634, B_633]: ('#skF_2'('#skF_4', B_634)!='#skF_2'('#skF_4', B_633) | v2_tex_2(B_633, '#skF_4') | ~r1_tarski('#skF_2'('#skF_4', B_634), B_633) | ~v2_tex_2(B_633, '#skF_5') | ~m1_subset_1(B_633, k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_tex_2(B_634, '#skF_4') | ~m1_subset_1(B_634, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_3771])).
% 16.84/8.72  tff(c_3925, plain, (![B_648]: (~v2_tex_2('#skF_3'('#skF_5', B_648), '#skF_5') | ~m1_subset_1('#skF_3'('#skF_5', B_648), k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_tex_2('#skF_3'('#skF_5', B_648), '#skF_4') | v3_tex_2(B_648, '#skF_5') | ~v2_tex_2(B_648, '#skF_5') | ~m1_subset_1(B_648, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_661, c_3775])).
% 16.84/8.72  tff(c_3948, plain, (![B_653]: (~v2_tex_2('#skF_3'('#skF_5', B_653), '#skF_5') | v2_tex_2('#skF_3'('#skF_5', B_653), '#skF_4') | v3_tex_2(B_653, '#skF_5') | ~v2_tex_2(B_653, '#skF_5') | ~m1_subset_1(B_653, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_600, c_3925])).
% 16.84/8.72  tff(c_3972, plain, (~v2_tex_2('#skF_3'('#skF_5', '#skF_6'), '#skF_5') | v2_tex_2('#skF_3'('#skF_5', '#skF_6'), '#skF_4') | v3_tex_2('#skF_6', '#skF_5') | ~v2_tex_2('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_46, c_3948])).
% 16.84/8.72  tff(c_3987, plain, (v2_tex_2('#skF_3'('#skF_5', '#skF_6'), '#skF_4') | v3_tex_2('#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_139, c_522, c_3972])).
% 16.84/8.72  tff(c_3989, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_825, c_3987])).
% 16.84/8.72  tff(c_3991, plain, (~v2_tex_2('#skF_6', '#skF_5')), inference(splitRight, [status(thm)], [c_138])).
% 16.84/8.72  tff(c_62, plain, (![B_58, A_59]: (v2_tex_2(B_58, A_59) | ~v3_tex_2(B_58, A_59) | ~m1_subset_1(B_58, k1_zfmisc_1(u1_struct_0(A_59))) | ~l1_pre_topc(A_59))), inference(cnfTransformation, [status(thm)], [f_86])).
% 16.84/8.72  tff(c_65, plain, (v2_tex_2('#skF_6', '#skF_4') | ~v3_tex_2('#skF_6', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_46, c_62])).
% 16.84/8.72  tff(c_71, plain, (v2_tex_2('#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_38, c_65])).
% 16.84/8.72  tff(c_3990, plain, (r1_tarski('#skF_2'('#skF_5', '#skF_6'), '#skF_6')), inference(splitRight, [status(thm)], [c_138])).
% 16.84/8.72  tff(c_3999, plain, (u1_struct_0('#skF_5')=u1_struct_0('#skF_4') | ~l1_pre_topc('#skF_4')), inference(reflexivity, [status(thm), theory('equality')], [c_125])).
% 16.84/8.72  tff(c_4001, plain, (u1_struct_0('#skF_5')=u1_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_3999])).
% 16.84/8.72  tff(c_4070, plain, (![A_658, B_659]: (m1_subset_1('#skF_2'(A_658, B_659), k1_zfmisc_1(u1_struct_0(A_658))) | v2_tex_2(B_659, A_658) | ~m1_subset_1(B_659, k1_zfmisc_1(u1_struct_0(A_658))) | ~l1_pre_topc(A_658))), inference(cnfTransformation, [status(thm)], [f_68])).
% 16.84/8.72  tff(c_4088, plain, (![B_659]: (m1_subset_1('#skF_2'('#skF_5', B_659), k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_tex_2(B_659, '#skF_5') | ~m1_subset_1(B_659, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_4001, c_4070])).
% 16.84/8.72  tff(c_4097, plain, (![B_659]: (m1_subset_1('#skF_2'('#skF_5', B_659), k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_tex_2(B_659, '#skF_5') | ~m1_subset_1(B_659, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_4001, c_4088])).
% 16.84/8.72  tff(c_4605, plain, (![A_694, B_695, C_696]: (v3_pre_topc('#skF_1'(A_694, B_695, C_696), A_694) | ~r1_tarski(C_696, B_695) | ~m1_subset_1(C_696, k1_zfmisc_1(u1_struct_0(A_694))) | ~v2_tex_2(B_695, A_694) | ~m1_subset_1(B_695, k1_zfmisc_1(u1_struct_0(A_694))) | ~l1_pre_topc(A_694))), inference(cnfTransformation, [status(thm)], [f_68])).
% 16.84/8.72  tff(c_4611, plain, (![B_695, B_659]: (v3_pre_topc('#skF_1'('#skF_4', B_695, '#skF_2'('#skF_5', B_659)), '#skF_4') | ~r1_tarski('#skF_2'('#skF_5', B_659), B_695) | ~v2_tex_2(B_695, '#skF_4') | ~m1_subset_1(B_695, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4') | v2_tex_2(B_659, '#skF_5') | ~m1_subset_1(B_659, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_4097, c_4605])).
% 16.84/8.72  tff(c_4624, plain, (![B_695, B_659]: (v3_pre_topc('#skF_1'('#skF_4', B_695, '#skF_2'('#skF_5', B_659)), '#skF_4') | ~r1_tarski('#skF_2'('#skF_5', B_659), B_695) | ~v2_tex_2(B_695, '#skF_4') | ~m1_subset_1(B_695, k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_tex_2(B_659, '#skF_5') | ~m1_subset_1(B_659, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_4611])).
% 16.84/8.72  tff(c_4714, plain, (![A_705, B_706, C_707]: (m1_subset_1('#skF_1'(A_705, B_706, C_707), k1_zfmisc_1(u1_struct_0(A_705))) | ~r1_tarski(C_707, B_706) | ~m1_subset_1(C_707, k1_zfmisc_1(u1_struct_0(A_705))) | ~v2_tex_2(B_706, A_705) | ~m1_subset_1(B_706, k1_zfmisc_1(u1_struct_0(A_705))) | ~l1_pre_topc(A_705))), inference(cnfTransformation, [status(thm)], [f_68])).
% 16.84/8.72  tff(c_4832, plain, (![A_705, B_706, C_707]: (r2_hidden('#skF_1'(A_705, B_706, C_707), u1_pre_topc(A_705)) | ~v3_pre_topc('#skF_1'(A_705, B_706, C_707), A_705) | ~r1_tarski(C_707, B_706) | ~m1_subset_1(C_707, k1_zfmisc_1(u1_struct_0(A_705))) | ~v2_tex_2(B_706, A_705) | ~m1_subset_1(B_706, k1_zfmisc_1(u1_struct_0(A_705))) | ~l1_pre_topc(A_705))), inference(resolution, [status(thm)], [c_4714, c_4])).
% 16.84/8.72  tff(c_4029, plain, (m1_subset_1(u1_pre_topc('#skF_5'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) | ~l1_pre_topc('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_4001, c_6])).
% 16.84/8.72  tff(c_4041, plain, (m1_subset_1(u1_pre_topc('#skF_5'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_4029])).
% 16.84/8.72  tff(c_4012, plain, (g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_5'))=g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_4001, c_42])).
% 16.84/8.72  tff(c_8, plain, (![D_10, B_6, C_9, A_5]: (D_10=B_6 | g1_pre_topc(C_9, D_10)!=g1_pre_topc(A_5, B_6) | ~m1_subset_1(B_6, k1_zfmisc_1(k1_zfmisc_1(A_5))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 16.84/8.72  tff(c_4052, plain, (![D_10, C_9]: (u1_pre_topc('#skF_5')=D_10 | g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))!=g1_pre_topc(C_9, D_10) | ~m1_subset_1(u1_pre_topc('#skF_5'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))))), inference(superposition, [status(thm), theory('equality')], [c_4012, c_8])).
% 16.84/8.72  tff(c_4060, plain, (![D_10, C_9]: (u1_pre_topc('#skF_5')=D_10 | g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))!=g1_pre_topc(C_9, D_10))), inference(demodulation, [status(thm), theory('equality')], [c_4041, c_4052])).
% 16.84/8.72  tff(c_4100, plain, (u1_pre_topc('#skF_5')=u1_pre_topc('#skF_4')), inference(reflexivity, [status(thm), theory('equality')], [c_4060])).
% 16.84/8.72  tff(c_4023, plain, (![B_3]: (v3_pre_topc(B_3, '#skF_5') | ~r2_hidden(B_3, u1_pre_topc('#skF_5')) | ~m1_subset_1(B_3, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_4001, c_2])).
% 16.84/8.72  tff(c_4037, plain, (![B_3]: (v3_pre_topc(B_3, '#skF_5') | ~r2_hidden(B_3, u1_pre_topc('#skF_5')) | ~m1_subset_1(B_3, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_4023])).
% 16.84/8.72  tff(c_4147, plain, (![B_3]: (v3_pre_topc(B_3, '#skF_5') | ~r2_hidden(B_3, u1_pre_topc('#skF_4')) | ~m1_subset_1(B_3, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_4100, c_4037])).
% 16.84/8.72  tff(c_4765, plain, (![B_706, C_707]: (v3_pre_topc('#skF_1'('#skF_4', B_706, C_707), '#skF_5') | ~r2_hidden('#skF_1'('#skF_4', B_706, C_707), u1_pre_topc('#skF_4')) | ~r1_tarski(C_707, B_706) | ~m1_subset_1(C_707, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~v2_tex_2(B_706, '#skF_4') | ~m1_subset_1(B_706, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4'))), inference(resolution, [status(thm)], [c_4714, c_4147])).
% 16.84/8.72  tff(c_5967, plain, (![B_825, C_826]: (v3_pre_topc('#skF_1'('#skF_4', B_825, C_826), '#skF_5') | ~r2_hidden('#skF_1'('#skF_4', B_825, C_826), u1_pre_topc('#skF_4')) | ~r1_tarski(C_826, B_825) | ~m1_subset_1(C_826, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~v2_tex_2(B_825, '#skF_4') | ~m1_subset_1(B_825, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_4765])).
% 16.84/8.72  tff(c_5971, plain, (![B_706, C_707]: (v3_pre_topc('#skF_1'('#skF_4', B_706, C_707), '#skF_5') | ~v3_pre_topc('#skF_1'('#skF_4', B_706, C_707), '#skF_4') | ~r1_tarski(C_707, B_706) | ~m1_subset_1(C_707, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~v2_tex_2(B_706, '#skF_4') | ~m1_subset_1(B_706, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4'))), inference(resolution, [status(thm)], [c_4832, c_5967])).
% 16.84/8.72  tff(c_5975, plain, (![B_827, C_828]: (v3_pre_topc('#skF_1'('#skF_4', B_827, C_828), '#skF_5') | ~v3_pre_topc('#skF_1'('#skF_4', B_827, C_828), '#skF_4') | ~r1_tarski(C_828, B_827) | ~m1_subset_1(C_828, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~v2_tex_2(B_827, '#skF_4') | ~m1_subset_1(B_827, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_5971])).
% 16.84/8.72  tff(c_6001, plain, (![B_827, B_659]: (v3_pre_topc('#skF_1'('#skF_4', B_827, '#skF_2'('#skF_5', B_659)), '#skF_5') | ~v3_pre_topc('#skF_1'('#skF_4', B_827, '#skF_2'('#skF_5', B_659)), '#skF_4') | ~r1_tarski('#skF_2'('#skF_5', B_659), B_827) | ~v2_tex_2(B_827, '#skF_4') | ~m1_subset_1(B_827, k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_tex_2(B_659, '#skF_5') | ~m1_subset_1(B_659, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_4097, c_5975])).
% 16.84/8.72  tff(c_22, plain, (![A_11, B_25, C_32]: (m1_subset_1('#skF_1'(A_11, B_25, C_32), k1_zfmisc_1(u1_struct_0(A_11))) | ~r1_tarski(C_32, B_25) | ~m1_subset_1(C_32, k1_zfmisc_1(u1_struct_0(A_11))) | ~v2_tex_2(B_25, A_11) | ~m1_subset_1(B_25, k1_zfmisc_1(u1_struct_0(A_11))) | ~l1_pre_topc(A_11))), inference(cnfTransformation, [status(thm)], [f_68])).
% 16.84/8.72  tff(c_5152, plain, (![A_731, B_732, C_733]: (k9_subset_1(u1_struct_0(A_731), B_732, '#skF_1'(A_731, B_732, C_733))=C_733 | ~r1_tarski(C_733, B_732) | ~m1_subset_1(C_733, k1_zfmisc_1(u1_struct_0(A_731))) | ~v2_tex_2(B_732, A_731) | ~m1_subset_1(B_732, k1_zfmisc_1(u1_struct_0(A_731))) | ~l1_pre_topc(A_731))), inference(cnfTransformation, [status(thm)], [f_68])).
% 16.84/8.72  tff(c_5160, plain, (![B_732, B_659]: (k9_subset_1(u1_struct_0('#skF_4'), B_732, '#skF_1'('#skF_4', B_732, '#skF_2'('#skF_5', B_659)))='#skF_2'('#skF_5', B_659) | ~r1_tarski('#skF_2'('#skF_5', B_659), B_732) | ~v2_tex_2(B_732, '#skF_4') | ~m1_subset_1(B_732, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4') | v2_tex_2(B_659, '#skF_5') | ~m1_subset_1(B_659, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_4097, c_5152])).
% 16.84/8.72  tff(c_6372, plain, (![B_908, B_909]: (k9_subset_1(u1_struct_0('#skF_4'), B_908, '#skF_1'('#skF_4', B_908, '#skF_2'('#skF_5', B_909)))='#skF_2'('#skF_5', B_909) | ~r1_tarski('#skF_2'('#skF_5', B_909), B_908) | ~v2_tex_2(B_908, '#skF_4') | ~m1_subset_1(B_908, k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_tex_2(B_909, '#skF_5') | ~m1_subset_1(B_909, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_5160])).
% 16.84/8.72  tff(c_5079, plain, (![A_719, B_720, D_721]: (k9_subset_1(u1_struct_0(A_719), B_720, D_721)!='#skF_2'(A_719, B_720) | ~v3_pre_topc(D_721, A_719) | ~m1_subset_1(D_721, k1_zfmisc_1(u1_struct_0(A_719))) | v2_tex_2(B_720, A_719) | ~m1_subset_1(B_720, k1_zfmisc_1(u1_struct_0(A_719))) | ~l1_pre_topc(A_719))), inference(cnfTransformation, [status(thm)], [f_68])).
% 16.84/8.72  tff(c_5081, plain, (![B_720, D_721]: (k9_subset_1(u1_struct_0('#skF_4'), B_720, D_721)!='#skF_2'('#skF_5', B_720) | ~v3_pre_topc(D_721, '#skF_5') | ~m1_subset_1(D_721, k1_zfmisc_1(u1_struct_0('#skF_5'))) | v2_tex_2(B_720, '#skF_5') | ~m1_subset_1(B_720, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_4001, c_5079])).
% 16.84/8.72  tff(c_5083, plain, (![B_720, D_721]: (k9_subset_1(u1_struct_0('#skF_4'), B_720, D_721)!='#skF_2'('#skF_5', B_720) | ~v3_pre_topc(D_721, '#skF_5') | ~m1_subset_1(D_721, k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_tex_2(B_720, '#skF_5') | ~m1_subset_1(B_720, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_4001, c_4001, c_5081])).
% 16.84/8.72  tff(c_8655, plain, (![B_1406, B_1405]: ('#skF_2'('#skF_5', B_1406)!='#skF_2'('#skF_5', B_1405) | ~v3_pre_topc('#skF_1'('#skF_4', B_1406, '#skF_2'('#skF_5', B_1405)), '#skF_5') | ~m1_subset_1('#skF_1'('#skF_4', B_1406, '#skF_2'('#skF_5', B_1405)), k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_tex_2(B_1406, '#skF_5') | ~m1_subset_1(B_1406, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r1_tarski('#skF_2'('#skF_5', B_1405), B_1406) | ~v2_tex_2(B_1406, '#skF_4') | ~m1_subset_1(B_1406, k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_tex_2(B_1405, '#skF_5') | ~m1_subset_1(B_1405, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(superposition, [status(thm), theory('equality')], [c_6372, c_5083])).
% 16.84/8.72  tff(c_8659, plain, (![B_25, B_1405]: ('#skF_2'('#skF_5', B_25)!='#skF_2'('#skF_5', B_1405) | ~v3_pre_topc('#skF_1'('#skF_4', B_25, '#skF_2'('#skF_5', B_1405)), '#skF_5') | v2_tex_2(B_25, '#skF_5') | v2_tex_2(B_1405, '#skF_5') | ~m1_subset_1(B_1405, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r1_tarski('#skF_2'('#skF_5', B_1405), B_25) | ~m1_subset_1('#skF_2'('#skF_5', B_1405), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~v2_tex_2(B_25, '#skF_4') | ~m1_subset_1(B_25, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4'))), inference(resolution, [status(thm)], [c_22, c_8655])).
% 16.84/8.72  tff(c_8663, plain, (![B_1408, B_1407]: ('#skF_2'('#skF_5', B_1408)!='#skF_2'('#skF_5', B_1407) | ~v3_pre_topc('#skF_1'('#skF_4', B_1407, '#skF_2'('#skF_5', B_1408)), '#skF_5') | v2_tex_2(B_1407, '#skF_5') | v2_tex_2(B_1408, '#skF_5') | ~m1_subset_1(B_1408, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r1_tarski('#skF_2'('#skF_5', B_1408), B_1407) | ~m1_subset_1('#skF_2'('#skF_5', B_1408), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~v2_tex_2(B_1407, '#skF_4') | ~m1_subset_1(B_1407, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_8659])).
% 16.84/8.72  tff(c_8667, plain, (![B_1410, B_1409]: ('#skF_2'('#skF_5', B_1410)!='#skF_2'('#skF_5', B_1409) | v2_tex_2(B_1409, '#skF_5') | ~m1_subset_1('#skF_2'('#skF_5', B_1410), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~v3_pre_topc('#skF_1'('#skF_4', B_1409, '#skF_2'('#skF_5', B_1410)), '#skF_4') | ~r1_tarski('#skF_2'('#skF_5', B_1410), B_1409) | ~v2_tex_2(B_1409, '#skF_4') | ~m1_subset_1(B_1409, k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_tex_2(B_1410, '#skF_5') | ~m1_subset_1(B_1410, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_6001, c_8663])).
% 16.84/8.72  tff(c_8671, plain, (![B_1412, B_1411]: ('#skF_2'('#skF_5', B_1412)!='#skF_2'('#skF_5', B_1411) | v2_tex_2(B_1412, '#skF_5') | ~v3_pre_topc('#skF_1'('#skF_4', B_1412, '#skF_2'('#skF_5', B_1411)), '#skF_4') | ~r1_tarski('#skF_2'('#skF_5', B_1411), B_1412) | ~v2_tex_2(B_1412, '#skF_4') | ~m1_subset_1(B_1412, k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_tex_2(B_1411, '#skF_5') | ~m1_subset_1(B_1411, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_4097, c_8667])).
% 16.84/8.72  tff(c_8676, plain, (![B_1414, B_1413]: ('#skF_2'('#skF_5', B_1414)!='#skF_2'('#skF_5', B_1413) | v2_tex_2(B_1413, '#skF_5') | ~r1_tarski('#skF_2'('#skF_5', B_1414), B_1413) | ~v2_tex_2(B_1413, '#skF_4') | ~m1_subset_1(B_1413, k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_tex_2(B_1414, '#skF_5') | ~m1_subset_1(B_1414, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_4624, c_8671])).
% 16.84/8.72  tff(c_8701, plain, (~v2_tex_2('#skF_6', '#skF_4') | v2_tex_2('#skF_6', '#skF_5') | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_3990, c_8676])).
% 16.84/8.72  tff(c_8720, plain, (v2_tex_2('#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_71, c_8701])).
% 16.84/8.72  tff(c_8722, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3991, c_8720])).
% 16.84/8.72  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 16.84/8.72  
% 16.84/8.72  Inference rules
% 16.84/8.72  ----------------------
% 16.84/8.72  #Ref     : 11
% 16.84/8.72  #Sup     : 1648
% 16.84/8.72  #Fact    : 0
% 16.84/8.72  #Define  : 0
% 16.84/8.72  #Split   : 13
% 16.84/8.72  #Chain   : 0
% 16.84/8.72  #Close   : 0
% 16.84/8.72  
% 16.84/8.72  Ordering : KBO
% 16.84/8.72  
% 16.84/8.72  Simplification rules
% 16.84/8.72  ----------------------
% 16.84/8.72  #Subsume      : 258
% 16.84/8.72  #Demod        : 1070
% 16.84/8.72  #Tautology    : 478
% 16.84/8.72  #SimpNegUnit  : 45
% 16.84/8.72  #BackRed      : 16
% 16.84/8.72  
% 16.84/8.72  #Partial instantiations: 0
% 16.84/8.72  #Strategies tried      : 1
% 16.84/8.72  
% 16.84/8.72  Timing (in seconds)
% 16.84/8.72  ----------------------
% 16.84/8.73  Preprocessing        : 0.53
% 16.84/8.73  Parsing              : 0.27
% 16.84/8.73  CNF conversion       : 0.04
% 16.84/8.73  Main loop            : 7.39
% 16.84/8.73  Inferencing          : 3.16
% 16.84/8.73  Reduction            : 1.74
% 16.84/8.73  Demodulation         : 1.07
% 16.84/8.73  BG Simplification    : 0.15
% 16.84/8.73  Subsumption          : 1.97
% 16.84/8.73  Abstraction          : 0.17
% 16.84/8.73  MUC search           : 0.00
% 16.84/8.73  Cooper               : 0.00
% 16.84/8.73  Total                : 7.98
% 16.84/8.73  Index Insertion      : 0.00
% 16.84/8.73  Index Deletion       : 0.00
% 16.84/8.73  Index Matching       : 0.00
% 16.84/8.73  BG Taut test         : 0.00
%------------------------------------------------------------------------------
