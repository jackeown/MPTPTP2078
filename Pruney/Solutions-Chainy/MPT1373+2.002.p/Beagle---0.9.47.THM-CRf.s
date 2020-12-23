%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:01 EST 2020

% Result     : Theorem 5.01s
% Output     : CNFRefutation 5.26s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 261 expanded)
%              Number of leaves         :   27 ( 102 expanded)
%              Depth                    :   13
%              Number of atoms          :  170 ( 714 expanded)
%              Number of equality atoms :   17 ( 101 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_compts_1 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > l1_struct_0 > l1_pre_topc > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_compts_1,type,(
    v2_compts_1: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

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

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_101,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_pre_topc(B,A)
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(B)))
                   => ( C = D
                     => ( v2_compts_1(C,A)
                      <=> v2_compts_1(D,B) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_compts_1)).

tff(f_47,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_43,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_54,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_83,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( r1_tarski(C,k2_struct_0(B))
               => ( v2_compts_1(C,A)
                <=> ! [D] :
                      ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(B)))
                     => ( D = C
                       => v2_compts_1(D,B) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_compts_1)).

tff(f_64,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(B)))
             => m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_pre_topc)).

tff(c_26,plain,(
    '#skF_5' = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_42,plain,
    ( v2_compts_1('#skF_5','#skF_3')
    | v2_compts_1('#skF_6','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_45,plain,
    ( v2_compts_1('#skF_6','#skF_3')
    | v2_compts_1('#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_42])).

tff(c_51,plain,(
    v2_compts_1('#skF_6','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_45])).

tff(c_36,plain,
    ( ~ v2_compts_1('#skF_6','#skF_4')
    | ~ v2_compts_1('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_43,plain,
    ( ~ v2_compts_1('#skF_6','#skF_4')
    | ~ v2_compts_1('#skF_6','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_36])).

tff(c_58,plain,(
    ~ v2_compts_1('#skF_6','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_51,c_43])).

tff(c_34,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_32,plain,(
    m1_pre_topc('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_12,plain,(
    ! [A_11] :
      ( l1_struct_0(A_11)
      | ~ l1_pre_topc(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_52,plain,(
    ! [A_56] :
      ( u1_struct_0(A_56) = k2_struct_0(A_56)
      | ~ l1_struct_0(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_59,plain,(
    ! [A_57] :
      ( u1_struct_0(A_57) = k2_struct_0(A_57)
      | ~ l1_pre_topc(A_57) ) ),
    inference(resolution,[status(thm)],[c_12,c_52])).

tff(c_63,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_59])).

tff(c_30,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_44,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_30])).

tff(c_64,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_44])).

tff(c_69,plain,(
    ! [B_58,A_59] :
      ( l1_pre_topc(B_58)
      | ~ m1_pre_topc(B_58,A_59)
      | ~ l1_pre_topc(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_72,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_69])).

tff(c_75,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_72])).

tff(c_56,plain,(
    ! [A_11] :
      ( u1_struct_0(A_11) = k2_struct_0(A_11)
      | ~ l1_pre_topc(A_11) ) ),
    inference(resolution,[status(thm)],[c_12,c_52])).

tff(c_79,plain,(
    u1_struct_0('#skF_4') = k2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_75,c_56])).

tff(c_28,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_81,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_struct_0('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_28])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_97,plain,(
    ! [C_68,A_69,B_70] :
      ( r2_hidden(C_68,A_69)
      | ~ r2_hidden(C_68,B_70)
      | ~ m1_subset_1(B_70,k1_zfmisc_1(A_69)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_113,plain,(
    ! [A_74,B_75,A_76] :
      ( r2_hidden('#skF_1'(A_74,B_75),A_76)
      | ~ m1_subset_1(A_74,k1_zfmisc_1(A_76))
      | r1_tarski(A_74,B_75) ) ),
    inference(resolution,[status(thm)],[c_6,c_97])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_125,plain,(
    ! [A_77,A_78] :
      ( ~ m1_subset_1(A_77,k1_zfmisc_1(A_78))
      | r1_tarski(A_77,A_78) ) ),
    inference(resolution,[status(thm)],[c_113,c_4])).

tff(c_132,plain,(
    r1_tarski('#skF_6',k2_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_81,c_125])).

tff(c_200,plain,(
    ! [A_94,B_95,C_96] :
      ( '#skF_2'(A_94,B_95,C_96) = C_96
      | v2_compts_1(C_96,A_94)
      | ~ r1_tarski(C_96,k2_struct_0(B_95))
      | ~ m1_subset_1(C_96,k1_zfmisc_1(u1_struct_0(A_94)))
      | ~ m1_pre_topc(B_95,A_94)
      | ~ l1_pre_topc(A_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_235,plain,(
    ! [A_100] :
      ( '#skF_2'(A_100,'#skF_4','#skF_6') = '#skF_6'
      | v2_compts_1('#skF_6',A_100)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0(A_100)))
      | ~ m1_pre_topc('#skF_4',A_100)
      | ~ l1_pre_topc(A_100) ) ),
    inference(resolution,[status(thm)],[c_132,c_200])).

tff(c_245,plain,
    ( '#skF_2'('#skF_3','#skF_4','#skF_6') = '#skF_6'
    | v2_compts_1('#skF_6','#skF_3')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_struct_0('#skF_3')))
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_63,c_235])).

tff(c_252,plain,
    ( '#skF_2'('#skF_3','#skF_4','#skF_6') = '#skF_6'
    | v2_compts_1('#skF_6','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_64,c_245])).

tff(c_253,plain,(
    '#skF_2'('#skF_3','#skF_4','#skF_6') = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_252])).

tff(c_309,plain,(
    ! [A_112,B_113,C_114] :
      ( ~ v2_compts_1('#skF_2'(A_112,B_113,C_114),B_113)
      | v2_compts_1(C_114,A_112)
      | ~ r1_tarski(C_114,k2_struct_0(B_113))
      | ~ m1_subset_1(C_114,k1_zfmisc_1(u1_struct_0(A_112)))
      | ~ m1_pre_topc(B_113,A_112)
      | ~ l1_pre_topc(A_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_311,plain,
    ( ~ v2_compts_1('#skF_6','#skF_4')
    | v2_compts_1('#skF_6','#skF_3')
    | ~ r1_tarski('#skF_6',k2_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_253,c_309])).

tff(c_313,plain,(
    v2_compts_1('#skF_6','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_64,c_63,c_132,c_51,c_311])).

tff(c_315,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_313])).

tff(c_317,plain,(
    ~ v2_compts_1('#skF_6','#skF_4') ),
    inference(splitRight,[status(thm)],[c_45])).

tff(c_335,plain,(
    ! [B_117,A_118] :
      ( l1_pre_topc(B_117)
      | ~ m1_pre_topc(B_117,A_118)
      | ~ l1_pre_topc(A_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_338,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_335])).

tff(c_341,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_338])).

tff(c_320,plain,(
    ! [A_115] :
      ( u1_struct_0(A_115) = k2_struct_0(A_115)
      | ~ l1_struct_0(A_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_324,plain,(
    ! [A_11] :
      ( u1_struct_0(A_11) = k2_struct_0(A_11)
      | ~ l1_pre_topc(A_11) ) ),
    inference(resolution,[status(thm)],[c_12,c_320])).

tff(c_345,plain,(
    u1_struct_0('#skF_4') = k2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_341,c_324])).

tff(c_347,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_struct_0('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_345,c_28])).

tff(c_363,plain,(
    ! [C_127,A_128,B_129] :
      ( r2_hidden(C_127,A_128)
      | ~ r2_hidden(C_127,B_129)
      | ~ m1_subset_1(B_129,k1_zfmisc_1(A_128)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_379,plain,(
    ! [A_133,B_134,A_135] :
      ( r2_hidden('#skF_1'(A_133,B_134),A_135)
      | ~ m1_subset_1(A_133,k1_zfmisc_1(A_135))
      | r1_tarski(A_133,B_134) ) ),
    inference(resolution,[status(thm)],[c_6,c_363])).

tff(c_391,plain,(
    ! [A_136,A_137] :
      ( ~ m1_subset_1(A_136,k1_zfmisc_1(A_137))
      | r1_tarski(A_136,A_137) ) ),
    inference(resolution,[status(thm)],[c_379,c_4])).

tff(c_398,plain,(
    r1_tarski('#skF_6',k2_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_347,c_391])).

tff(c_316,plain,(
    v2_compts_1('#skF_6','#skF_3') ),
    inference(splitRight,[status(thm)],[c_45])).

tff(c_400,plain,(
    ! [C_138,A_139,B_140] :
      ( m1_subset_1(C_138,k1_zfmisc_1(u1_struct_0(A_139)))
      | ~ m1_subset_1(C_138,k1_zfmisc_1(u1_struct_0(B_140)))
      | ~ m1_pre_topc(B_140,A_139)
      | ~ l1_pre_topc(A_139) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_402,plain,(
    ! [C_138,A_139] :
      ( m1_subset_1(C_138,k1_zfmisc_1(u1_struct_0(A_139)))
      | ~ m1_subset_1(C_138,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ m1_pre_topc('#skF_4',A_139)
      | ~ l1_pre_topc(A_139) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_345,c_400])).

tff(c_801,plain,(
    ! [D_208,B_209,A_210] :
      ( v2_compts_1(D_208,B_209)
      | ~ m1_subset_1(D_208,k1_zfmisc_1(u1_struct_0(B_209)))
      | ~ v2_compts_1(D_208,A_210)
      | ~ r1_tarski(D_208,k2_struct_0(B_209))
      | ~ m1_subset_1(D_208,k1_zfmisc_1(u1_struct_0(A_210)))
      | ~ m1_pre_topc(B_209,A_210)
      | ~ l1_pre_topc(A_210) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_2303,plain,(
    ! [D_372,A_373] :
      ( v2_compts_1(D_372,'#skF_4')
      | ~ m1_subset_1(D_372,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ v2_compts_1(D_372,A_373)
      | ~ r1_tarski(D_372,k2_struct_0('#skF_4'))
      | ~ m1_subset_1(D_372,k1_zfmisc_1(u1_struct_0(A_373)))
      | ~ m1_pre_topc('#skF_4',A_373)
      | ~ l1_pre_topc(A_373) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_345,c_801])).

tff(c_2341,plain,(
    ! [C_375,A_376] :
      ( v2_compts_1(C_375,'#skF_4')
      | ~ v2_compts_1(C_375,A_376)
      | ~ r1_tarski(C_375,k2_struct_0('#skF_4'))
      | ~ m1_subset_1(C_375,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ m1_pre_topc('#skF_4',A_376)
      | ~ l1_pre_topc(A_376) ) ),
    inference(resolution,[status(thm)],[c_402,c_2303])).

tff(c_2347,plain,
    ( v2_compts_1('#skF_6','#skF_4')
    | ~ r1_tarski('#skF_6',k2_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_struct_0('#skF_4')))
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_316,c_2341])).

tff(c_2358,plain,(
    v2_compts_1('#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_347,c_398,c_2347])).

tff(c_2360,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_317,c_2358])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:46:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.01/1.94  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.01/1.95  
% 5.01/1.95  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.01/1.95  %$ v2_compts_1 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > l1_struct_0 > l1_pre_topc > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4 > #skF_1
% 5.01/1.95  
% 5.01/1.95  %Foreground sorts:
% 5.01/1.95  
% 5.01/1.95  
% 5.01/1.95  %Background operators:
% 5.01/1.95  
% 5.01/1.95  
% 5.01/1.95  %Foreground operators:
% 5.01/1.95  tff(v2_compts_1, type, v2_compts_1: ($i * $i) > $o).
% 5.01/1.95  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.01/1.95  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.01/1.95  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 5.01/1.95  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.01/1.95  tff('#skF_5', type, '#skF_5': $i).
% 5.01/1.95  tff('#skF_6', type, '#skF_6': $i).
% 5.01/1.95  tff('#skF_3', type, '#skF_3': $i).
% 5.01/1.95  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 5.01/1.95  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.01/1.95  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 5.01/1.95  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.01/1.95  tff('#skF_4', type, '#skF_4': $i).
% 5.01/1.95  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.01/1.95  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 5.01/1.95  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.01/1.95  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.01/1.95  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 5.01/1.95  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.01/1.95  
% 5.26/1.97  tff(f_101, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => ((C = D) => (v2_compts_1(C, A) <=> v2_compts_1(D, B))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_compts_1)).
% 5.26/1.97  tff(f_47, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 5.26/1.97  tff(f_43, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 5.26/1.97  tff(f_54, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 5.26/1.97  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 5.26/1.97  tff(f_39, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 5.26/1.97  tff(f_83, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(C, k2_struct_0(B)) => (v2_compts_1(C, A) <=> (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => ((D = C) => v2_compts_1(D, B)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_compts_1)).
% 5.26/1.97  tff(f_64, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B))) => m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_pre_topc)).
% 5.26/1.97  tff(c_26, plain, ('#skF_5'='#skF_6'), inference(cnfTransformation, [status(thm)], [f_101])).
% 5.26/1.97  tff(c_42, plain, (v2_compts_1('#skF_5', '#skF_3') | v2_compts_1('#skF_6', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_101])).
% 5.26/1.97  tff(c_45, plain, (v2_compts_1('#skF_6', '#skF_3') | v2_compts_1('#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_42])).
% 5.26/1.97  tff(c_51, plain, (v2_compts_1('#skF_6', '#skF_4')), inference(splitLeft, [status(thm)], [c_45])).
% 5.26/1.97  tff(c_36, plain, (~v2_compts_1('#skF_6', '#skF_4') | ~v2_compts_1('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_101])).
% 5.26/1.97  tff(c_43, plain, (~v2_compts_1('#skF_6', '#skF_4') | ~v2_compts_1('#skF_6', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_36])).
% 5.26/1.97  tff(c_58, plain, (~v2_compts_1('#skF_6', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_51, c_43])).
% 5.26/1.97  tff(c_34, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_101])).
% 5.26/1.97  tff(c_32, plain, (m1_pre_topc('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_101])).
% 5.26/1.97  tff(c_12, plain, (![A_11]: (l1_struct_0(A_11) | ~l1_pre_topc(A_11))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.26/1.97  tff(c_52, plain, (![A_56]: (u1_struct_0(A_56)=k2_struct_0(A_56) | ~l1_struct_0(A_56))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.26/1.97  tff(c_59, plain, (![A_57]: (u1_struct_0(A_57)=k2_struct_0(A_57) | ~l1_pre_topc(A_57))), inference(resolution, [status(thm)], [c_12, c_52])).
% 5.26/1.97  tff(c_63, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_34, c_59])).
% 5.26/1.97  tff(c_30, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_101])).
% 5.26/1.97  tff(c_44, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_30])).
% 5.26/1.97  tff(c_64, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_63, c_44])).
% 5.26/1.97  tff(c_69, plain, (![B_58, A_59]: (l1_pre_topc(B_58) | ~m1_pre_topc(B_58, A_59) | ~l1_pre_topc(A_59))), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.26/1.97  tff(c_72, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_32, c_69])).
% 5.26/1.97  tff(c_75, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_72])).
% 5.26/1.97  tff(c_56, plain, (![A_11]: (u1_struct_0(A_11)=k2_struct_0(A_11) | ~l1_pre_topc(A_11))), inference(resolution, [status(thm)], [c_12, c_52])).
% 5.26/1.97  tff(c_79, plain, (u1_struct_0('#skF_4')=k2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_75, c_56])).
% 5.26/1.97  tff(c_28, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_101])).
% 5.26/1.97  tff(c_81, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_79, c_28])).
% 5.26/1.97  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.26/1.97  tff(c_97, plain, (![C_68, A_69, B_70]: (r2_hidden(C_68, A_69) | ~r2_hidden(C_68, B_70) | ~m1_subset_1(B_70, k1_zfmisc_1(A_69)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.26/1.97  tff(c_113, plain, (![A_74, B_75, A_76]: (r2_hidden('#skF_1'(A_74, B_75), A_76) | ~m1_subset_1(A_74, k1_zfmisc_1(A_76)) | r1_tarski(A_74, B_75))), inference(resolution, [status(thm)], [c_6, c_97])).
% 5.26/1.97  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.26/1.97  tff(c_125, plain, (![A_77, A_78]: (~m1_subset_1(A_77, k1_zfmisc_1(A_78)) | r1_tarski(A_77, A_78))), inference(resolution, [status(thm)], [c_113, c_4])).
% 5.26/1.97  tff(c_132, plain, (r1_tarski('#skF_6', k2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_81, c_125])).
% 5.26/1.97  tff(c_200, plain, (![A_94, B_95, C_96]: ('#skF_2'(A_94, B_95, C_96)=C_96 | v2_compts_1(C_96, A_94) | ~r1_tarski(C_96, k2_struct_0(B_95)) | ~m1_subset_1(C_96, k1_zfmisc_1(u1_struct_0(A_94))) | ~m1_pre_topc(B_95, A_94) | ~l1_pre_topc(A_94))), inference(cnfTransformation, [status(thm)], [f_83])).
% 5.26/1.97  tff(c_235, plain, (![A_100]: ('#skF_2'(A_100, '#skF_4', '#skF_6')='#skF_6' | v2_compts_1('#skF_6', A_100) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0(A_100))) | ~m1_pre_topc('#skF_4', A_100) | ~l1_pre_topc(A_100))), inference(resolution, [status(thm)], [c_132, c_200])).
% 5.26/1.97  tff(c_245, plain, ('#skF_2'('#skF_3', '#skF_4', '#skF_6')='#skF_6' | v2_compts_1('#skF_6', '#skF_3') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~m1_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_63, c_235])).
% 5.26/1.97  tff(c_252, plain, ('#skF_2'('#skF_3', '#skF_4', '#skF_6')='#skF_6' | v2_compts_1('#skF_6', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_64, c_245])).
% 5.26/1.97  tff(c_253, plain, ('#skF_2'('#skF_3', '#skF_4', '#skF_6')='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_58, c_252])).
% 5.26/1.97  tff(c_309, plain, (![A_112, B_113, C_114]: (~v2_compts_1('#skF_2'(A_112, B_113, C_114), B_113) | v2_compts_1(C_114, A_112) | ~r1_tarski(C_114, k2_struct_0(B_113)) | ~m1_subset_1(C_114, k1_zfmisc_1(u1_struct_0(A_112))) | ~m1_pre_topc(B_113, A_112) | ~l1_pre_topc(A_112))), inference(cnfTransformation, [status(thm)], [f_83])).
% 5.26/1.97  tff(c_311, plain, (~v2_compts_1('#skF_6', '#skF_4') | v2_compts_1('#skF_6', '#skF_3') | ~r1_tarski('#skF_6', k2_struct_0('#skF_4')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_253, c_309])).
% 5.26/1.97  tff(c_313, plain, (v2_compts_1('#skF_6', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_64, c_63, c_132, c_51, c_311])).
% 5.26/1.97  tff(c_315, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_313])).
% 5.26/1.97  tff(c_317, plain, (~v2_compts_1('#skF_6', '#skF_4')), inference(splitRight, [status(thm)], [c_45])).
% 5.26/1.97  tff(c_335, plain, (![B_117, A_118]: (l1_pre_topc(B_117) | ~m1_pre_topc(B_117, A_118) | ~l1_pre_topc(A_118))), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.26/1.97  tff(c_338, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_32, c_335])).
% 5.26/1.97  tff(c_341, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_338])).
% 5.26/1.97  tff(c_320, plain, (![A_115]: (u1_struct_0(A_115)=k2_struct_0(A_115) | ~l1_struct_0(A_115))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.26/1.97  tff(c_324, plain, (![A_11]: (u1_struct_0(A_11)=k2_struct_0(A_11) | ~l1_pre_topc(A_11))), inference(resolution, [status(thm)], [c_12, c_320])).
% 5.26/1.97  tff(c_345, plain, (u1_struct_0('#skF_4')=k2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_341, c_324])).
% 5.26/1.97  tff(c_347, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_345, c_28])).
% 5.26/1.97  tff(c_363, plain, (![C_127, A_128, B_129]: (r2_hidden(C_127, A_128) | ~r2_hidden(C_127, B_129) | ~m1_subset_1(B_129, k1_zfmisc_1(A_128)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.26/1.97  tff(c_379, plain, (![A_133, B_134, A_135]: (r2_hidden('#skF_1'(A_133, B_134), A_135) | ~m1_subset_1(A_133, k1_zfmisc_1(A_135)) | r1_tarski(A_133, B_134))), inference(resolution, [status(thm)], [c_6, c_363])).
% 5.26/1.97  tff(c_391, plain, (![A_136, A_137]: (~m1_subset_1(A_136, k1_zfmisc_1(A_137)) | r1_tarski(A_136, A_137))), inference(resolution, [status(thm)], [c_379, c_4])).
% 5.26/1.97  tff(c_398, plain, (r1_tarski('#skF_6', k2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_347, c_391])).
% 5.26/1.97  tff(c_316, plain, (v2_compts_1('#skF_6', '#skF_3')), inference(splitRight, [status(thm)], [c_45])).
% 5.26/1.97  tff(c_400, plain, (![C_138, A_139, B_140]: (m1_subset_1(C_138, k1_zfmisc_1(u1_struct_0(A_139))) | ~m1_subset_1(C_138, k1_zfmisc_1(u1_struct_0(B_140))) | ~m1_pre_topc(B_140, A_139) | ~l1_pre_topc(A_139))), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.26/1.97  tff(c_402, plain, (![C_138, A_139]: (m1_subset_1(C_138, k1_zfmisc_1(u1_struct_0(A_139))) | ~m1_subset_1(C_138, k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~m1_pre_topc('#skF_4', A_139) | ~l1_pre_topc(A_139))), inference(superposition, [status(thm), theory('equality')], [c_345, c_400])).
% 5.26/1.97  tff(c_801, plain, (![D_208, B_209, A_210]: (v2_compts_1(D_208, B_209) | ~m1_subset_1(D_208, k1_zfmisc_1(u1_struct_0(B_209))) | ~v2_compts_1(D_208, A_210) | ~r1_tarski(D_208, k2_struct_0(B_209)) | ~m1_subset_1(D_208, k1_zfmisc_1(u1_struct_0(A_210))) | ~m1_pre_topc(B_209, A_210) | ~l1_pre_topc(A_210))), inference(cnfTransformation, [status(thm)], [f_83])).
% 5.26/1.97  tff(c_2303, plain, (![D_372, A_373]: (v2_compts_1(D_372, '#skF_4') | ~m1_subset_1(D_372, k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~v2_compts_1(D_372, A_373) | ~r1_tarski(D_372, k2_struct_0('#skF_4')) | ~m1_subset_1(D_372, k1_zfmisc_1(u1_struct_0(A_373))) | ~m1_pre_topc('#skF_4', A_373) | ~l1_pre_topc(A_373))), inference(superposition, [status(thm), theory('equality')], [c_345, c_801])).
% 5.26/1.97  tff(c_2341, plain, (![C_375, A_376]: (v2_compts_1(C_375, '#skF_4') | ~v2_compts_1(C_375, A_376) | ~r1_tarski(C_375, k2_struct_0('#skF_4')) | ~m1_subset_1(C_375, k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~m1_pre_topc('#skF_4', A_376) | ~l1_pre_topc(A_376))), inference(resolution, [status(thm)], [c_402, c_2303])).
% 5.26/1.97  tff(c_2347, plain, (v2_compts_1('#skF_6', '#skF_4') | ~r1_tarski('#skF_6', k2_struct_0('#skF_4')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~m1_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_316, c_2341])).
% 5.26/1.97  tff(c_2358, plain, (v2_compts_1('#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_347, c_398, c_2347])).
% 5.26/1.97  tff(c_2360, plain, $false, inference(negUnitSimplification, [status(thm)], [c_317, c_2358])).
% 5.26/1.97  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.26/1.97  
% 5.26/1.97  Inference rules
% 5.26/1.97  ----------------------
% 5.26/1.97  #Ref     : 0
% 5.26/1.97  #Sup     : 599
% 5.26/1.97  #Fact    : 0
% 5.26/1.97  #Define  : 0
% 5.26/1.97  #Split   : 18
% 5.26/1.97  #Chain   : 0
% 5.26/1.97  #Close   : 0
% 5.26/1.97  
% 5.26/1.97  Ordering : KBO
% 5.26/1.97  
% 5.26/1.97  Simplification rules
% 5.26/1.97  ----------------------
% 5.26/1.97  #Subsume      : 298
% 5.26/1.97  #Demod        : 140
% 5.26/1.97  #Tautology    : 30
% 5.26/1.97  #SimpNegUnit  : 7
% 5.26/1.97  #BackRed      : 4
% 5.26/1.97  
% 5.26/1.97  #Partial instantiations: 0
% 5.26/1.97  #Strategies tried      : 1
% 5.26/1.97  
% 5.26/1.97  Timing (in seconds)
% 5.26/1.97  ----------------------
% 5.26/1.97  Preprocessing        : 0.31
% 5.26/1.97  Parsing              : 0.16
% 5.26/1.97  CNF conversion       : 0.03
% 5.26/1.97  Main loop            : 0.84
% 5.26/1.97  Inferencing          : 0.25
% 5.26/1.97  Reduction            : 0.23
% 5.26/1.97  Demodulation         : 0.15
% 5.26/1.97  BG Simplification    : 0.03
% 5.26/1.97  Subsumption          : 0.28
% 5.26/1.97  Abstraction          : 0.03
% 5.26/1.97  MUC search           : 0.00
% 5.26/1.98  Cooper               : 0.00
% 5.26/1.98  Total                : 1.19
% 5.26/1.98  Index Insertion      : 0.00
% 5.26/1.98  Index Deletion       : 0.00
% 5.26/1.98  Index Matching       : 0.00
% 5.26/1.98  BG Taut test         : 0.00
%------------------------------------------------------------------------------
