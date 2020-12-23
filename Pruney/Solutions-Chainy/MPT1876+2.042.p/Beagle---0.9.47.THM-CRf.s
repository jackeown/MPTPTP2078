%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:56 EST 2020

% Result     : Theorem 7.79s
% Output     : CNFRefutation 7.79s
% Verified   : 
% Statistics : Number of formulae       :  174 ( 885 expanded)
%              Number of leaves         :   42 ( 319 expanded)
%              Depth                    :   22
%              Number of atoms          :  447 (2613 expanded)
%              Number of equality atoms :   18 (  71 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v7_struct_0 > v2_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_zfmisc_1 > v1_xboole_0 > v1_tdlat_3 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k6_domain_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(v7_struct_0,type,(
    v7_struct_0: $i > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(v1_tdlat_3,type,(
    v1_tdlat_3: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(v2_tdlat_3,type,(
    v2_tdlat_3: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_190,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & v2_tdlat_3(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v1_xboole_0(B)
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
           => ( v2_tex_2(B,A)
            <=> v1_zfmisc_1(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tex_2)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_41,axiom,(
    ! [A] : ~ v1_xboole_0(k1_tarski(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_xboole_0)).

tff(f_58,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(k1_tarski(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_subset_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_129,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v1_zfmisc_1(B) )
         => ( r1_tarski(A,B)
           => A = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_54,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_86,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_170,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => v2_tex_2(k6_domain_1(u1_struct_0(A),B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_tex_2)).

tff(f_158,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
         => ~ ( v2_tex_2(B,A)
              & ! [C] :
                  ( ( ~ v2_struct_0(C)
                    & v1_pre_topc(C)
                    & v1_tdlat_3(C)
                    & m1_pre_topc(C,A) )
                 => B != u1_struct_0(C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_tex_2)).

tff(f_73,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_66,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_116,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & v2_tdlat_3(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ( ( ~ v2_struct_0(B)
              & ~ v7_struct_0(B) )
           => ( ~ v2_struct_0(B)
              & ~ v1_tdlat_3(B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc32_tex_2)).

tff(f_79,axiom,(
    ! [A] :
      ( ( v7_struct_0(A)
        & l1_struct_0(A) )
     => v1_zfmisc_1(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_struct_0)).

tff(c_60,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_66,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_58,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_64,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_74,plain,
    ( v2_tex_2('#skF_5','#skF_4')
    | v1_zfmisc_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_77,plain,(
    v1_zfmisc_1('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_74])).

tff(c_68,plain,
    ( ~ v1_zfmisc_1('#skF_5')
    | ~ v2_tex_2('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_80,plain,(
    ~ v2_tex_2('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_68])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_12,plain,(
    ! [A_10] : ~ v1_xboole_0(k1_tarski(A_10)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_172,plain,(
    ! [A_70,B_71] :
      ( m1_subset_1(k1_tarski(A_70),k1_zfmisc_1(B_71))
      | ~ r2_hidden(A_70,B_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_24,plain,(
    ! [A_15,B_16] :
      ( r1_tarski(A_15,B_16)
      | ~ m1_subset_1(A_15,k1_zfmisc_1(B_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_182,plain,(
    ! [A_70,B_71] :
      ( r1_tarski(k1_tarski(A_70),B_71)
      | ~ r2_hidden(A_70,B_71) ) ),
    inference(resolution,[status(thm)],[c_172,c_24])).

tff(c_301,plain,(
    ! [B_94,A_95] :
      ( B_94 = A_95
      | ~ r1_tarski(A_95,B_94)
      | ~ v1_zfmisc_1(B_94)
      | v1_xboole_0(B_94)
      | v1_xboole_0(A_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_307,plain,(
    ! [A_70,B_71] :
      ( k1_tarski(A_70) = B_71
      | ~ v1_zfmisc_1(B_71)
      | v1_xboole_0(B_71)
      | v1_xboole_0(k1_tarski(A_70))
      | ~ r2_hidden(A_70,B_71) ) ),
    inference(resolution,[status(thm)],[c_182,c_301])).

tff(c_333,plain,(
    ! [A_96,B_97] :
      ( k1_tarski(A_96) = B_97
      | ~ v1_zfmisc_1(B_97)
      | v1_xboole_0(B_97)
      | ~ r2_hidden(A_96,B_97) ) ),
    inference(negUnitSimplification,[status(thm)],[c_12,c_307])).

tff(c_349,plain,(
    ! [A_1] :
      ( k1_tarski('#skF_1'(A_1)) = A_1
      | ~ v1_zfmisc_1(A_1)
      | v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_4,c_333])).

tff(c_146,plain,(
    ! [A_64,B_65] :
      ( r2_hidden('#skF_2'(A_64,B_65),A_64)
      | r1_tarski(A_64,B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( ~ r2_hidden('#skF_2'(A_5,B_6),B_6)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_158,plain,(
    ! [A_64] : r1_tarski(A_64,A_64) ),
    inference(resolution,[status(thm)],[c_146,c_8])).

tff(c_56,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_93,plain,(
    ! [A_47,B_48] :
      ( r1_tarski(A_47,B_48)
      | ~ m1_subset_1(A_47,k1_zfmisc_1(B_48)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_97,plain,(
    r1_tarski('#skF_5',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_56,c_93])).

tff(c_187,plain,(
    ! [C_79,B_80,A_81] :
      ( r2_hidden(C_79,B_80)
      | ~ r2_hidden(C_79,A_81)
      | ~ r1_tarski(A_81,B_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_197,plain,(
    ! [A_82,B_83] :
      ( r2_hidden('#skF_1'(A_82),B_83)
      | ~ r1_tarski(A_82,B_83)
      | v1_xboole_0(A_82) ) ),
    inference(resolution,[status(thm)],[c_4,c_187])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_209,plain,(
    ! [B_84,A_85] :
      ( ~ v1_xboole_0(B_84)
      | ~ r1_tarski(A_85,B_84)
      | v1_xboole_0(A_85) ) ),
    inference(resolution,[status(thm)],[c_197,c_2])).

tff(c_224,plain,
    ( ~ v1_xboole_0(u1_struct_0('#skF_4'))
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_97,c_209])).

tff(c_232,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_224])).

tff(c_137,plain,(
    ! [B_62,A_63] :
      ( m1_subset_1(B_62,A_63)
      | ~ r2_hidden(B_62,A_63)
      | v1_xboole_0(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_145,plain,(
    ! [A_1] :
      ( m1_subset_1('#skF_1'(A_1),A_1)
      | v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_4,c_137])).

tff(c_16,plain,(
    ! [B_12,A_11] :
      ( r2_hidden(B_12,A_11)
      | ~ m1_subset_1(B_12,A_11)
      | v1_xboole_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_450,plain,(
    ! [B_113,B_114,A_115] :
      ( r2_hidden(B_113,B_114)
      | ~ r1_tarski(A_115,B_114)
      | ~ m1_subset_1(B_113,A_115)
      | v1_xboole_0(A_115) ) ),
    inference(resolution,[status(thm)],[c_16,c_187])).

tff(c_456,plain,(
    ! [B_113,B_71,A_70] :
      ( r2_hidden(B_113,B_71)
      | ~ m1_subset_1(B_113,k1_tarski(A_70))
      | v1_xboole_0(k1_tarski(A_70))
      | ~ r2_hidden(A_70,B_71) ) ),
    inference(resolution,[status(thm)],[c_182,c_450])).

tff(c_547,plain,(
    ! [B_119,B_120,A_121] :
      ( r2_hidden(B_119,B_120)
      | ~ m1_subset_1(B_119,k1_tarski(A_121))
      | ~ r2_hidden(A_121,B_120) ) ),
    inference(negUnitSimplification,[status(thm)],[c_12,c_456])).

tff(c_555,plain,(
    ! [A_121,B_120] :
      ( r2_hidden('#skF_1'(k1_tarski(A_121)),B_120)
      | ~ r2_hidden(A_121,B_120)
      | v1_xboole_0(k1_tarski(A_121)) ) ),
    inference(resolution,[status(thm)],[c_145,c_547])).

tff(c_601,plain,(
    ! [A_124,B_125] :
      ( r2_hidden('#skF_1'(k1_tarski(A_124)),B_125)
      | ~ r2_hidden(A_124,B_125) ) ),
    inference(negUnitSimplification,[status(thm)],[c_12,c_555])).

tff(c_320,plain,(
    ! [A_70,B_71] :
      ( k1_tarski(A_70) = B_71
      | ~ v1_zfmisc_1(B_71)
      | v1_xboole_0(B_71)
      | ~ r2_hidden(A_70,B_71) ) ),
    inference(negUnitSimplification,[status(thm)],[c_12,c_307])).

tff(c_1456,plain,(
    ! [A_173,B_174] :
      ( k1_tarski('#skF_1'(k1_tarski(A_173))) = B_174
      | ~ v1_zfmisc_1(B_174)
      | v1_xboole_0(B_174)
      | ~ r2_hidden(A_173,B_174) ) ),
    inference(resolution,[status(thm)],[c_601,c_320])).

tff(c_1486,plain,(
    ! [A_1] :
      ( k1_tarski('#skF_1'(k1_tarski('#skF_1'(A_1)))) = A_1
      | ~ v1_zfmisc_1(A_1)
      | v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_4,c_1456])).

tff(c_14,plain,(
    ! [B_12,A_11] :
      ( m1_subset_1(B_12,A_11)
      | ~ r2_hidden(B_12,A_11)
      | v1_xboole_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_677,plain,(
    ! [A_132,B_133] :
      ( m1_subset_1('#skF_1'(A_132),B_133)
      | v1_xboole_0(B_133)
      | ~ r1_tarski(A_132,B_133)
      | v1_xboole_0(A_132) ) ),
    inference(resolution,[status(thm)],[c_197,c_14])).

tff(c_467,plain,(
    ! [B_113,B_71,A_70] :
      ( r2_hidden(B_113,B_71)
      | ~ m1_subset_1(B_113,k1_tarski(A_70))
      | ~ r2_hidden(A_70,B_71) ) ),
    inference(negUnitSimplification,[status(thm)],[c_12,c_456])).

tff(c_684,plain,(
    ! [A_132,B_71,A_70] :
      ( r2_hidden('#skF_1'(A_132),B_71)
      | ~ r2_hidden(A_70,B_71)
      | v1_xboole_0(k1_tarski(A_70))
      | ~ r1_tarski(A_132,k1_tarski(A_70))
      | v1_xboole_0(A_132) ) ),
    inference(resolution,[status(thm)],[c_677,c_467])).

tff(c_3746,plain,(
    ! [A_259,B_260,A_261] :
      ( r2_hidden('#skF_1'(A_259),B_260)
      | ~ r2_hidden(A_261,B_260)
      | ~ r1_tarski(A_259,k1_tarski(A_261))
      | v1_xboole_0(A_259) ) ),
    inference(negUnitSimplification,[status(thm)],[c_12,c_684])).

tff(c_3842,plain,(
    ! [A_266,A_267] :
      ( r2_hidden('#skF_1'(A_266),A_267)
      | ~ r1_tarski(A_266,k1_tarski('#skF_1'(A_267)))
      | v1_xboole_0(A_266)
      | v1_xboole_0(A_267) ) ),
    inference(resolution,[status(thm)],[c_4,c_3746])).

tff(c_3884,plain,(
    ! [A_267] :
      ( r2_hidden('#skF_1'(k1_tarski('#skF_1'(A_267))),A_267)
      | v1_xboole_0(k1_tarski('#skF_1'(A_267)))
      | v1_xboole_0(A_267) ) ),
    inference(resolution,[status(thm)],[c_158,c_3842])).

tff(c_3974,plain,(
    ! [A_269] :
      ( r2_hidden('#skF_1'(k1_tarski('#skF_1'(A_269))),A_269)
      | v1_xboole_0(A_269) ) ),
    inference(negUnitSimplification,[status(thm)],[c_12,c_3884])).

tff(c_4030,plain,(
    ! [A_270] :
      ( m1_subset_1('#skF_1'(k1_tarski('#skF_1'(A_270))),A_270)
      | v1_xboole_0(A_270) ) ),
    inference(resolution,[status(thm)],[c_3974,c_14])).

tff(c_4084,plain,(
    ! [A_1] :
      ( m1_subset_1('#skF_1'(A_1),k1_tarski('#skF_1'(A_1)))
      | v1_xboole_0(k1_tarski('#skF_1'(A_1)))
      | ~ v1_zfmisc_1(A_1)
      | v1_xboole_0(A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1486,c_4030])).

tff(c_4110,plain,(
    ! [A_1] :
      ( m1_subset_1('#skF_1'(A_1),k1_tarski('#skF_1'(A_1)))
      | ~ v1_zfmisc_1(A_1)
      | v1_xboole_0(A_1) ) ),
    inference(negUnitSimplification,[status(thm)],[c_12,c_4084])).

tff(c_3898,plain,(
    ! [A_267] :
      ( r2_hidden('#skF_1'(k1_tarski('#skF_1'(A_267))),A_267)
      | v1_xboole_0(A_267) ) ),
    inference(negUnitSimplification,[status(thm)],[c_12,c_3884])).

tff(c_6,plain,(
    ! [C_9,B_6,A_5] :
      ( r2_hidden(C_9,B_6)
      | ~ r2_hidden(C_9,A_5)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_706,plain,(
    ! [A_134,B_135,B_136] :
      ( r2_hidden('#skF_1'(k1_tarski(A_134)),B_135)
      | ~ r1_tarski(B_136,B_135)
      | ~ r2_hidden(A_134,B_136) ) ),
    inference(resolution,[status(thm)],[c_601,c_6])).

tff(c_725,plain,(
    ! [A_137] :
      ( r2_hidden('#skF_1'(k1_tarski(A_137)),u1_struct_0('#skF_4'))
      | ~ r2_hidden(A_137,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_97,c_706])).

tff(c_7205,plain,(
    ! [A_340] :
      ( r2_hidden('#skF_1'(A_340),u1_struct_0('#skF_4'))
      | ~ r2_hidden('#skF_1'(A_340),'#skF_5')
      | ~ v1_zfmisc_1(A_340)
      | v1_xboole_0(A_340) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_349,c_725])).

tff(c_350,plain,(
    ! [A_98] :
      ( k1_tarski('#skF_1'(A_98)) = A_98
      | ~ v1_zfmisc_1(A_98)
      | v1_xboole_0(A_98) ) ),
    inference(resolution,[status(thm)],[c_4,c_333])).

tff(c_356,plain,(
    ! [A_98,B_71] :
      ( r1_tarski(A_98,B_71)
      | ~ r2_hidden('#skF_1'(A_98),B_71)
      | ~ v1_zfmisc_1(A_98)
      | v1_xboole_0(A_98) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_350,c_182])).

tff(c_7248,plain,(
    ! [A_341] :
      ( r1_tarski(A_341,u1_struct_0('#skF_4'))
      | ~ r2_hidden('#skF_1'(A_341),'#skF_5')
      | ~ v1_zfmisc_1(A_341)
      | v1_xboole_0(A_341) ) ),
    inference(resolution,[status(thm)],[c_7205,c_356])).

tff(c_7272,plain,
    ( r1_tarski(k1_tarski('#skF_1'('#skF_5')),u1_struct_0('#skF_4'))
    | ~ v1_zfmisc_1(k1_tarski('#skF_1'('#skF_5')))
    | v1_xboole_0(k1_tarski('#skF_1'('#skF_5')))
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_3898,c_7248])).

tff(c_7315,plain,
    ( r1_tarski(k1_tarski('#skF_1'('#skF_5')),u1_struct_0('#skF_4'))
    | ~ v1_zfmisc_1(k1_tarski('#skF_1'('#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_12,c_7272])).

tff(c_7409,plain,(
    ~ v1_zfmisc_1(k1_tarski('#skF_1'('#skF_5'))) ),
    inference(splitLeft,[status(thm)],[c_7315])).

tff(c_7412,plain,
    ( ~ v1_zfmisc_1('#skF_5')
    | ~ v1_zfmisc_1('#skF_5')
    | v1_xboole_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_349,c_7409])).

tff(c_7414,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_77,c_7412])).

tff(c_7416,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_7414])).

tff(c_7417,plain,(
    r1_tarski(k1_tarski('#skF_1'('#skF_5')),u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_7315])).

tff(c_195,plain,(
    ! [B_12,B_80,A_11] :
      ( r2_hidden(B_12,B_80)
      | ~ r1_tarski(A_11,B_80)
      | ~ m1_subset_1(B_12,A_11)
      | v1_xboole_0(A_11) ) ),
    inference(resolution,[status(thm)],[c_16,c_187])).

tff(c_7538,plain,(
    ! [B_12] :
      ( r2_hidden(B_12,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(B_12,k1_tarski('#skF_1'('#skF_5')))
      | v1_xboole_0(k1_tarski('#skF_1'('#skF_5'))) ) ),
    inference(resolution,[status(thm)],[c_7417,c_195])).

tff(c_7589,plain,(
    ! [B_346] :
      ( r2_hidden(B_346,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(B_346,k1_tarski('#skF_1'('#skF_5'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_12,c_7538])).

tff(c_7613,plain,
    ( r2_hidden('#skF_1'('#skF_5'),u1_struct_0('#skF_4'))
    | ~ v1_zfmisc_1('#skF_5')
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_4110,c_7589])).

tff(c_7673,plain,
    ( r2_hidden('#skF_1'('#skF_5'),u1_struct_0('#skF_4'))
    | v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_7613])).

tff(c_7674,plain,(
    r2_hidden('#skF_1'('#skF_5'),u1_struct_0('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_7673])).

tff(c_7726,plain,
    ( m1_subset_1('#skF_1'('#skF_5'),u1_struct_0('#skF_4'))
    | v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_7674,c_14])).

tff(c_7749,plain,(
    m1_subset_1('#skF_1'('#skF_5'),u1_struct_0('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_232,c_7726])).

tff(c_966,plain,(
    ! [A_148,B_149,B_150] :
      ( r2_hidden('#skF_1'(A_148),B_149)
      | ~ r1_tarski(B_150,B_149)
      | ~ r1_tarski(A_148,B_150)
      | v1_xboole_0(A_148) ) ),
    inference(resolution,[status(thm)],[c_197,c_6])).

tff(c_991,plain,(
    ! [A_151] :
      ( r2_hidden('#skF_1'(A_151),u1_struct_0('#skF_4'))
      | ~ r1_tarski(A_151,'#skF_5')
      | v1_xboole_0(A_151) ) ),
    inference(resolution,[status(thm)],[c_97,c_966])).

tff(c_1002,plain,(
    ! [A_151] :
      ( m1_subset_1('#skF_1'(A_151),u1_struct_0('#skF_4'))
      | v1_xboole_0(u1_struct_0('#skF_4'))
      | ~ r1_tarski(A_151,'#skF_5')
      | v1_xboole_0(A_151) ) ),
    inference(resolution,[status(thm)],[c_991,c_14])).

tff(c_1014,plain,(
    ! [A_152] :
      ( m1_subset_1('#skF_1'(A_152),u1_struct_0('#skF_4'))
      | ~ r1_tarski(A_152,'#skF_5')
      | v1_xboole_0(A_152) ) ),
    inference(negUnitSimplification,[status(thm)],[c_232,c_1002])).

tff(c_34,plain,(
    ! [A_22,B_23] :
      ( k6_domain_1(A_22,B_23) = k1_tarski(B_23)
      | ~ m1_subset_1(B_23,A_22)
      | v1_xboole_0(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_1020,plain,(
    ! [A_152] :
      ( k6_domain_1(u1_struct_0('#skF_4'),'#skF_1'(A_152)) = k1_tarski('#skF_1'(A_152))
      | v1_xboole_0(u1_struct_0('#skF_4'))
      | ~ r1_tarski(A_152,'#skF_5')
      | v1_xboole_0(A_152) ) ),
    inference(resolution,[status(thm)],[c_1014,c_34])).

tff(c_1182,plain,(
    ! [A_161] :
      ( k6_domain_1(u1_struct_0('#skF_4'),'#skF_1'(A_161)) = k1_tarski('#skF_1'(A_161))
      | ~ r1_tarski(A_161,'#skF_5')
      | v1_xboole_0(A_161) ) ),
    inference(negUnitSimplification,[status(thm)],[c_232,c_1020])).

tff(c_54,plain,(
    ! [A_37,B_39] :
      ( v2_tex_2(k6_domain_1(u1_struct_0(A_37),B_39),A_37)
      | ~ m1_subset_1(B_39,u1_struct_0(A_37))
      | ~ l1_pre_topc(A_37)
      | ~ v2_pre_topc(A_37)
      | v2_struct_0(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_1191,plain,(
    ! [A_161] :
      ( v2_tex_2(k1_tarski('#skF_1'(A_161)),'#skF_4')
      | ~ m1_subset_1('#skF_1'(A_161),u1_struct_0('#skF_4'))
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ r1_tarski(A_161,'#skF_5')
      | v1_xboole_0(A_161) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1182,c_54])).

tff(c_1209,plain,(
    ! [A_161] :
      ( v2_tex_2(k1_tarski('#skF_1'(A_161)),'#skF_4')
      | ~ m1_subset_1('#skF_1'(A_161),u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_4')
      | ~ r1_tarski(A_161,'#skF_5')
      | v1_xboole_0(A_161) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_60,c_1191])).

tff(c_1210,plain,(
    ! [A_161] :
      ( v2_tex_2(k1_tarski('#skF_1'(A_161)),'#skF_4')
      | ~ m1_subset_1('#skF_1'(A_161),u1_struct_0('#skF_4'))
      | ~ r1_tarski(A_161,'#skF_5')
      | v1_xboole_0(A_161) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_1209])).

tff(c_26,plain,(
    ! [A_15,B_16] :
      ( m1_subset_1(A_15,k1_zfmisc_1(B_16))
      | ~ r1_tarski(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_566,plain,(
    ! [A_122,B_123] :
      ( ~ v2_struct_0('#skF_3'(A_122,B_123))
      | ~ v2_tex_2(B_123,A_122)
      | ~ m1_subset_1(B_123,k1_zfmisc_1(u1_struct_0(A_122)))
      | v1_xboole_0(B_123)
      | ~ l1_pre_topc(A_122)
      | ~ v2_pre_topc(A_122)
      | v2_struct_0(A_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_595,plain,(
    ! [A_122,A_15] :
      ( ~ v2_struct_0('#skF_3'(A_122,A_15))
      | ~ v2_tex_2(A_15,A_122)
      | v1_xboole_0(A_15)
      | ~ l1_pre_topc(A_122)
      | ~ v2_pre_topc(A_122)
      | v2_struct_0(A_122)
      | ~ r1_tarski(A_15,u1_struct_0(A_122)) ) ),
    inference(resolution,[status(thm)],[c_26,c_566])).

tff(c_7524,plain,
    ( ~ v2_struct_0('#skF_3'('#skF_4',k1_tarski('#skF_1'('#skF_5'))))
    | ~ v2_tex_2(k1_tarski('#skF_1'('#skF_5')),'#skF_4')
    | v1_xboole_0(k1_tarski('#skF_1'('#skF_5')))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_7417,c_595])).

tff(c_7564,plain,
    ( ~ v2_struct_0('#skF_3'('#skF_4',k1_tarski('#skF_1'('#skF_5'))))
    | ~ v2_tex_2(k1_tarski('#skF_1'('#skF_5')),'#skF_4')
    | v1_xboole_0(k1_tarski('#skF_1'('#skF_5')))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_60,c_7524])).

tff(c_7565,plain,
    ( ~ v2_struct_0('#skF_3'('#skF_4',k1_tarski('#skF_1'('#skF_5'))))
    | ~ v2_tex_2(k1_tarski('#skF_1'('#skF_5')),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_12,c_7564])).

tff(c_8019,plain,(
    ~ v2_tex_2(k1_tarski('#skF_1'('#skF_5')),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_7565])).

tff(c_8022,plain,
    ( ~ m1_subset_1('#skF_1'('#skF_5'),u1_struct_0('#skF_4'))
    | ~ r1_tarski('#skF_5','#skF_5')
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_1210,c_8019])).

tff(c_8031,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_158,c_7749,c_8022])).

tff(c_8033,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_8031])).

tff(c_8035,plain,(
    v2_tex_2(k1_tarski('#skF_1'('#skF_5')),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_7565])).

tff(c_8038,plain,
    ( v2_tex_2('#skF_5','#skF_4')
    | ~ v1_zfmisc_1('#skF_5')
    | v1_xboole_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_349,c_8035])).

tff(c_8040,plain,
    ( v2_tex_2('#skF_5','#skF_4')
    | v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_8038])).

tff(c_8042,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_80,c_8040])).

tff(c_8043,plain,(
    v2_tex_2('#skF_5','#skF_4') ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_9402,plain,(
    ! [A_481,B_482] :
      ( m1_pre_topc('#skF_3'(A_481,B_482),A_481)
      | ~ v2_tex_2(B_482,A_481)
      | ~ m1_subset_1(B_482,k1_zfmisc_1(u1_struct_0(A_481)))
      | v1_xboole_0(B_482)
      | ~ l1_pre_topc(A_481)
      | ~ v2_pre_topc(A_481)
      | v2_struct_0(A_481) ) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_9428,plain,
    ( m1_pre_topc('#skF_3'('#skF_4','#skF_5'),'#skF_4')
    | ~ v2_tex_2('#skF_5','#skF_4')
    | v1_xboole_0('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_9402])).

tff(c_9441,plain,
    ( m1_pre_topc('#skF_3'('#skF_4','#skF_5'),'#skF_4')
    | v1_xboole_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_60,c_8043,c_9428])).

tff(c_9442,plain,(
    m1_pre_topc('#skF_3'('#skF_4','#skF_5'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_58,c_9441])).

tff(c_30,plain,(
    ! [B_20,A_18] :
      ( l1_pre_topc(B_20)
      | ~ m1_pre_topc(B_20,A_18)
      | ~ l1_pre_topc(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_9448,plain,
    ( l1_pre_topc('#skF_3'('#skF_4','#skF_5'))
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_9442,c_30])).

tff(c_9455,plain,(
    l1_pre_topc('#skF_3'('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_9448])).

tff(c_28,plain,(
    ! [A_17] :
      ( l1_struct_0(A_17)
      | ~ l1_pre_topc(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_8044,plain,(
    ~ v1_zfmisc_1('#skF_5') ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_9036,plain,(
    ! [A_464,B_465] :
      ( ~ v2_struct_0('#skF_3'(A_464,B_465))
      | ~ v2_tex_2(B_465,A_464)
      | ~ m1_subset_1(B_465,k1_zfmisc_1(u1_struct_0(A_464)))
      | v1_xboole_0(B_465)
      | ~ l1_pre_topc(A_464)
      | ~ v2_pre_topc(A_464)
      | v2_struct_0(A_464) ) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_9067,plain,
    ( ~ v2_struct_0('#skF_3'('#skF_4','#skF_5'))
    | ~ v2_tex_2('#skF_5','#skF_4')
    | v1_xboole_0('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_9036])).

tff(c_9079,plain,
    ( ~ v2_struct_0('#skF_3'('#skF_4','#skF_5'))
    | v1_xboole_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_60,c_8043,c_9067])).

tff(c_9080,plain,(
    ~ v2_struct_0('#skF_3'('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_58,c_9079])).

tff(c_62,plain,(
    v2_tdlat_3('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_8824,plain,(
    ! [A_451,B_452] :
      ( v1_tdlat_3('#skF_3'(A_451,B_452))
      | ~ v2_tex_2(B_452,A_451)
      | ~ m1_subset_1(B_452,k1_zfmisc_1(u1_struct_0(A_451)))
      | v1_xboole_0(B_452)
      | ~ l1_pre_topc(A_451)
      | ~ v2_pre_topc(A_451)
      | v2_struct_0(A_451) ) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_8855,plain,
    ( v1_tdlat_3('#skF_3'('#skF_4','#skF_5'))
    | ~ v2_tex_2('#skF_5','#skF_4')
    | v1_xboole_0('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_8824])).

tff(c_8867,plain,
    ( v1_tdlat_3('#skF_3'('#skF_4','#skF_5'))
    | v1_xboole_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_60,c_8043,c_8855])).

tff(c_8868,plain,(
    v1_tdlat_3('#skF_3'('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_58,c_8867])).

tff(c_38,plain,(
    ! [B_27,A_25] :
      ( ~ v1_tdlat_3(B_27)
      | v7_struct_0(B_27)
      | v2_struct_0(B_27)
      | ~ m1_pre_topc(B_27,A_25)
      | ~ l1_pre_topc(A_25)
      | ~ v2_tdlat_3(A_25)
      | ~ v2_pre_topc(A_25)
      | v2_struct_0(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_9445,plain,
    ( ~ v1_tdlat_3('#skF_3'('#skF_4','#skF_5'))
    | v7_struct_0('#skF_3'('#skF_4','#skF_5'))
    | v2_struct_0('#skF_3'('#skF_4','#skF_5'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_tdlat_3('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_9442,c_38])).

tff(c_9451,plain,
    ( v7_struct_0('#skF_3'('#skF_4','#skF_5'))
    | v2_struct_0('#skF_3'('#skF_4','#skF_5'))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_60,c_8868,c_9445])).

tff(c_9452,plain,(
    v7_struct_0('#skF_3'('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_9080,c_9451])).

tff(c_9661,plain,(
    ! [A_489,B_490] :
      ( u1_struct_0('#skF_3'(A_489,B_490)) = B_490
      | ~ v2_tex_2(B_490,A_489)
      | ~ m1_subset_1(B_490,k1_zfmisc_1(u1_struct_0(A_489)))
      | v1_xboole_0(B_490)
      | ~ l1_pre_topc(A_489)
      | ~ v2_pre_topc(A_489)
      | v2_struct_0(A_489) ) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_9702,plain,
    ( u1_struct_0('#skF_3'('#skF_4','#skF_5')) = '#skF_5'
    | ~ v2_tex_2('#skF_5','#skF_4')
    | v1_xboole_0('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_9661])).

tff(c_9723,plain,
    ( u1_struct_0('#skF_3'('#skF_4','#skF_5')) = '#skF_5'
    | v1_xboole_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_60,c_8043,c_9702])).

tff(c_9724,plain,(
    u1_struct_0('#skF_3'('#skF_4','#skF_5')) = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_58,c_9723])).

tff(c_32,plain,(
    ! [A_21] :
      ( v1_zfmisc_1(u1_struct_0(A_21))
      | ~ l1_struct_0(A_21)
      | ~ v7_struct_0(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_9745,plain,
    ( v1_zfmisc_1('#skF_5')
    | ~ l1_struct_0('#skF_3'('#skF_4','#skF_5'))
    | ~ v7_struct_0('#skF_3'('#skF_4','#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_9724,c_32])).

tff(c_9767,plain,
    ( v1_zfmisc_1('#skF_5')
    | ~ l1_struct_0('#skF_3'('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9452,c_9745])).

tff(c_9768,plain,(
    ~ l1_struct_0('#skF_3'('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_8044,c_9767])).

tff(c_9772,plain,(
    ~ l1_pre_topc('#skF_3'('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_28,c_9768])).

tff(c_9776,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_9455,c_9772])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:29:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.79/2.75  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.79/2.76  
% 7.79/2.76  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.79/2.77  %$ v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v7_struct_0 > v2_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_zfmisc_1 > v1_xboole_0 > v1_tdlat_3 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k6_domain_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2
% 7.79/2.77  
% 7.79/2.77  %Foreground sorts:
% 7.79/2.77  
% 7.79/2.77  
% 7.79/2.77  %Background operators:
% 7.79/2.77  
% 7.79/2.77  
% 7.79/2.77  %Foreground operators:
% 7.79/2.77  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 7.79/2.77  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.79/2.77  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.79/2.77  tff(k1_tarski, type, k1_tarski: $i > $i).
% 7.79/2.77  tff('#skF_1', type, '#skF_1': $i > $i).
% 7.79/2.77  tff(v7_struct_0, type, v7_struct_0: $i > $o).
% 7.79/2.77  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 7.79/2.77  tff(v1_tdlat_3, type, v1_tdlat_3: $i > $o).
% 7.79/2.77  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 7.79/2.77  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 7.79/2.77  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.79/2.77  tff('#skF_5', type, '#skF_5': $i).
% 7.79/2.77  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 7.79/2.77  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 7.79/2.77  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.79/2.77  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 7.79/2.77  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.79/2.77  tff('#skF_4', type, '#skF_4': $i).
% 7.79/2.77  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.79/2.77  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 7.79/2.77  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 7.79/2.77  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 7.79/2.77  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 7.79/2.77  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 7.79/2.77  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 7.79/2.77  tff(v2_tdlat_3, type, v2_tdlat_3: $i > $o).
% 7.79/2.77  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.79/2.77  
% 7.79/2.79  tff(f_190, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v2_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v2_tex_2(B, A) <=> v1_zfmisc_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tex_2)).
% 7.79/2.79  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 7.79/2.79  tff(f_41, axiom, (![A]: ~v1_xboole_0(k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_xboole_0)).
% 7.79/2.79  tff(f_58, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(k1_tarski(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_subset_1)).
% 7.79/2.79  tff(f_62, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 7.79/2.79  tff(f_129, axiom, (![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tex_2)).
% 7.79/2.79  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 7.79/2.79  tff(f_54, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 7.79/2.79  tff(f_86, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 7.79/2.79  tff(f_170, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => v2_tex_2(k6_domain_1(u1_struct_0(A), B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_tex_2)).
% 7.79/2.79  tff(f_158, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ~(v2_tex_2(B, A) & (![C]: ((((~v2_struct_0(C) & v1_pre_topc(C)) & v1_tdlat_3(C)) & m1_pre_topc(C, A)) => ~(B = u1_struct_0(C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_tex_2)).
% 7.79/2.79  tff(f_73, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 7.79/2.79  tff(f_66, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 7.79/2.79  tff(f_116, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v2_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => ((~v2_struct_0(B) & ~v7_struct_0(B)) => (~v2_struct_0(B) & ~v1_tdlat_3(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc32_tex_2)).
% 7.79/2.79  tff(f_79, axiom, (![A]: ((v7_struct_0(A) & l1_struct_0(A)) => v1_zfmisc_1(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc7_struct_0)).
% 7.79/2.79  tff(c_60, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_190])).
% 7.79/2.79  tff(c_66, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_190])).
% 7.79/2.79  tff(c_58, plain, (~v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_190])).
% 7.79/2.79  tff(c_64, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_190])).
% 7.79/2.79  tff(c_74, plain, (v2_tex_2('#skF_5', '#skF_4') | v1_zfmisc_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_190])).
% 7.79/2.79  tff(c_77, plain, (v1_zfmisc_1('#skF_5')), inference(splitLeft, [status(thm)], [c_74])).
% 7.79/2.79  tff(c_68, plain, (~v1_zfmisc_1('#skF_5') | ~v2_tex_2('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_190])).
% 7.79/2.79  tff(c_80, plain, (~v2_tex_2('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_77, c_68])).
% 7.79/2.79  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.79/2.79  tff(c_12, plain, (![A_10]: (~v1_xboole_0(k1_tarski(A_10)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.79/2.79  tff(c_172, plain, (![A_70, B_71]: (m1_subset_1(k1_tarski(A_70), k1_zfmisc_1(B_71)) | ~r2_hidden(A_70, B_71))), inference(cnfTransformation, [status(thm)], [f_58])).
% 7.79/2.79  tff(c_24, plain, (![A_15, B_16]: (r1_tarski(A_15, B_16) | ~m1_subset_1(A_15, k1_zfmisc_1(B_16)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 7.79/2.79  tff(c_182, plain, (![A_70, B_71]: (r1_tarski(k1_tarski(A_70), B_71) | ~r2_hidden(A_70, B_71))), inference(resolution, [status(thm)], [c_172, c_24])).
% 7.79/2.79  tff(c_301, plain, (![B_94, A_95]: (B_94=A_95 | ~r1_tarski(A_95, B_94) | ~v1_zfmisc_1(B_94) | v1_xboole_0(B_94) | v1_xboole_0(A_95))), inference(cnfTransformation, [status(thm)], [f_129])).
% 7.79/2.79  tff(c_307, plain, (![A_70, B_71]: (k1_tarski(A_70)=B_71 | ~v1_zfmisc_1(B_71) | v1_xboole_0(B_71) | v1_xboole_0(k1_tarski(A_70)) | ~r2_hidden(A_70, B_71))), inference(resolution, [status(thm)], [c_182, c_301])).
% 7.79/2.79  tff(c_333, plain, (![A_96, B_97]: (k1_tarski(A_96)=B_97 | ~v1_zfmisc_1(B_97) | v1_xboole_0(B_97) | ~r2_hidden(A_96, B_97))), inference(negUnitSimplification, [status(thm)], [c_12, c_307])).
% 7.79/2.79  tff(c_349, plain, (![A_1]: (k1_tarski('#skF_1'(A_1))=A_1 | ~v1_zfmisc_1(A_1) | v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_4, c_333])).
% 7.79/2.79  tff(c_146, plain, (![A_64, B_65]: (r2_hidden('#skF_2'(A_64, B_65), A_64) | r1_tarski(A_64, B_65))), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.79/2.79  tff(c_8, plain, (![A_5, B_6]: (~r2_hidden('#skF_2'(A_5, B_6), B_6) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.79/2.79  tff(c_158, plain, (![A_64]: (r1_tarski(A_64, A_64))), inference(resolution, [status(thm)], [c_146, c_8])).
% 7.79/2.79  tff(c_56, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_190])).
% 7.79/2.79  tff(c_93, plain, (![A_47, B_48]: (r1_tarski(A_47, B_48) | ~m1_subset_1(A_47, k1_zfmisc_1(B_48)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 7.79/2.79  tff(c_97, plain, (r1_tarski('#skF_5', u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_56, c_93])).
% 7.79/2.79  tff(c_187, plain, (![C_79, B_80, A_81]: (r2_hidden(C_79, B_80) | ~r2_hidden(C_79, A_81) | ~r1_tarski(A_81, B_80))), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.79/2.79  tff(c_197, plain, (![A_82, B_83]: (r2_hidden('#skF_1'(A_82), B_83) | ~r1_tarski(A_82, B_83) | v1_xboole_0(A_82))), inference(resolution, [status(thm)], [c_4, c_187])).
% 7.79/2.79  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.79/2.79  tff(c_209, plain, (![B_84, A_85]: (~v1_xboole_0(B_84) | ~r1_tarski(A_85, B_84) | v1_xboole_0(A_85))), inference(resolution, [status(thm)], [c_197, c_2])).
% 7.79/2.79  tff(c_224, plain, (~v1_xboole_0(u1_struct_0('#skF_4')) | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_97, c_209])).
% 7.79/2.79  tff(c_232, plain, (~v1_xboole_0(u1_struct_0('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_58, c_224])).
% 7.79/2.79  tff(c_137, plain, (![B_62, A_63]: (m1_subset_1(B_62, A_63) | ~r2_hidden(B_62, A_63) | v1_xboole_0(A_63))), inference(cnfTransformation, [status(thm)], [f_54])).
% 7.79/2.79  tff(c_145, plain, (![A_1]: (m1_subset_1('#skF_1'(A_1), A_1) | v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_4, c_137])).
% 7.79/2.79  tff(c_16, plain, (![B_12, A_11]: (r2_hidden(B_12, A_11) | ~m1_subset_1(B_12, A_11) | v1_xboole_0(A_11))), inference(cnfTransformation, [status(thm)], [f_54])).
% 7.79/2.79  tff(c_450, plain, (![B_113, B_114, A_115]: (r2_hidden(B_113, B_114) | ~r1_tarski(A_115, B_114) | ~m1_subset_1(B_113, A_115) | v1_xboole_0(A_115))), inference(resolution, [status(thm)], [c_16, c_187])).
% 7.79/2.79  tff(c_456, plain, (![B_113, B_71, A_70]: (r2_hidden(B_113, B_71) | ~m1_subset_1(B_113, k1_tarski(A_70)) | v1_xboole_0(k1_tarski(A_70)) | ~r2_hidden(A_70, B_71))), inference(resolution, [status(thm)], [c_182, c_450])).
% 7.79/2.79  tff(c_547, plain, (![B_119, B_120, A_121]: (r2_hidden(B_119, B_120) | ~m1_subset_1(B_119, k1_tarski(A_121)) | ~r2_hidden(A_121, B_120))), inference(negUnitSimplification, [status(thm)], [c_12, c_456])).
% 7.79/2.79  tff(c_555, plain, (![A_121, B_120]: (r2_hidden('#skF_1'(k1_tarski(A_121)), B_120) | ~r2_hidden(A_121, B_120) | v1_xboole_0(k1_tarski(A_121)))), inference(resolution, [status(thm)], [c_145, c_547])).
% 7.79/2.79  tff(c_601, plain, (![A_124, B_125]: (r2_hidden('#skF_1'(k1_tarski(A_124)), B_125) | ~r2_hidden(A_124, B_125))), inference(negUnitSimplification, [status(thm)], [c_12, c_555])).
% 7.79/2.79  tff(c_320, plain, (![A_70, B_71]: (k1_tarski(A_70)=B_71 | ~v1_zfmisc_1(B_71) | v1_xboole_0(B_71) | ~r2_hidden(A_70, B_71))), inference(negUnitSimplification, [status(thm)], [c_12, c_307])).
% 7.79/2.79  tff(c_1456, plain, (![A_173, B_174]: (k1_tarski('#skF_1'(k1_tarski(A_173)))=B_174 | ~v1_zfmisc_1(B_174) | v1_xboole_0(B_174) | ~r2_hidden(A_173, B_174))), inference(resolution, [status(thm)], [c_601, c_320])).
% 7.79/2.79  tff(c_1486, plain, (![A_1]: (k1_tarski('#skF_1'(k1_tarski('#skF_1'(A_1))))=A_1 | ~v1_zfmisc_1(A_1) | v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_4, c_1456])).
% 7.79/2.79  tff(c_14, plain, (![B_12, A_11]: (m1_subset_1(B_12, A_11) | ~r2_hidden(B_12, A_11) | v1_xboole_0(A_11))), inference(cnfTransformation, [status(thm)], [f_54])).
% 7.79/2.79  tff(c_677, plain, (![A_132, B_133]: (m1_subset_1('#skF_1'(A_132), B_133) | v1_xboole_0(B_133) | ~r1_tarski(A_132, B_133) | v1_xboole_0(A_132))), inference(resolution, [status(thm)], [c_197, c_14])).
% 7.79/2.79  tff(c_467, plain, (![B_113, B_71, A_70]: (r2_hidden(B_113, B_71) | ~m1_subset_1(B_113, k1_tarski(A_70)) | ~r2_hidden(A_70, B_71))), inference(negUnitSimplification, [status(thm)], [c_12, c_456])).
% 7.79/2.79  tff(c_684, plain, (![A_132, B_71, A_70]: (r2_hidden('#skF_1'(A_132), B_71) | ~r2_hidden(A_70, B_71) | v1_xboole_0(k1_tarski(A_70)) | ~r1_tarski(A_132, k1_tarski(A_70)) | v1_xboole_0(A_132))), inference(resolution, [status(thm)], [c_677, c_467])).
% 7.79/2.79  tff(c_3746, plain, (![A_259, B_260, A_261]: (r2_hidden('#skF_1'(A_259), B_260) | ~r2_hidden(A_261, B_260) | ~r1_tarski(A_259, k1_tarski(A_261)) | v1_xboole_0(A_259))), inference(negUnitSimplification, [status(thm)], [c_12, c_684])).
% 7.79/2.79  tff(c_3842, plain, (![A_266, A_267]: (r2_hidden('#skF_1'(A_266), A_267) | ~r1_tarski(A_266, k1_tarski('#skF_1'(A_267))) | v1_xboole_0(A_266) | v1_xboole_0(A_267))), inference(resolution, [status(thm)], [c_4, c_3746])).
% 7.79/2.79  tff(c_3884, plain, (![A_267]: (r2_hidden('#skF_1'(k1_tarski('#skF_1'(A_267))), A_267) | v1_xboole_0(k1_tarski('#skF_1'(A_267))) | v1_xboole_0(A_267))), inference(resolution, [status(thm)], [c_158, c_3842])).
% 7.79/2.79  tff(c_3974, plain, (![A_269]: (r2_hidden('#skF_1'(k1_tarski('#skF_1'(A_269))), A_269) | v1_xboole_0(A_269))), inference(negUnitSimplification, [status(thm)], [c_12, c_3884])).
% 7.79/2.79  tff(c_4030, plain, (![A_270]: (m1_subset_1('#skF_1'(k1_tarski('#skF_1'(A_270))), A_270) | v1_xboole_0(A_270))), inference(resolution, [status(thm)], [c_3974, c_14])).
% 7.79/2.79  tff(c_4084, plain, (![A_1]: (m1_subset_1('#skF_1'(A_1), k1_tarski('#skF_1'(A_1))) | v1_xboole_0(k1_tarski('#skF_1'(A_1))) | ~v1_zfmisc_1(A_1) | v1_xboole_0(A_1))), inference(superposition, [status(thm), theory('equality')], [c_1486, c_4030])).
% 7.79/2.79  tff(c_4110, plain, (![A_1]: (m1_subset_1('#skF_1'(A_1), k1_tarski('#skF_1'(A_1))) | ~v1_zfmisc_1(A_1) | v1_xboole_0(A_1))), inference(negUnitSimplification, [status(thm)], [c_12, c_4084])).
% 7.79/2.79  tff(c_3898, plain, (![A_267]: (r2_hidden('#skF_1'(k1_tarski('#skF_1'(A_267))), A_267) | v1_xboole_0(A_267))), inference(negUnitSimplification, [status(thm)], [c_12, c_3884])).
% 7.79/2.79  tff(c_6, plain, (![C_9, B_6, A_5]: (r2_hidden(C_9, B_6) | ~r2_hidden(C_9, A_5) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.79/2.79  tff(c_706, plain, (![A_134, B_135, B_136]: (r2_hidden('#skF_1'(k1_tarski(A_134)), B_135) | ~r1_tarski(B_136, B_135) | ~r2_hidden(A_134, B_136))), inference(resolution, [status(thm)], [c_601, c_6])).
% 7.79/2.79  tff(c_725, plain, (![A_137]: (r2_hidden('#skF_1'(k1_tarski(A_137)), u1_struct_0('#skF_4')) | ~r2_hidden(A_137, '#skF_5'))), inference(resolution, [status(thm)], [c_97, c_706])).
% 7.79/2.79  tff(c_7205, plain, (![A_340]: (r2_hidden('#skF_1'(A_340), u1_struct_0('#skF_4')) | ~r2_hidden('#skF_1'(A_340), '#skF_5') | ~v1_zfmisc_1(A_340) | v1_xboole_0(A_340))), inference(superposition, [status(thm), theory('equality')], [c_349, c_725])).
% 7.79/2.79  tff(c_350, plain, (![A_98]: (k1_tarski('#skF_1'(A_98))=A_98 | ~v1_zfmisc_1(A_98) | v1_xboole_0(A_98))), inference(resolution, [status(thm)], [c_4, c_333])).
% 7.79/2.79  tff(c_356, plain, (![A_98, B_71]: (r1_tarski(A_98, B_71) | ~r2_hidden('#skF_1'(A_98), B_71) | ~v1_zfmisc_1(A_98) | v1_xboole_0(A_98))), inference(superposition, [status(thm), theory('equality')], [c_350, c_182])).
% 7.79/2.79  tff(c_7248, plain, (![A_341]: (r1_tarski(A_341, u1_struct_0('#skF_4')) | ~r2_hidden('#skF_1'(A_341), '#skF_5') | ~v1_zfmisc_1(A_341) | v1_xboole_0(A_341))), inference(resolution, [status(thm)], [c_7205, c_356])).
% 7.79/2.79  tff(c_7272, plain, (r1_tarski(k1_tarski('#skF_1'('#skF_5')), u1_struct_0('#skF_4')) | ~v1_zfmisc_1(k1_tarski('#skF_1'('#skF_5'))) | v1_xboole_0(k1_tarski('#skF_1'('#skF_5'))) | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_3898, c_7248])).
% 7.79/2.79  tff(c_7315, plain, (r1_tarski(k1_tarski('#skF_1'('#skF_5')), u1_struct_0('#skF_4')) | ~v1_zfmisc_1(k1_tarski('#skF_1'('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_58, c_12, c_7272])).
% 7.79/2.79  tff(c_7409, plain, (~v1_zfmisc_1(k1_tarski('#skF_1'('#skF_5')))), inference(splitLeft, [status(thm)], [c_7315])).
% 7.79/2.79  tff(c_7412, plain, (~v1_zfmisc_1('#skF_5') | ~v1_zfmisc_1('#skF_5') | v1_xboole_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_349, c_7409])).
% 7.79/2.79  tff(c_7414, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_77, c_77, c_7412])).
% 7.79/2.79  tff(c_7416, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_7414])).
% 7.79/2.79  tff(c_7417, plain, (r1_tarski(k1_tarski('#skF_1'('#skF_5')), u1_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_7315])).
% 7.79/2.79  tff(c_195, plain, (![B_12, B_80, A_11]: (r2_hidden(B_12, B_80) | ~r1_tarski(A_11, B_80) | ~m1_subset_1(B_12, A_11) | v1_xboole_0(A_11))), inference(resolution, [status(thm)], [c_16, c_187])).
% 7.79/2.79  tff(c_7538, plain, (![B_12]: (r2_hidden(B_12, u1_struct_0('#skF_4')) | ~m1_subset_1(B_12, k1_tarski('#skF_1'('#skF_5'))) | v1_xboole_0(k1_tarski('#skF_1'('#skF_5'))))), inference(resolution, [status(thm)], [c_7417, c_195])).
% 7.79/2.79  tff(c_7589, plain, (![B_346]: (r2_hidden(B_346, u1_struct_0('#skF_4')) | ~m1_subset_1(B_346, k1_tarski('#skF_1'('#skF_5'))))), inference(negUnitSimplification, [status(thm)], [c_12, c_7538])).
% 7.79/2.79  tff(c_7613, plain, (r2_hidden('#skF_1'('#skF_5'), u1_struct_0('#skF_4')) | ~v1_zfmisc_1('#skF_5') | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_4110, c_7589])).
% 7.79/2.79  tff(c_7673, plain, (r2_hidden('#skF_1'('#skF_5'), u1_struct_0('#skF_4')) | v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_77, c_7613])).
% 7.79/2.79  tff(c_7674, plain, (r2_hidden('#skF_1'('#skF_5'), u1_struct_0('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_58, c_7673])).
% 7.79/2.79  tff(c_7726, plain, (m1_subset_1('#skF_1'('#skF_5'), u1_struct_0('#skF_4')) | v1_xboole_0(u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_7674, c_14])).
% 7.79/2.79  tff(c_7749, plain, (m1_subset_1('#skF_1'('#skF_5'), u1_struct_0('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_232, c_7726])).
% 7.79/2.79  tff(c_966, plain, (![A_148, B_149, B_150]: (r2_hidden('#skF_1'(A_148), B_149) | ~r1_tarski(B_150, B_149) | ~r1_tarski(A_148, B_150) | v1_xboole_0(A_148))), inference(resolution, [status(thm)], [c_197, c_6])).
% 7.79/2.79  tff(c_991, plain, (![A_151]: (r2_hidden('#skF_1'(A_151), u1_struct_0('#skF_4')) | ~r1_tarski(A_151, '#skF_5') | v1_xboole_0(A_151))), inference(resolution, [status(thm)], [c_97, c_966])).
% 7.79/2.79  tff(c_1002, plain, (![A_151]: (m1_subset_1('#skF_1'(A_151), u1_struct_0('#skF_4')) | v1_xboole_0(u1_struct_0('#skF_4')) | ~r1_tarski(A_151, '#skF_5') | v1_xboole_0(A_151))), inference(resolution, [status(thm)], [c_991, c_14])).
% 7.79/2.79  tff(c_1014, plain, (![A_152]: (m1_subset_1('#skF_1'(A_152), u1_struct_0('#skF_4')) | ~r1_tarski(A_152, '#skF_5') | v1_xboole_0(A_152))), inference(negUnitSimplification, [status(thm)], [c_232, c_1002])).
% 7.79/2.79  tff(c_34, plain, (![A_22, B_23]: (k6_domain_1(A_22, B_23)=k1_tarski(B_23) | ~m1_subset_1(B_23, A_22) | v1_xboole_0(A_22))), inference(cnfTransformation, [status(thm)], [f_86])).
% 7.79/2.79  tff(c_1020, plain, (![A_152]: (k6_domain_1(u1_struct_0('#skF_4'), '#skF_1'(A_152))=k1_tarski('#skF_1'(A_152)) | v1_xboole_0(u1_struct_0('#skF_4')) | ~r1_tarski(A_152, '#skF_5') | v1_xboole_0(A_152))), inference(resolution, [status(thm)], [c_1014, c_34])).
% 7.79/2.79  tff(c_1182, plain, (![A_161]: (k6_domain_1(u1_struct_0('#skF_4'), '#skF_1'(A_161))=k1_tarski('#skF_1'(A_161)) | ~r1_tarski(A_161, '#skF_5') | v1_xboole_0(A_161))), inference(negUnitSimplification, [status(thm)], [c_232, c_1020])).
% 7.79/2.79  tff(c_54, plain, (![A_37, B_39]: (v2_tex_2(k6_domain_1(u1_struct_0(A_37), B_39), A_37) | ~m1_subset_1(B_39, u1_struct_0(A_37)) | ~l1_pre_topc(A_37) | ~v2_pre_topc(A_37) | v2_struct_0(A_37))), inference(cnfTransformation, [status(thm)], [f_170])).
% 7.79/2.79  tff(c_1191, plain, (![A_161]: (v2_tex_2(k1_tarski('#skF_1'(A_161)), '#skF_4') | ~m1_subset_1('#skF_1'(A_161), u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~r1_tarski(A_161, '#skF_5') | v1_xboole_0(A_161))), inference(superposition, [status(thm), theory('equality')], [c_1182, c_54])).
% 7.79/2.79  tff(c_1209, plain, (![A_161]: (v2_tex_2(k1_tarski('#skF_1'(A_161)), '#skF_4') | ~m1_subset_1('#skF_1'(A_161), u1_struct_0('#skF_4')) | v2_struct_0('#skF_4') | ~r1_tarski(A_161, '#skF_5') | v1_xboole_0(A_161))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_60, c_1191])).
% 7.79/2.79  tff(c_1210, plain, (![A_161]: (v2_tex_2(k1_tarski('#skF_1'(A_161)), '#skF_4') | ~m1_subset_1('#skF_1'(A_161), u1_struct_0('#skF_4')) | ~r1_tarski(A_161, '#skF_5') | v1_xboole_0(A_161))), inference(negUnitSimplification, [status(thm)], [c_66, c_1209])).
% 7.79/2.79  tff(c_26, plain, (![A_15, B_16]: (m1_subset_1(A_15, k1_zfmisc_1(B_16)) | ~r1_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_62])).
% 7.79/2.79  tff(c_566, plain, (![A_122, B_123]: (~v2_struct_0('#skF_3'(A_122, B_123)) | ~v2_tex_2(B_123, A_122) | ~m1_subset_1(B_123, k1_zfmisc_1(u1_struct_0(A_122))) | v1_xboole_0(B_123) | ~l1_pre_topc(A_122) | ~v2_pre_topc(A_122) | v2_struct_0(A_122))), inference(cnfTransformation, [status(thm)], [f_158])).
% 7.79/2.79  tff(c_595, plain, (![A_122, A_15]: (~v2_struct_0('#skF_3'(A_122, A_15)) | ~v2_tex_2(A_15, A_122) | v1_xboole_0(A_15) | ~l1_pre_topc(A_122) | ~v2_pre_topc(A_122) | v2_struct_0(A_122) | ~r1_tarski(A_15, u1_struct_0(A_122)))), inference(resolution, [status(thm)], [c_26, c_566])).
% 7.79/2.79  tff(c_7524, plain, (~v2_struct_0('#skF_3'('#skF_4', k1_tarski('#skF_1'('#skF_5')))) | ~v2_tex_2(k1_tarski('#skF_1'('#skF_5')), '#skF_4') | v1_xboole_0(k1_tarski('#skF_1'('#skF_5'))) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_7417, c_595])).
% 7.79/2.79  tff(c_7564, plain, (~v2_struct_0('#skF_3'('#skF_4', k1_tarski('#skF_1'('#skF_5')))) | ~v2_tex_2(k1_tarski('#skF_1'('#skF_5')), '#skF_4') | v1_xboole_0(k1_tarski('#skF_1'('#skF_5'))) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_60, c_7524])).
% 7.79/2.79  tff(c_7565, plain, (~v2_struct_0('#skF_3'('#skF_4', k1_tarski('#skF_1'('#skF_5')))) | ~v2_tex_2(k1_tarski('#skF_1'('#skF_5')), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_66, c_12, c_7564])).
% 7.79/2.79  tff(c_8019, plain, (~v2_tex_2(k1_tarski('#skF_1'('#skF_5')), '#skF_4')), inference(splitLeft, [status(thm)], [c_7565])).
% 7.79/2.79  tff(c_8022, plain, (~m1_subset_1('#skF_1'('#skF_5'), u1_struct_0('#skF_4')) | ~r1_tarski('#skF_5', '#skF_5') | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_1210, c_8019])).
% 7.79/2.79  tff(c_8031, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_158, c_7749, c_8022])).
% 7.79/2.79  tff(c_8033, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_8031])).
% 7.79/2.79  tff(c_8035, plain, (v2_tex_2(k1_tarski('#skF_1'('#skF_5')), '#skF_4')), inference(splitRight, [status(thm)], [c_7565])).
% 7.79/2.79  tff(c_8038, plain, (v2_tex_2('#skF_5', '#skF_4') | ~v1_zfmisc_1('#skF_5') | v1_xboole_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_349, c_8035])).
% 7.79/2.79  tff(c_8040, plain, (v2_tex_2('#skF_5', '#skF_4') | v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_77, c_8038])).
% 7.79/2.79  tff(c_8042, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_80, c_8040])).
% 7.79/2.79  tff(c_8043, plain, (v2_tex_2('#skF_5', '#skF_4')), inference(splitRight, [status(thm)], [c_74])).
% 7.79/2.79  tff(c_9402, plain, (![A_481, B_482]: (m1_pre_topc('#skF_3'(A_481, B_482), A_481) | ~v2_tex_2(B_482, A_481) | ~m1_subset_1(B_482, k1_zfmisc_1(u1_struct_0(A_481))) | v1_xboole_0(B_482) | ~l1_pre_topc(A_481) | ~v2_pre_topc(A_481) | v2_struct_0(A_481))), inference(cnfTransformation, [status(thm)], [f_158])).
% 7.79/2.79  tff(c_9428, plain, (m1_pre_topc('#skF_3'('#skF_4', '#skF_5'), '#skF_4') | ~v2_tex_2('#skF_5', '#skF_4') | v1_xboole_0('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_56, c_9402])).
% 7.79/2.79  tff(c_9441, plain, (m1_pre_topc('#skF_3'('#skF_4', '#skF_5'), '#skF_4') | v1_xboole_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_60, c_8043, c_9428])).
% 7.79/2.79  tff(c_9442, plain, (m1_pre_topc('#skF_3'('#skF_4', '#skF_5'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_66, c_58, c_9441])).
% 7.79/2.79  tff(c_30, plain, (![B_20, A_18]: (l1_pre_topc(B_20) | ~m1_pre_topc(B_20, A_18) | ~l1_pre_topc(A_18))), inference(cnfTransformation, [status(thm)], [f_73])).
% 7.79/2.79  tff(c_9448, plain, (l1_pre_topc('#skF_3'('#skF_4', '#skF_5')) | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_9442, c_30])).
% 7.79/2.79  tff(c_9455, plain, (l1_pre_topc('#skF_3'('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_9448])).
% 7.79/2.79  tff(c_28, plain, (![A_17]: (l1_struct_0(A_17) | ~l1_pre_topc(A_17))), inference(cnfTransformation, [status(thm)], [f_66])).
% 7.79/2.79  tff(c_8044, plain, (~v1_zfmisc_1('#skF_5')), inference(splitRight, [status(thm)], [c_74])).
% 7.79/2.79  tff(c_9036, plain, (![A_464, B_465]: (~v2_struct_0('#skF_3'(A_464, B_465)) | ~v2_tex_2(B_465, A_464) | ~m1_subset_1(B_465, k1_zfmisc_1(u1_struct_0(A_464))) | v1_xboole_0(B_465) | ~l1_pre_topc(A_464) | ~v2_pre_topc(A_464) | v2_struct_0(A_464))), inference(cnfTransformation, [status(thm)], [f_158])).
% 7.79/2.79  tff(c_9067, plain, (~v2_struct_0('#skF_3'('#skF_4', '#skF_5')) | ~v2_tex_2('#skF_5', '#skF_4') | v1_xboole_0('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_56, c_9036])).
% 7.79/2.79  tff(c_9079, plain, (~v2_struct_0('#skF_3'('#skF_4', '#skF_5')) | v1_xboole_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_60, c_8043, c_9067])).
% 7.79/2.79  tff(c_9080, plain, (~v2_struct_0('#skF_3'('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_66, c_58, c_9079])).
% 7.79/2.79  tff(c_62, plain, (v2_tdlat_3('#skF_4')), inference(cnfTransformation, [status(thm)], [f_190])).
% 7.79/2.79  tff(c_8824, plain, (![A_451, B_452]: (v1_tdlat_3('#skF_3'(A_451, B_452)) | ~v2_tex_2(B_452, A_451) | ~m1_subset_1(B_452, k1_zfmisc_1(u1_struct_0(A_451))) | v1_xboole_0(B_452) | ~l1_pre_topc(A_451) | ~v2_pre_topc(A_451) | v2_struct_0(A_451))), inference(cnfTransformation, [status(thm)], [f_158])).
% 7.79/2.79  tff(c_8855, plain, (v1_tdlat_3('#skF_3'('#skF_4', '#skF_5')) | ~v2_tex_2('#skF_5', '#skF_4') | v1_xboole_0('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_56, c_8824])).
% 7.79/2.79  tff(c_8867, plain, (v1_tdlat_3('#skF_3'('#skF_4', '#skF_5')) | v1_xboole_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_60, c_8043, c_8855])).
% 7.79/2.79  tff(c_8868, plain, (v1_tdlat_3('#skF_3'('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_66, c_58, c_8867])).
% 7.79/2.79  tff(c_38, plain, (![B_27, A_25]: (~v1_tdlat_3(B_27) | v7_struct_0(B_27) | v2_struct_0(B_27) | ~m1_pre_topc(B_27, A_25) | ~l1_pre_topc(A_25) | ~v2_tdlat_3(A_25) | ~v2_pre_topc(A_25) | v2_struct_0(A_25))), inference(cnfTransformation, [status(thm)], [f_116])).
% 7.79/2.79  tff(c_9445, plain, (~v1_tdlat_3('#skF_3'('#skF_4', '#skF_5')) | v7_struct_0('#skF_3'('#skF_4', '#skF_5')) | v2_struct_0('#skF_3'('#skF_4', '#skF_5')) | ~l1_pre_topc('#skF_4') | ~v2_tdlat_3('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_9442, c_38])).
% 7.79/2.79  tff(c_9451, plain, (v7_struct_0('#skF_3'('#skF_4', '#skF_5')) | v2_struct_0('#skF_3'('#skF_4', '#skF_5')) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_60, c_8868, c_9445])).
% 7.79/2.79  tff(c_9452, plain, (v7_struct_0('#skF_3'('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_66, c_9080, c_9451])).
% 7.79/2.79  tff(c_9661, plain, (![A_489, B_490]: (u1_struct_0('#skF_3'(A_489, B_490))=B_490 | ~v2_tex_2(B_490, A_489) | ~m1_subset_1(B_490, k1_zfmisc_1(u1_struct_0(A_489))) | v1_xboole_0(B_490) | ~l1_pre_topc(A_489) | ~v2_pre_topc(A_489) | v2_struct_0(A_489))), inference(cnfTransformation, [status(thm)], [f_158])).
% 7.79/2.79  tff(c_9702, plain, (u1_struct_0('#skF_3'('#skF_4', '#skF_5'))='#skF_5' | ~v2_tex_2('#skF_5', '#skF_4') | v1_xboole_0('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_56, c_9661])).
% 7.79/2.79  tff(c_9723, plain, (u1_struct_0('#skF_3'('#skF_4', '#skF_5'))='#skF_5' | v1_xboole_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_60, c_8043, c_9702])).
% 7.79/2.79  tff(c_9724, plain, (u1_struct_0('#skF_3'('#skF_4', '#skF_5'))='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_66, c_58, c_9723])).
% 7.79/2.79  tff(c_32, plain, (![A_21]: (v1_zfmisc_1(u1_struct_0(A_21)) | ~l1_struct_0(A_21) | ~v7_struct_0(A_21))), inference(cnfTransformation, [status(thm)], [f_79])).
% 7.79/2.79  tff(c_9745, plain, (v1_zfmisc_1('#skF_5') | ~l1_struct_0('#skF_3'('#skF_4', '#skF_5')) | ~v7_struct_0('#skF_3'('#skF_4', '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_9724, c_32])).
% 7.79/2.79  tff(c_9767, plain, (v1_zfmisc_1('#skF_5') | ~l1_struct_0('#skF_3'('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_9452, c_9745])).
% 7.79/2.79  tff(c_9768, plain, (~l1_struct_0('#skF_3'('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_8044, c_9767])).
% 7.79/2.79  tff(c_9772, plain, (~l1_pre_topc('#skF_3'('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_28, c_9768])).
% 7.79/2.79  tff(c_9776, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_9455, c_9772])).
% 7.79/2.79  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.79/2.79  
% 7.79/2.79  Inference rules
% 7.79/2.79  ----------------------
% 7.79/2.79  #Ref     : 0
% 7.79/2.79  #Sup     : 2133
% 7.79/2.79  #Fact    : 0
% 7.79/2.79  #Define  : 0
% 7.79/2.79  #Split   : 14
% 7.79/2.79  #Chain   : 0
% 7.79/2.79  #Close   : 0
% 7.79/2.79  
% 7.79/2.79  Ordering : KBO
% 7.79/2.79  
% 7.79/2.79  Simplification rules
% 7.79/2.79  ----------------------
% 7.79/2.79  #Subsume      : 569
% 7.79/2.79  #Demod        : 310
% 7.79/2.79  #Tautology    : 295
% 7.79/2.79  #SimpNegUnit  : 715
% 7.79/2.79  #BackRed      : 0
% 7.79/2.79  
% 7.79/2.79  #Partial instantiations: 0
% 7.79/2.79  #Strategies tried      : 1
% 7.79/2.79  
% 7.79/2.79  Timing (in seconds)
% 7.79/2.79  ----------------------
% 7.79/2.80  Preprocessing        : 0.33
% 7.79/2.80  Parsing              : 0.18
% 7.79/2.80  CNF conversion       : 0.02
% 7.79/2.80  Main loop            : 1.67
% 7.79/2.80  Inferencing          : 0.54
% 7.79/2.80  Reduction            : 0.47
% 7.79/2.80  Demodulation         : 0.27
% 7.79/2.80  BG Simplification    : 0.06
% 7.79/2.80  Subsumption          : 0.47
% 7.79/2.80  Abstraction          : 0.08
% 7.79/2.80  MUC search           : 0.00
% 7.79/2.80  Cooper               : 0.00
% 7.79/2.80  Total                : 2.06
% 7.79/2.80  Index Insertion      : 0.00
% 7.79/2.80  Index Deletion       : 0.00
% 7.79/2.80  Index Matching       : 0.00
% 7.79/2.80  BG Taut test         : 0.00
%------------------------------------------------------------------------------
