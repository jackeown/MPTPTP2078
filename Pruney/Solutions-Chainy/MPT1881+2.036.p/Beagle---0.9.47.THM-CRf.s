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
% DateTime   : Thu Dec  3 10:30:11 EST 2020

% Result     : Theorem 3.88s
% Output     : CNFRefutation 4.14s
% Verified   : 
% Statistics : Number of formulae       :  125 ( 536 expanded)
%              Number of leaves         :   29 ( 191 expanded)
%              Depth                    :   14
%              Number of atoms          :  282 (1487 expanded)
%              Number of equality atoms :   24 (  99 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_tex_2 > v2_tex_2 > v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_tdlat_3 > l1_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(v1_tdlat_3,type,(
    v1_tdlat_3: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v3_tex_2,type,(
    v3_tex_2: ( $i * $i ) > $o )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_40,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_42,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( v1_subset_1(B,A)
      <=> B != A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).

tff(f_120,negated_conjecture,(
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

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_88,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( B = u1_struct_0(A)
           => ( v2_tex_2(B,A)
            <=> v1_tdlat_3(A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_tex_2)).

tff(f_74,axiom,(
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

tff(c_14,plain,(
    ! [A_8] : k2_subset_1(A_8) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_16,plain,(
    ! [A_9] : m1_subset_1(k2_subset_1(A_9),k1_zfmisc_1(A_9)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_59,plain,(
    ! [A_9] : m1_subset_1(A_9,k1_zfmisc_1(A_9)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_16])).

tff(c_22,plain,(
    ! [B_15] :
      ( ~ v1_subset_1(B_15,B_15)
      | ~ m1_subset_1(B_15,k1_zfmisc_1(B_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_61,plain,(
    ! [B_15] : ~ v1_subset_1(B_15,B_15) ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_22])).

tff(c_42,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_577,plain,(
    ! [C_124,A_125,B_126] :
      ( r2_hidden(C_124,A_125)
      | ~ r2_hidden(C_124,B_126)
      | ~ m1_subset_1(B_126,k1_zfmisc_1(A_125)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_606,plain,(
    ! [A_133,B_134,A_135] :
      ( r2_hidden('#skF_1'(A_133,B_134),A_135)
      | ~ m1_subset_1(A_133,k1_zfmisc_1(A_135))
      | r1_tarski(A_133,B_134) ) ),
    inference(resolution,[status(thm)],[c_6,c_577])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_618,plain,(
    ! [A_136,A_137] :
      ( ~ m1_subset_1(A_136,k1_zfmisc_1(A_137))
      | r1_tarski(A_136,A_137) ) ),
    inference(resolution,[status(thm)],[c_606,c_4])).

tff(c_625,plain,(
    r1_tarski('#skF_4',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_42,c_618])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( B_7 = A_6
      | ~ r1_tarski(B_7,A_6)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_643,plain,
    ( u1_struct_0('#skF_3') = '#skF_4'
    | ~ r1_tarski(u1_struct_0('#skF_3'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_625,c_8])).

tff(c_644,plain,(
    ~ r1_tarski(u1_struct_0('#skF_3'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_643])).

tff(c_44,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_58,plain,
    ( v3_tex_2('#skF_4','#skF_3')
    | ~ v1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_79,plain,(
    ~ v1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_52,plain,
    ( v1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ v3_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_80,plain,(
    ~ v3_tex_2('#skF_4','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_79,c_52])).

tff(c_50,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_46,plain,(
    v1_tdlat_3('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_96,plain,(
    ! [B_43,A_44] :
      ( v1_subset_1(B_43,A_44)
      | B_43 = A_44
      | ~ m1_subset_1(B_43,k1_zfmisc_1(A_44)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_99,plain,
    ( v1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | u1_struct_0('#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_42,c_96])).

tff(c_105,plain,(
    u1_struct_0('#skF_3') = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_79,c_99])).

tff(c_36,plain,(
    ! [A_26] :
      ( v2_tex_2(u1_struct_0(A_26),A_26)
      | ~ v1_tdlat_3(A_26)
      | ~ m1_subset_1(u1_struct_0(A_26),k1_zfmisc_1(u1_struct_0(A_26)))
      | ~ l1_pre_topc(A_26)
      | v2_struct_0(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_143,plain,(
    ! [A_54] :
      ( v2_tex_2(u1_struct_0(A_54),A_54)
      | ~ v1_tdlat_3(A_54)
      | ~ l1_pre_topc(A_54)
      | v2_struct_0(A_54) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_36])).

tff(c_149,plain,
    ( v2_tex_2('#skF_4','#skF_3')
    | ~ v1_tdlat_3('#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_105,c_143])).

tff(c_152,plain,
    ( v2_tex_2('#skF_4','#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_46,c_149])).

tff(c_153,plain,(
    v2_tex_2('#skF_4','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_152])).

tff(c_210,plain,(
    ! [A_66,B_67] :
      ( '#skF_2'(A_66,B_67) != B_67
      | v3_tex_2(B_67,A_66)
      | ~ v2_tex_2(B_67,A_66)
      | ~ m1_subset_1(B_67,k1_zfmisc_1(u1_struct_0(A_66)))
      | ~ l1_pre_topc(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_213,plain,(
    ! [B_67] :
      ( '#skF_2'('#skF_3',B_67) != B_67
      | v3_tex_2(B_67,'#skF_3')
      | ~ v2_tex_2(B_67,'#skF_3')
      | ~ m1_subset_1(B_67,k1_zfmisc_1('#skF_4'))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_105,c_210])).

tff(c_231,plain,(
    ! [B_74] :
      ( '#skF_2'('#skF_3',B_74) != B_74
      | v3_tex_2(B_74,'#skF_3')
      | ~ v2_tex_2(B_74,'#skF_3')
      | ~ m1_subset_1(B_74,k1_zfmisc_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_213])).

tff(c_235,plain,
    ( '#skF_2'('#skF_3','#skF_4') != '#skF_4'
    | v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_59,c_231])).

tff(c_238,plain,
    ( '#skF_2'('#skF_3','#skF_4') != '#skF_4'
    | v3_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_153,c_235])).

tff(c_239,plain,(
    '#skF_2'('#skF_3','#skF_4') != '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_238])).

tff(c_321,plain,(
    ! [A_96,B_97] :
      ( m1_subset_1('#skF_2'(A_96,B_97),k1_zfmisc_1(u1_struct_0(A_96)))
      | v3_tex_2(B_97,A_96)
      | ~ v2_tex_2(B_97,A_96)
      | ~ m1_subset_1(B_97,k1_zfmisc_1(u1_struct_0(A_96)))
      | ~ l1_pre_topc(A_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_347,plain,(
    ! [B_97] :
      ( m1_subset_1('#skF_2'('#skF_3',B_97),k1_zfmisc_1('#skF_4'))
      | v3_tex_2(B_97,'#skF_3')
      | ~ v2_tex_2(B_97,'#skF_3')
      | ~ m1_subset_1(B_97,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_105,c_321])).

tff(c_485,plain,(
    ! [B_109] :
      ( m1_subset_1('#skF_2'('#skF_3',B_109),k1_zfmisc_1('#skF_4'))
      | v3_tex_2(B_109,'#skF_3')
      | ~ v2_tex_2(B_109,'#skF_3')
      | ~ m1_subset_1(B_109,k1_zfmisc_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_105,c_347])).

tff(c_121,plain,(
    ! [C_48,A_49,B_50] :
      ( r2_hidden(C_48,A_49)
      | ~ r2_hidden(C_48,B_50)
      | ~ m1_subset_1(B_50,k1_zfmisc_1(A_49)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_198,plain,(
    ! [A_63,B_64,A_65] :
      ( r2_hidden('#skF_1'(A_63,B_64),A_65)
      | ~ m1_subset_1(A_63,k1_zfmisc_1(A_65))
      | r1_tarski(A_63,B_64) ) ),
    inference(resolution,[status(thm)],[c_6,c_121])).

tff(c_209,plain,(
    ! [A_63,A_65] :
      ( ~ m1_subset_1(A_63,k1_zfmisc_1(A_65))
      | r1_tarski(A_63,A_65) ) ),
    inference(resolution,[status(thm)],[c_198,c_4])).

tff(c_508,plain,(
    ! [B_110] :
      ( r1_tarski('#skF_2'('#skF_3',B_110),'#skF_4')
      | v3_tex_2(B_110,'#skF_3')
      | ~ v2_tex_2(B_110,'#skF_3')
      | ~ m1_subset_1(B_110,k1_zfmisc_1('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_485,c_209])).

tff(c_280,plain,(
    ! [B_92,A_93] :
      ( r1_tarski(B_92,'#skF_2'(A_93,B_92))
      | v3_tex_2(B_92,A_93)
      | ~ v2_tex_2(B_92,A_93)
      | ~ m1_subset_1(B_92,k1_zfmisc_1(u1_struct_0(A_93)))
      | ~ l1_pre_topc(A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_299,plain,(
    ! [A_95] :
      ( r1_tarski(u1_struct_0(A_95),'#skF_2'(A_95,u1_struct_0(A_95)))
      | v3_tex_2(u1_struct_0(A_95),A_95)
      | ~ v2_tex_2(u1_struct_0(A_95),A_95)
      | ~ l1_pre_topc(A_95) ) ),
    inference(resolution,[status(thm)],[c_59,c_280])).

tff(c_308,plain,
    ( r1_tarski('#skF_4','#skF_2'('#skF_3',u1_struct_0('#skF_3')))
    | v3_tex_2(u1_struct_0('#skF_3'),'#skF_3')
    | ~ v2_tex_2(u1_struct_0('#skF_3'),'#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_105,c_299])).

tff(c_316,plain,
    ( r1_tarski('#skF_4','#skF_2'('#skF_3','#skF_4'))
    | v3_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_153,c_105,c_105,c_105,c_308])).

tff(c_317,plain,(
    r1_tarski('#skF_4','#skF_2'('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_316])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_208,plain,(
    ! [A_63,B_64,B_2,A_65] :
      ( r2_hidden('#skF_1'(A_63,B_64),B_2)
      | ~ r1_tarski(A_65,B_2)
      | ~ m1_subset_1(A_63,k1_zfmisc_1(A_65))
      | r1_tarski(A_63,B_64) ) ),
    inference(resolution,[status(thm)],[c_198,c_2])).

tff(c_411,plain,(
    ! [A_102,B_103] :
      ( r2_hidden('#skF_1'(A_102,B_103),'#skF_2'('#skF_3','#skF_4'))
      | ~ m1_subset_1(A_102,k1_zfmisc_1('#skF_4'))
      | r1_tarski(A_102,B_103) ) ),
    inference(resolution,[status(thm)],[c_317,c_208])).

tff(c_423,plain,(
    ! [A_104] :
      ( ~ m1_subset_1(A_104,k1_zfmisc_1('#skF_4'))
      | r1_tarski(A_104,'#skF_2'('#skF_3','#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_411,c_4])).

tff(c_437,plain,(
    ! [A_104] :
      ( A_104 = '#skF_2'('#skF_3','#skF_4')
      | ~ r1_tarski('#skF_2'('#skF_3','#skF_4'),A_104)
      | ~ m1_subset_1(A_104,k1_zfmisc_1('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_423,c_8])).

tff(c_514,plain,
    ( '#skF_2'('#skF_3','#skF_4') = '#skF_4'
    | v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_508,c_437])).

tff(c_531,plain,
    ( '#skF_2'('#skF_3','#skF_4') = '#skF_4'
    | v3_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_153,c_514])).

tff(c_533,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_239,c_531])).

tff(c_534,plain,(
    v3_tex_2('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_65,plain,(
    ! [A_26] :
      ( v2_tex_2(u1_struct_0(A_26),A_26)
      | ~ v1_tdlat_3(A_26)
      | ~ l1_pre_topc(A_26)
      | v2_struct_0(A_26) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_36])).

tff(c_810,plain,(
    ! [B_174,A_175] :
      ( r1_tarski(B_174,'#skF_2'(A_175,B_174))
      | v3_tex_2(B_174,A_175)
      | ~ v2_tex_2(B_174,A_175)
      | ~ m1_subset_1(B_174,k1_zfmisc_1(u1_struct_0(A_175)))
      | ~ l1_pre_topc(A_175) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_919,plain,(
    ! [A_199] :
      ( r1_tarski(u1_struct_0(A_199),'#skF_2'(A_199,u1_struct_0(A_199)))
      | v3_tex_2(u1_struct_0(A_199),A_199)
      | ~ v2_tex_2(u1_struct_0(A_199),A_199)
      | ~ l1_pre_topc(A_199) ) ),
    inference(resolution,[status(thm)],[c_59,c_810])).

tff(c_567,plain,(
    ! [C_119,B_120,A_121] :
      ( r2_hidden(C_119,B_120)
      | ~ r2_hidden(C_119,A_121)
      | ~ r1_tarski(A_121,B_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_594,plain,(
    ! [A_130,B_131,B_132] :
      ( r2_hidden('#skF_1'(A_130,B_131),B_132)
      | ~ r1_tarski(A_130,B_132)
      | r1_tarski(A_130,B_131) ) ),
    inference(resolution,[status(thm)],[c_6,c_567])).

tff(c_657,plain,(
    ! [A_142,B_143,B_144,B_145] :
      ( r2_hidden('#skF_1'(A_142,B_143),B_144)
      | ~ r1_tarski(B_145,B_144)
      | ~ r1_tarski(A_142,B_145)
      | r1_tarski(A_142,B_143) ) ),
    inference(resolution,[status(thm)],[c_594,c_2])).

tff(c_664,plain,(
    ! [A_146,B_147] :
      ( r2_hidden('#skF_1'(A_146,B_147),u1_struct_0('#skF_3'))
      | ~ r1_tarski(A_146,'#skF_4')
      | r1_tarski(A_146,B_147) ) ),
    inference(resolution,[status(thm)],[c_625,c_657])).

tff(c_748,plain,(
    ! [A_163,B_164,B_165] :
      ( r2_hidden('#skF_1'(A_163,B_164),B_165)
      | ~ r1_tarski(u1_struct_0('#skF_3'),B_165)
      | ~ r1_tarski(A_163,'#skF_4')
      | r1_tarski(A_163,B_164) ) ),
    inference(resolution,[status(thm)],[c_664,c_2])).

tff(c_759,plain,(
    ! [B_165,A_163] :
      ( ~ r1_tarski(u1_struct_0('#skF_3'),B_165)
      | ~ r1_tarski(A_163,'#skF_4')
      | r1_tarski(A_163,B_165) ) ),
    inference(resolution,[status(thm)],[c_748,c_4])).

tff(c_933,plain,(
    ! [A_163] :
      ( ~ r1_tarski(A_163,'#skF_4')
      | r1_tarski(A_163,'#skF_2'('#skF_3',u1_struct_0('#skF_3')))
      | v3_tex_2(u1_struct_0('#skF_3'),'#skF_3')
      | ~ v2_tex_2(u1_struct_0('#skF_3'),'#skF_3')
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_919,c_759])).

tff(c_954,plain,(
    ! [A_163] :
      ( ~ r1_tarski(A_163,'#skF_4')
      | r1_tarski(A_163,'#skF_2'('#skF_3',u1_struct_0('#skF_3')))
      | v3_tex_2(u1_struct_0('#skF_3'),'#skF_3')
      | ~ v2_tex_2(u1_struct_0('#skF_3'),'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_933])).

tff(c_971,plain,(
    ~ v2_tex_2(u1_struct_0('#skF_3'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_954])).

tff(c_990,plain,
    ( ~ v1_tdlat_3('#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_65,c_971])).

tff(c_993,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_46,c_990])).

tff(c_995,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_993])).

tff(c_997,plain,(
    v2_tex_2(u1_struct_0('#skF_3'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_954])).

tff(c_1028,plain,(
    ! [C_211,B_212,A_213] :
      ( C_211 = B_212
      | ~ r1_tarski(B_212,C_211)
      | ~ v2_tex_2(C_211,A_213)
      | ~ m1_subset_1(C_211,k1_zfmisc_1(u1_struct_0(A_213)))
      | ~ v3_tex_2(B_212,A_213)
      | ~ m1_subset_1(B_212,k1_zfmisc_1(u1_struct_0(A_213)))
      | ~ l1_pre_topc(A_213) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_1042,plain,(
    ! [A_213] :
      ( u1_struct_0('#skF_3') = '#skF_4'
      | ~ v2_tex_2(u1_struct_0('#skF_3'),A_213)
      | ~ m1_subset_1(u1_struct_0('#skF_3'),k1_zfmisc_1(u1_struct_0(A_213)))
      | ~ v3_tex_2('#skF_4',A_213)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(A_213)))
      | ~ l1_pre_topc(A_213) ) ),
    inference(resolution,[status(thm)],[c_625,c_1028])).

tff(c_1099,plain,(
    ! [A_224] :
      ( ~ v2_tex_2(u1_struct_0('#skF_3'),A_224)
      | ~ m1_subset_1(u1_struct_0('#skF_3'),k1_zfmisc_1(u1_struct_0(A_224)))
      | ~ v3_tex_2('#skF_4',A_224)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(A_224)))
      | ~ l1_pre_topc(A_224) ) ),
    inference(splitLeft,[status(thm)],[c_1042])).

tff(c_1103,plain,
    ( ~ v2_tex_2(u1_struct_0('#skF_3'),'#skF_3')
    | ~ v3_tex_2('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_59,c_1099])).

tff(c_1107,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_534,c_997,c_1103])).

tff(c_1108,plain,(
    u1_struct_0('#skF_3') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1042])).

tff(c_711,plain,(
    ! [A_156,B_157,B_158,A_159] :
      ( r2_hidden('#skF_1'(A_156,B_157),B_158)
      | ~ r1_tarski(A_159,B_158)
      | ~ m1_subset_1(A_156,k1_zfmisc_1(A_159))
      | r1_tarski(A_156,B_157) ) ),
    inference(resolution,[status(thm)],[c_606,c_2])).

tff(c_721,plain,(
    ! [A_160,B_161] :
      ( r2_hidden('#skF_1'(A_160,B_161),u1_struct_0('#skF_3'))
      | ~ m1_subset_1(A_160,k1_zfmisc_1('#skF_4'))
      | r1_tarski(A_160,B_161) ) ),
    inference(resolution,[status(thm)],[c_625,c_711])).

tff(c_733,plain,(
    ! [A_162] :
      ( ~ m1_subset_1(A_162,k1_zfmisc_1('#skF_4'))
      | r1_tarski(A_162,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_721,c_4])).

tff(c_604,plain,(
    ! [A_130,B_131,B_2,B_132] :
      ( r2_hidden('#skF_1'(A_130,B_131),B_2)
      | ~ r1_tarski(B_132,B_2)
      | ~ r1_tarski(A_130,B_132)
      | r1_tarski(A_130,B_131) ) ),
    inference(resolution,[status(thm)],[c_594,c_2])).

tff(c_862,plain,(
    ! [A_191,B_192,A_193] :
      ( r2_hidden('#skF_1'(A_191,B_192),u1_struct_0('#skF_3'))
      | ~ r1_tarski(A_191,A_193)
      | r1_tarski(A_191,B_192)
      | ~ m1_subset_1(A_193,k1_zfmisc_1('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_733,c_604])).

tff(c_873,plain,(
    ! [B_192] :
      ( r2_hidden('#skF_1'('#skF_4',B_192),u1_struct_0('#skF_3'))
      | r1_tarski('#skF_4',B_192)
      | ~ m1_subset_1(u1_struct_0('#skF_3'),k1_zfmisc_1('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_625,c_862])).

tff(c_875,plain,(
    ~ m1_subset_1(u1_struct_0('#skF_3'),k1_zfmisc_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_873])).

tff(c_1115,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1108,c_875])).

tff(c_1138,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_1115])).

tff(c_1140,plain,(
    m1_subset_1(u1_struct_0('#skF_3'),k1_zfmisc_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_873])).

tff(c_617,plain,(
    ! [A_133,A_135] :
      ( ~ m1_subset_1(A_133,k1_zfmisc_1(A_135))
      | r1_tarski(A_133,A_135) ) ),
    inference(resolution,[status(thm)],[c_606,c_4])).

tff(c_1151,plain,(
    r1_tarski(u1_struct_0('#skF_3'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_1140,c_617])).

tff(c_1162,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_644,c_1151])).

tff(c_1163,plain,(
    u1_struct_0('#skF_3') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_643])).

tff(c_537,plain,(
    v1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_534,c_52])).

tff(c_1166,plain,(
    v1_subset_1('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1163,c_537])).

tff(c_1170,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_61,c_1166])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:33:54 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.88/1.78  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.88/1.79  
% 3.88/1.79  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.88/1.79  %$ v3_tex_2 > v2_tex_2 > v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_tdlat_3 > l1_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 3.88/1.79  
% 3.88/1.79  %Foreground sorts:
% 3.88/1.79  
% 3.88/1.79  
% 3.88/1.79  %Background operators:
% 3.88/1.79  
% 3.88/1.79  
% 3.88/1.79  %Foreground operators:
% 3.88/1.79  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.88/1.79  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.88/1.79  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.88/1.79  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 3.88/1.79  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.88/1.79  tff(v1_tdlat_3, type, v1_tdlat_3: $i > $o).
% 3.88/1.79  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.88/1.79  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 3.88/1.79  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 3.88/1.79  tff('#skF_3', type, '#skF_3': $i).
% 3.88/1.79  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.88/1.79  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.88/1.79  tff('#skF_4', type, '#skF_4': $i).
% 3.88/1.79  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.88/1.79  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.88/1.79  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.88/1.79  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.88/1.79  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.88/1.79  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 3.88/1.79  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.88/1.79  
% 4.14/1.82  tff(f_40, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 4.14/1.82  tff(f_42, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 4.14/1.82  tff(f_56, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (v1_subset_1(B, A) <=> ~(B = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_subset_1)).
% 4.14/1.82  tff(f_120, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v1_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tex_2(B, A) <=> ~v1_subset_1(B, u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_tex_2)).
% 4.14/1.82  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 4.14/1.82  tff(f_49, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 4.14/1.82  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.14/1.82  tff(f_88, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((B = u1_struct_0(A)) => (v2_tex_2(B, A) <=> v1_tdlat_3(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t27_tex_2)).
% 4.14/1.82  tff(f_74, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tex_2(B, A) <=> (v2_tex_2(B, A) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v2_tex_2(C, A) & r1_tarski(B, C)) => (B = C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_tex_2)).
% 4.14/1.82  tff(c_14, plain, (![A_8]: (k2_subset_1(A_8)=A_8)), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.14/1.82  tff(c_16, plain, (![A_9]: (m1_subset_1(k2_subset_1(A_9), k1_zfmisc_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.14/1.82  tff(c_59, plain, (![A_9]: (m1_subset_1(A_9, k1_zfmisc_1(A_9)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_16])).
% 4.14/1.82  tff(c_22, plain, (![B_15]: (~v1_subset_1(B_15, B_15) | ~m1_subset_1(B_15, k1_zfmisc_1(B_15)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.14/1.82  tff(c_61, plain, (![B_15]: (~v1_subset_1(B_15, B_15))), inference(demodulation, [status(thm), theory('equality')], [c_59, c_22])).
% 4.14/1.82  tff(c_42, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_120])).
% 4.14/1.82  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.14/1.82  tff(c_577, plain, (![C_124, A_125, B_126]: (r2_hidden(C_124, A_125) | ~r2_hidden(C_124, B_126) | ~m1_subset_1(B_126, k1_zfmisc_1(A_125)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.14/1.82  tff(c_606, plain, (![A_133, B_134, A_135]: (r2_hidden('#skF_1'(A_133, B_134), A_135) | ~m1_subset_1(A_133, k1_zfmisc_1(A_135)) | r1_tarski(A_133, B_134))), inference(resolution, [status(thm)], [c_6, c_577])).
% 4.14/1.82  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.14/1.82  tff(c_618, plain, (![A_136, A_137]: (~m1_subset_1(A_136, k1_zfmisc_1(A_137)) | r1_tarski(A_136, A_137))), inference(resolution, [status(thm)], [c_606, c_4])).
% 4.14/1.82  tff(c_625, plain, (r1_tarski('#skF_4', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_42, c_618])).
% 4.14/1.82  tff(c_8, plain, (![B_7, A_6]: (B_7=A_6 | ~r1_tarski(B_7, A_6) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.14/1.82  tff(c_643, plain, (u1_struct_0('#skF_3')='#skF_4' | ~r1_tarski(u1_struct_0('#skF_3'), '#skF_4')), inference(resolution, [status(thm)], [c_625, c_8])).
% 4.14/1.82  tff(c_644, plain, (~r1_tarski(u1_struct_0('#skF_3'), '#skF_4')), inference(splitLeft, [status(thm)], [c_643])).
% 4.14/1.82  tff(c_44, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_120])).
% 4.14/1.82  tff(c_58, plain, (v3_tex_2('#skF_4', '#skF_3') | ~v1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_120])).
% 4.14/1.82  tff(c_79, plain, (~v1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_58])).
% 4.14/1.82  tff(c_52, plain, (v1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~v3_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_120])).
% 4.14/1.82  tff(c_80, plain, (~v3_tex_2('#skF_4', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_79, c_52])).
% 4.14/1.82  tff(c_50, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_120])).
% 4.14/1.82  tff(c_46, plain, (v1_tdlat_3('#skF_3')), inference(cnfTransformation, [status(thm)], [f_120])).
% 4.14/1.82  tff(c_96, plain, (![B_43, A_44]: (v1_subset_1(B_43, A_44) | B_43=A_44 | ~m1_subset_1(B_43, k1_zfmisc_1(A_44)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.14/1.82  tff(c_99, plain, (v1_subset_1('#skF_4', u1_struct_0('#skF_3')) | u1_struct_0('#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_42, c_96])).
% 4.14/1.82  tff(c_105, plain, (u1_struct_0('#skF_3')='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_79, c_99])).
% 4.14/1.82  tff(c_36, plain, (![A_26]: (v2_tex_2(u1_struct_0(A_26), A_26) | ~v1_tdlat_3(A_26) | ~m1_subset_1(u1_struct_0(A_26), k1_zfmisc_1(u1_struct_0(A_26))) | ~l1_pre_topc(A_26) | v2_struct_0(A_26))), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.14/1.82  tff(c_143, plain, (![A_54]: (v2_tex_2(u1_struct_0(A_54), A_54) | ~v1_tdlat_3(A_54) | ~l1_pre_topc(A_54) | v2_struct_0(A_54))), inference(demodulation, [status(thm), theory('equality')], [c_59, c_36])).
% 4.14/1.82  tff(c_149, plain, (v2_tex_2('#skF_4', '#skF_3') | ~v1_tdlat_3('#skF_3') | ~l1_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_105, c_143])).
% 4.14/1.82  tff(c_152, plain, (v2_tex_2('#skF_4', '#skF_3') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_46, c_149])).
% 4.14/1.82  tff(c_153, plain, (v2_tex_2('#skF_4', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_50, c_152])).
% 4.14/1.82  tff(c_210, plain, (![A_66, B_67]: ('#skF_2'(A_66, B_67)!=B_67 | v3_tex_2(B_67, A_66) | ~v2_tex_2(B_67, A_66) | ~m1_subset_1(B_67, k1_zfmisc_1(u1_struct_0(A_66))) | ~l1_pre_topc(A_66))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.14/1.82  tff(c_213, plain, (![B_67]: ('#skF_2'('#skF_3', B_67)!=B_67 | v3_tex_2(B_67, '#skF_3') | ~v2_tex_2(B_67, '#skF_3') | ~m1_subset_1(B_67, k1_zfmisc_1('#skF_4')) | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_105, c_210])).
% 4.14/1.82  tff(c_231, plain, (![B_74]: ('#skF_2'('#skF_3', B_74)!=B_74 | v3_tex_2(B_74, '#skF_3') | ~v2_tex_2(B_74, '#skF_3') | ~m1_subset_1(B_74, k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_213])).
% 4.14/1.82  tff(c_235, plain, ('#skF_2'('#skF_3', '#skF_4')!='#skF_4' | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_59, c_231])).
% 4.14/1.82  tff(c_238, plain, ('#skF_2'('#skF_3', '#skF_4')!='#skF_4' | v3_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_153, c_235])).
% 4.14/1.82  tff(c_239, plain, ('#skF_2'('#skF_3', '#skF_4')!='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_80, c_238])).
% 4.14/1.82  tff(c_321, plain, (![A_96, B_97]: (m1_subset_1('#skF_2'(A_96, B_97), k1_zfmisc_1(u1_struct_0(A_96))) | v3_tex_2(B_97, A_96) | ~v2_tex_2(B_97, A_96) | ~m1_subset_1(B_97, k1_zfmisc_1(u1_struct_0(A_96))) | ~l1_pre_topc(A_96))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.14/1.82  tff(c_347, plain, (![B_97]: (m1_subset_1('#skF_2'('#skF_3', B_97), k1_zfmisc_1('#skF_4')) | v3_tex_2(B_97, '#skF_3') | ~v2_tex_2(B_97, '#skF_3') | ~m1_subset_1(B_97, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_105, c_321])).
% 4.14/1.82  tff(c_485, plain, (![B_109]: (m1_subset_1('#skF_2'('#skF_3', B_109), k1_zfmisc_1('#skF_4')) | v3_tex_2(B_109, '#skF_3') | ~v2_tex_2(B_109, '#skF_3') | ~m1_subset_1(B_109, k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_105, c_347])).
% 4.14/1.82  tff(c_121, plain, (![C_48, A_49, B_50]: (r2_hidden(C_48, A_49) | ~r2_hidden(C_48, B_50) | ~m1_subset_1(B_50, k1_zfmisc_1(A_49)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.14/1.82  tff(c_198, plain, (![A_63, B_64, A_65]: (r2_hidden('#skF_1'(A_63, B_64), A_65) | ~m1_subset_1(A_63, k1_zfmisc_1(A_65)) | r1_tarski(A_63, B_64))), inference(resolution, [status(thm)], [c_6, c_121])).
% 4.14/1.82  tff(c_209, plain, (![A_63, A_65]: (~m1_subset_1(A_63, k1_zfmisc_1(A_65)) | r1_tarski(A_63, A_65))), inference(resolution, [status(thm)], [c_198, c_4])).
% 4.14/1.82  tff(c_508, plain, (![B_110]: (r1_tarski('#skF_2'('#skF_3', B_110), '#skF_4') | v3_tex_2(B_110, '#skF_3') | ~v2_tex_2(B_110, '#skF_3') | ~m1_subset_1(B_110, k1_zfmisc_1('#skF_4')))), inference(resolution, [status(thm)], [c_485, c_209])).
% 4.14/1.82  tff(c_280, plain, (![B_92, A_93]: (r1_tarski(B_92, '#skF_2'(A_93, B_92)) | v3_tex_2(B_92, A_93) | ~v2_tex_2(B_92, A_93) | ~m1_subset_1(B_92, k1_zfmisc_1(u1_struct_0(A_93))) | ~l1_pre_topc(A_93))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.14/1.82  tff(c_299, plain, (![A_95]: (r1_tarski(u1_struct_0(A_95), '#skF_2'(A_95, u1_struct_0(A_95))) | v3_tex_2(u1_struct_0(A_95), A_95) | ~v2_tex_2(u1_struct_0(A_95), A_95) | ~l1_pre_topc(A_95))), inference(resolution, [status(thm)], [c_59, c_280])).
% 4.14/1.82  tff(c_308, plain, (r1_tarski('#skF_4', '#skF_2'('#skF_3', u1_struct_0('#skF_3'))) | v3_tex_2(u1_struct_0('#skF_3'), '#skF_3') | ~v2_tex_2(u1_struct_0('#skF_3'), '#skF_3') | ~l1_pre_topc('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_105, c_299])).
% 4.14/1.82  tff(c_316, plain, (r1_tarski('#skF_4', '#skF_2'('#skF_3', '#skF_4')) | v3_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_153, c_105, c_105, c_105, c_308])).
% 4.14/1.82  tff(c_317, plain, (r1_tarski('#skF_4', '#skF_2'('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_80, c_316])).
% 4.14/1.82  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.14/1.82  tff(c_208, plain, (![A_63, B_64, B_2, A_65]: (r2_hidden('#skF_1'(A_63, B_64), B_2) | ~r1_tarski(A_65, B_2) | ~m1_subset_1(A_63, k1_zfmisc_1(A_65)) | r1_tarski(A_63, B_64))), inference(resolution, [status(thm)], [c_198, c_2])).
% 4.14/1.82  tff(c_411, plain, (![A_102, B_103]: (r2_hidden('#skF_1'(A_102, B_103), '#skF_2'('#skF_3', '#skF_4')) | ~m1_subset_1(A_102, k1_zfmisc_1('#skF_4')) | r1_tarski(A_102, B_103))), inference(resolution, [status(thm)], [c_317, c_208])).
% 4.14/1.82  tff(c_423, plain, (![A_104]: (~m1_subset_1(A_104, k1_zfmisc_1('#skF_4')) | r1_tarski(A_104, '#skF_2'('#skF_3', '#skF_4')))), inference(resolution, [status(thm)], [c_411, c_4])).
% 4.14/1.82  tff(c_437, plain, (![A_104]: (A_104='#skF_2'('#skF_3', '#skF_4') | ~r1_tarski('#skF_2'('#skF_3', '#skF_4'), A_104) | ~m1_subset_1(A_104, k1_zfmisc_1('#skF_4')))), inference(resolution, [status(thm)], [c_423, c_8])).
% 4.14/1.82  tff(c_514, plain, ('#skF_2'('#skF_3', '#skF_4')='#skF_4' | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(resolution, [status(thm)], [c_508, c_437])).
% 4.14/1.82  tff(c_531, plain, ('#skF_2'('#skF_3', '#skF_4')='#skF_4' | v3_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_59, c_153, c_514])).
% 4.14/1.82  tff(c_533, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_239, c_531])).
% 4.14/1.82  tff(c_534, plain, (v3_tex_2('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_58])).
% 4.14/1.82  tff(c_65, plain, (![A_26]: (v2_tex_2(u1_struct_0(A_26), A_26) | ~v1_tdlat_3(A_26) | ~l1_pre_topc(A_26) | v2_struct_0(A_26))), inference(demodulation, [status(thm), theory('equality')], [c_59, c_36])).
% 4.14/1.82  tff(c_810, plain, (![B_174, A_175]: (r1_tarski(B_174, '#skF_2'(A_175, B_174)) | v3_tex_2(B_174, A_175) | ~v2_tex_2(B_174, A_175) | ~m1_subset_1(B_174, k1_zfmisc_1(u1_struct_0(A_175))) | ~l1_pre_topc(A_175))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.14/1.82  tff(c_919, plain, (![A_199]: (r1_tarski(u1_struct_0(A_199), '#skF_2'(A_199, u1_struct_0(A_199))) | v3_tex_2(u1_struct_0(A_199), A_199) | ~v2_tex_2(u1_struct_0(A_199), A_199) | ~l1_pre_topc(A_199))), inference(resolution, [status(thm)], [c_59, c_810])).
% 4.14/1.82  tff(c_567, plain, (![C_119, B_120, A_121]: (r2_hidden(C_119, B_120) | ~r2_hidden(C_119, A_121) | ~r1_tarski(A_121, B_120))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.14/1.82  tff(c_594, plain, (![A_130, B_131, B_132]: (r2_hidden('#skF_1'(A_130, B_131), B_132) | ~r1_tarski(A_130, B_132) | r1_tarski(A_130, B_131))), inference(resolution, [status(thm)], [c_6, c_567])).
% 4.14/1.82  tff(c_657, plain, (![A_142, B_143, B_144, B_145]: (r2_hidden('#skF_1'(A_142, B_143), B_144) | ~r1_tarski(B_145, B_144) | ~r1_tarski(A_142, B_145) | r1_tarski(A_142, B_143))), inference(resolution, [status(thm)], [c_594, c_2])).
% 4.14/1.82  tff(c_664, plain, (![A_146, B_147]: (r2_hidden('#skF_1'(A_146, B_147), u1_struct_0('#skF_3')) | ~r1_tarski(A_146, '#skF_4') | r1_tarski(A_146, B_147))), inference(resolution, [status(thm)], [c_625, c_657])).
% 4.14/1.82  tff(c_748, plain, (![A_163, B_164, B_165]: (r2_hidden('#skF_1'(A_163, B_164), B_165) | ~r1_tarski(u1_struct_0('#skF_3'), B_165) | ~r1_tarski(A_163, '#skF_4') | r1_tarski(A_163, B_164))), inference(resolution, [status(thm)], [c_664, c_2])).
% 4.14/1.82  tff(c_759, plain, (![B_165, A_163]: (~r1_tarski(u1_struct_0('#skF_3'), B_165) | ~r1_tarski(A_163, '#skF_4') | r1_tarski(A_163, B_165))), inference(resolution, [status(thm)], [c_748, c_4])).
% 4.14/1.82  tff(c_933, plain, (![A_163]: (~r1_tarski(A_163, '#skF_4') | r1_tarski(A_163, '#skF_2'('#skF_3', u1_struct_0('#skF_3'))) | v3_tex_2(u1_struct_0('#skF_3'), '#skF_3') | ~v2_tex_2(u1_struct_0('#skF_3'), '#skF_3') | ~l1_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_919, c_759])).
% 4.14/1.82  tff(c_954, plain, (![A_163]: (~r1_tarski(A_163, '#skF_4') | r1_tarski(A_163, '#skF_2'('#skF_3', u1_struct_0('#skF_3'))) | v3_tex_2(u1_struct_0('#skF_3'), '#skF_3') | ~v2_tex_2(u1_struct_0('#skF_3'), '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_933])).
% 4.14/1.82  tff(c_971, plain, (~v2_tex_2(u1_struct_0('#skF_3'), '#skF_3')), inference(splitLeft, [status(thm)], [c_954])).
% 4.14/1.82  tff(c_990, plain, (~v1_tdlat_3('#skF_3') | ~l1_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_65, c_971])).
% 4.14/1.82  tff(c_993, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_46, c_990])).
% 4.14/1.82  tff(c_995, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_993])).
% 4.14/1.82  tff(c_997, plain, (v2_tex_2(u1_struct_0('#skF_3'), '#skF_3')), inference(splitRight, [status(thm)], [c_954])).
% 4.14/1.82  tff(c_1028, plain, (![C_211, B_212, A_213]: (C_211=B_212 | ~r1_tarski(B_212, C_211) | ~v2_tex_2(C_211, A_213) | ~m1_subset_1(C_211, k1_zfmisc_1(u1_struct_0(A_213))) | ~v3_tex_2(B_212, A_213) | ~m1_subset_1(B_212, k1_zfmisc_1(u1_struct_0(A_213))) | ~l1_pre_topc(A_213))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.14/1.82  tff(c_1042, plain, (![A_213]: (u1_struct_0('#skF_3')='#skF_4' | ~v2_tex_2(u1_struct_0('#skF_3'), A_213) | ~m1_subset_1(u1_struct_0('#skF_3'), k1_zfmisc_1(u1_struct_0(A_213))) | ~v3_tex_2('#skF_4', A_213) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(A_213))) | ~l1_pre_topc(A_213))), inference(resolution, [status(thm)], [c_625, c_1028])).
% 4.14/1.82  tff(c_1099, plain, (![A_224]: (~v2_tex_2(u1_struct_0('#skF_3'), A_224) | ~m1_subset_1(u1_struct_0('#skF_3'), k1_zfmisc_1(u1_struct_0(A_224))) | ~v3_tex_2('#skF_4', A_224) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(A_224))) | ~l1_pre_topc(A_224))), inference(splitLeft, [status(thm)], [c_1042])).
% 4.14/1.82  tff(c_1103, plain, (~v2_tex_2(u1_struct_0('#skF_3'), '#skF_3') | ~v3_tex_2('#skF_4', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_59, c_1099])).
% 4.14/1.82  tff(c_1107, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_534, c_997, c_1103])).
% 4.14/1.82  tff(c_1108, plain, (u1_struct_0('#skF_3')='#skF_4'), inference(splitRight, [status(thm)], [c_1042])).
% 4.14/1.82  tff(c_711, plain, (![A_156, B_157, B_158, A_159]: (r2_hidden('#skF_1'(A_156, B_157), B_158) | ~r1_tarski(A_159, B_158) | ~m1_subset_1(A_156, k1_zfmisc_1(A_159)) | r1_tarski(A_156, B_157))), inference(resolution, [status(thm)], [c_606, c_2])).
% 4.14/1.82  tff(c_721, plain, (![A_160, B_161]: (r2_hidden('#skF_1'(A_160, B_161), u1_struct_0('#skF_3')) | ~m1_subset_1(A_160, k1_zfmisc_1('#skF_4')) | r1_tarski(A_160, B_161))), inference(resolution, [status(thm)], [c_625, c_711])).
% 4.14/1.82  tff(c_733, plain, (![A_162]: (~m1_subset_1(A_162, k1_zfmisc_1('#skF_4')) | r1_tarski(A_162, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_721, c_4])).
% 4.14/1.82  tff(c_604, plain, (![A_130, B_131, B_2, B_132]: (r2_hidden('#skF_1'(A_130, B_131), B_2) | ~r1_tarski(B_132, B_2) | ~r1_tarski(A_130, B_132) | r1_tarski(A_130, B_131))), inference(resolution, [status(thm)], [c_594, c_2])).
% 4.14/1.82  tff(c_862, plain, (![A_191, B_192, A_193]: (r2_hidden('#skF_1'(A_191, B_192), u1_struct_0('#skF_3')) | ~r1_tarski(A_191, A_193) | r1_tarski(A_191, B_192) | ~m1_subset_1(A_193, k1_zfmisc_1('#skF_4')))), inference(resolution, [status(thm)], [c_733, c_604])).
% 4.14/1.82  tff(c_873, plain, (![B_192]: (r2_hidden('#skF_1'('#skF_4', B_192), u1_struct_0('#skF_3')) | r1_tarski('#skF_4', B_192) | ~m1_subset_1(u1_struct_0('#skF_3'), k1_zfmisc_1('#skF_4')))), inference(resolution, [status(thm)], [c_625, c_862])).
% 4.14/1.82  tff(c_875, plain, (~m1_subset_1(u1_struct_0('#skF_3'), k1_zfmisc_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_873])).
% 4.14/1.82  tff(c_1115, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1108, c_875])).
% 4.14/1.82  tff(c_1138, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_59, c_1115])).
% 4.14/1.82  tff(c_1140, plain, (m1_subset_1(u1_struct_0('#skF_3'), k1_zfmisc_1('#skF_4'))), inference(splitRight, [status(thm)], [c_873])).
% 4.14/1.82  tff(c_617, plain, (![A_133, A_135]: (~m1_subset_1(A_133, k1_zfmisc_1(A_135)) | r1_tarski(A_133, A_135))), inference(resolution, [status(thm)], [c_606, c_4])).
% 4.14/1.82  tff(c_1151, plain, (r1_tarski(u1_struct_0('#skF_3'), '#skF_4')), inference(resolution, [status(thm)], [c_1140, c_617])).
% 4.14/1.82  tff(c_1162, plain, $false, inference(negUnitSimplification, [status(thm)], [c_644, c_1151])).
% 4.14/1.82  tff(c_1163, plain, (u1_struct_0('#skF_3')='#skF_4'), inference(splitRight, [status(thm)], [c_643])).
% 4.14/1.82  tff(c_537, plain, (v1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_534, c_52])).
% 4.14/1.82  tff(c_1166, plain, (v1_subset_1('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1163, c_537])).
% 4.14/1.82  tff(c_1170, plain, $false, inference(negUnitSimplification, [status(thm)], [c_61, c_1166])).
% 4.14/1.82  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.14/1.82  
% 4.14/1.82  Inference rules
% 4.14/1.82  ----------------------
% 4.14/1.82  #Ref     : 0
% 4.14/1.82  #Sup     : 241
% 4.14/1.82  #Fact    : 0
% 4.14/1.82  #Define  : 0
% 4.14/1.82  #Split   : 6
% 4.14/1.82  #Chain   : 0
% 4.14/1.82  #Close   : 0
% 4.14/1.82  
% 4.14/1.82  Ordering : KBO
% 4.14/1.82  
% 4.14/1.82  Simplification rules
% 4.14/1.82  ----------------------
% 4.14/1.82  #Subsume      : 67
% 4.14/1.82  #Demod        : 125
% 4.14/1.82  #Tautology    : 44
% 4.14/1.82  #SimpNegUnit  : 20
% 4.14/1.82  #BackRed      : 29
% 4.14/1.82  
% 4.14/1.82  #Partial instantiations: 0
% 4.14/1.82  #Strategies tried      : 1
% 4.14/1.82  
% 4.14/1.82  Timing (in seconds)
% 4.14/1.82  ----------------------
% 4.14/1.82  Preprocessing        : 0.35
% 4.14/1.82  Parsing              : 0.19
% 4.14/1.82  CNF conversion       : 0.03
% 4.14/1.82  Main loop            : 0.54
% 4.14/1.82  Inferencing          : 0.17
% 4.14/1.82  Reduction            : 0.15
% 4.14/1.82  Demodulation         : 0.10
% 4.14/1.82  BG Simplification    : 0.03
% 4.14/1.82  Subsumption          : 0.17
% 4.14/1.82  Abstraction          : 0.02
% 4.14/1.82  MUC search           : 0.00
% 4.14/1.82  Cooper               : 0.00
% 4.14/1.82  Total                : 0.94
% 4.14/1.82  Index Insertion      : 0.00
% 4.14/1.82  Index Deletion       : 0.00
% 4.14/1.82  Index Matching       : 0.00
% 4.14/1.82  BG Taut test         : 0.00
%------------------------------------------------------------------------------
