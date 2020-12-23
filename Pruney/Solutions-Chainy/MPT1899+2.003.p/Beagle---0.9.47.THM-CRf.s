%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:35 EST 2020

% Result     : Theorem 7.53s
% Output     : CNFRefutation 7.87s
% Verified   : 
% Statistics : Number of formulae       :  131 (5126 expanded)
%              Number of leaves         :   29 (1835 expanded)
%              Depth                    :   37
%              Number of atoms          :  561 (35981 expanded)
%              Number of equality atoms :    5 ( 597 expanded)
%              Maximal formula depth    :   19 (   6 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_tex_2 > v3_tex_2 > v2_tex_2 > r1_tarski > m1_subset_1 > m1_pre_topc > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_tdlat_3 > v1_pre_topc > l1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(v4_tex_2,type,(
    v4_tex_2: ( $i * $i ) > $o )).

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

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v3_tdlat_3,type,(
    v3_tdlat_3: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_163,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & v3_tdlat_3(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & v1_tdlat_3(B)
              & m1_pre_topc(B,A) )
           => ? [C] :
                ( ~ v2_struct_0(C)
                & v1_pre_topc(C)
                & m1_pre_topc(C,A)
                & m1_pre_topc(B,C)
                & v4_tex_2(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_tex_2)).

tff(f_32,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_66,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & m1_pre_topc(B,A) )
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( C = u1_struct_0(B)
               => ( v2_tex_2(C,A)
                <=> v1_tdlat_3(B) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_tex_2)).

tff(f_133,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & v3_tdlat_3(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ~ ( v2_tex_2(B,A)
              & ! [C] :
                  ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
                 => ~ ( r1_tarski(B,C)
                      & v3_tex_2(C,A) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tex_2)).

tff(f_110,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
         => ~ ( v3_tex_2(B,A)
              & ! [C] :
                  ( ( ~ v2_struct_0(C)
                    & v1_pre_topc(C)
                    & m1_pre_topc(C,A) )
                 => ~ ( v4_tex_2(C,A)
                      & B = u1_struct_0(C) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_tex_2)).

tff(f_46,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_pre_topc(C,A)
             => ( r1_tarski(u1_struct_0(B),u1_struct_0(C))
              <=> m1_pre_topc(B,C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_tsep_1)).

tff(f_81,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( v1_xboole_0(B)
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
         => ~ v3_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_tex_2)).

tff(c_44,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_38,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_32,plain,(
    m1_pre_topc('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_2,plain,(
    ! [B_3,A_1] :
      ( m1_subset_1(u1_struct_0(B_3),k1_zfmisc_1(u1_struct_0(A_1)))
      | ~ m1_pre_topc(B_3,A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_42,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_40,plain,(
    v3_tdlat_3('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_36,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_34,plain,(
    v1_tdlat_3('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_97,plain,(
    ! [B_68,A_69] :
      ( v2_tex_2(u1_struct_0(B_68),A_69)
      | ~ v1_tdlat_3(B_68)
      | ~ m1_subset_1(u1_struct_0(B_68),k1_zfmisc_1(u1_struct_0(A_69)))
      | ~ m1_pre_topc(B_68,A_69)
      | v2_struct_0(B_68)
      | ~ l1_pre_topc(A_69)
      | v2_struct_0(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_101,plain,(
    ! [B_3,A_1] :
      ( v2_tex_2(u1_struct_0(B_3),A_1)
      | ~ v1_tdlat_3(B_3)
      | v2_struct_0(B_3)
      | v2_struct_0(A_1)
      | ~ m1_pre_topc(B_3,A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(resolution,[status(thm)],[c_2,c_97])).

tff(c_111,plain,(
    ! [A_74,B_75] :
      ( m1_subset_1('#skF_2'(A_74,B_75),k1_zfmisc_1(u1_struct_0(A_74)))
      | ~ v2_tex_2(B_75,A_74)
      | ~ m1_subset_1(B_75,k1_zfmisc_1(u1_struct_0(A_74)))
      | ~ l1_pre_topc(A_74)
      | ~ v3_tdlat_3(A_74)
      | ~ v2_pre_topc(A_74)
      | v2_struct_0(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_18,plain,(
    ! [A_21,B_25] :
      ( m1_pre_topc('#skF_1'(A_21,B_25),A_21)
      | ~ v3_tex_2(B_25,A_21)
      | ~ m1_subset_1(B_25,k1_zfmisc_1(u1_struct_0(A_21)))
      | v1_xboole_0(B_25)
      | ~ l1_pre_topc(A_21)
      | ~ v2_pre_topc(A_21)
      | v2_struct_0(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_303,plain,(
    ! [A_111,B_112] :
      ( m1_pre_topc('#skF_1'(A_111,'#skF_2'(A_111,B_112)),A_111)
      | ~ v3_tex_2('#skF_2'(A_111,B_112),A_111)
      | v1_xboole_0('#skF_2'(A_111,B_112))
      | ~ v2_tex_2(B_112,A_111)
      | ~ m1_subset_1(B_112,k1_zfmisc_1(u1_struct_0(A_111)))
      | ~ l1_pre_topc(A_111)
      | ~ v3_tdlat_3(A_111)
      | ~ v2_pre_topc(A_111)
      | v2_struct_0(A_111) ) ),
    inference(resolution,[status(thm)],[c_111,c_18])).

tff(c_311,plain,(
    ! [A_1,B_3] :
      ( m1_pre_topc('#skF_1'(A_1,'#skF_2'(A_1,u1_struct_0(B_3))),A_1)
      | ~ v3_tex_2('#skF_2'(A_1,u1_struct_0(B_3)),A_1)
      | v1_xboole_0('#skF_2'(A_1,u1_struct_0(B_3)))
      | ~ v2_tex_2(u1_struct_0(B_3),A_1)
      | ~ v3_tdlat_3(A_1)
      | ~ v2_pre_topc(A_1)
      | v2_struct_0(A_1)
      | ~ m1_pre_topc(B_3,A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(resolution,[status(thm)],[c_2,c_303])).

tff(c_82,plain,(
    ! [B_60,A_61] :
      ( r1_tarski(B_60,'#skF_2'(A_61,B_60))
      | ~ v2_tex_2(B_60,A_61)
      | ~ m1_subset_1(B_60,k1_zfmisc_1(u1_struct_0(A_61)))
      | ~ l1_pre_topc(A_61)
      | ~ v3_tdlat_3(A_61)
      | ~ v2_pre_topc(A_61)
      | v2_struct_0(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_85,plain,(
    ! [B_3,A_1] :
      ( r1_tarski(u1_struct_0(B_3),'#skF_2'(A_1,u1_struct_0(B_3)))
      | ~ v2_tex_2(u1_struct_0(B_3),A_1)
      | ~ v3_tdlat_3(A_1)
      | ~ v2_pre_topc(A_1)
      | v2_struct_0(A_1)
      | ~ m1_pre_topc(B_3,A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(resolution,[status(thm)],[c_2,c_82])).

tff(c_14,plain,(
    ! [A_21,B_25] :
      ( u1_struct_0('#skF_1'(A_21,B_25)) = B_25
      | ~ v3_tex_2(B_25,A_21)
      | ~ m1_subset_1(B_25,k1_zfmisc_1(u1_struct_0(A_21)))
      | v1_xboole_0(B_25)
      | ~ l1_pre_topc(A_21)
      | ~ v2_pre_topc(A_21)
      | v2_struct_0(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_312,plain,(
    ! [A_113,B_114] :
      ( u1_struct_0('#skF_1'(A_113,'#skF_2'(A_113,B_114))) = '#skF_2'(A_113,B_114)
      | ~ v3_tex_2('#skF_2'(A_113,B_114),A_113)
      | v1_xboole_0('#skF_2'(A_113,B_114))
      | ~ v2_tex_2(B_114,A_113)
      | ~ m1_subset_1(B_114,k1_zfmisc_1(u1_struct_0(A_113)))
      | ~ l1_pre_topc(A_113)
      | ~ v3_tdlat_3(A_113)
      | ~ v2_pre_topc(A_113)
      | v2_struct_0(A_113) ) ),
    inference(resolution,[status(thm)],[c_111,c_14])).

tff(c_408,plain,(
    ! [A_136,B_137] :
      ( u1_struct_0('#skF_1'(A_136,'#skF_2'(A_136,u1_struct_0(B_137)))) = '#skF_2'(A_136,u1_struct_0(B_137))
      | ~ v3_tex_2('#skF_2'(A_136,u1_struct_0(B_137)),A_136)
      | v1_xboole_0('#skF_2'(A_136,u1_struct_0(B_137)))
      | ~ v2_tex_2(u1_struct_0(B_137),A_136)
      | ~ v3_tdlat_3(A_136)
      | ~ v2_pre_topc(A_136)
      | v2_struct_0(A_136)
      | ~ m1_pre_topc(B_137,A_136)
      | ~ l1_pre_topc(A_136) ) ),
    inference(resolution,[status(thm)],[c_2,c_312])).

tff(c_6,plain,(
    ! [B_8,C_10,A_4] :
      ( m1_pre_topc(B_8,C_10)
      | ~ r1_tarski(u1_struct_0(B_8),u1_struct_0(C_10))
      | ~ m1_pre_topc(C_10,A_4)
      | ~ m1_pre_topc(B_8,A_4)
      | ~ l1_pre_topc(A_4)
      | ~ v2_pre_topc(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_2449,plain,(
    ! [B_330,A_331,B_332,A_333] :
      ( m1_pre_topc(B_330,'#skF_1'(A_331,'#skF_2'(A_331,u1_struct_0(B_332))))
      | ~ r1_tarski(u1_struct_0(B_330),'#skF_2'(A_331,u1_struct_0(B_332)))
      | ~ m1_pre_topc('#skF_1'(A_331,'#skF_2'(A_331,u1_struct_0(B_332))),A_333)
      | ~ m1_pre_topc(B_330,A_333)
      | ~ l1_pre_topc(A_333)
      | ~ v2_pre_topc(A_333)
      | ~ v3_tex_2('#skF_2'(A_331,u1_struct_0(B_332)),A_331)
      | v1_xboole_0('#skF_2'(A_331,u1_struct_0(B_332)))
      | ~ v2_tex_2(u1_struct_0(B_332),A_331)
      | ~ v3_tdlat_3(A_331)
      | ~ v2_pre_topc(A_331)
      | v2_struct_0(A_331)
      | ~ m1_pre_topc(B_332,A_331)
      | ~ l1_pre_topc(A_331) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_408,c_6])).

tff(c_2479,plain,(
    ! [B_334,A_335,A_336] :
      ( m1_pre_topc(B_334,'#skF_1'(A_335,'#skF_2'(A_335,u1_struct_0(B_334))))
      | ~ m1_pre_topc('#skF_1'(A_335,'#skF_2'(A_335,u1_struct_0(B_334))),A_336)
      | ~ m1_pre_topc(B_334,A_336)
      | ~ l1_pre_topc(A_336)
      | ~ v2_pre_topc(A_336)
      | ~ v3_tex_2('#skF_2'(A_335,u1_struct_0(B_334)),A_335)
      | v1_xboole_0('#skF_2'(A_335,u1_struct_0(B_334)))
      | ~ v2_tex_2(u1_struct_0(B_334),A_335)
      | ~ v3_tdlat_3(A_335)
      | ~ v2_pre_topc(A_335)
      | v2_struct_0(A_335)
      | ~ m1_pre_topc(B_334,A_335)
      | ~ l1_pre_topc(A_335) ) ),
    inference(resolution,[status(thm)],[c_85,c_2449])).

tff(c_2515,plain,(
    ! [B_339,A_340] :
      ( m1_pre_topc(B_339,'#skF_1'(A_340,'#skF_2'(A_340,u1_struct_0(B_339))))
      | ~ v3_tex_2('#skF_2'(A_340,u1_struct_0(B_339)),A_340)
      | v1_xboole_0('#skF_2'(A_340,u1_struct_0(B_339)))
      | ~ v2_tex_2(u1_struct_0(B_339),A_340)
      | ~ v3_tdlat_3(A_340)
      | ~ v2_pre_topc(A_340)
      | v2_struct_0(A_340)
      | ~ m1_pre_topc(B_339,A_340)
      | ~ l1_pre_topc(A_340) ) ),
    inference(resolution,[status(thm)],[c_311,c_2479])).

tff(c_783,plain,(
    ! [A_189,B_190,A_191] :
      ( m1_subset_1('#skF_2'(A_189,u1_struct_0(B_190)),k1_zfmisc_1(u1_struct_0(A_191)))
      | ~ m1_pre_topc('#skF_1'(A_189,'#skF_2'(A_189,u1_struct_0(B_190))),A_191)
      | ~ l1_pre_topc(A_191)
      | ~ v3_tex_2('#skF_2'(A_189,u1_struct_0(B_190)),A_189)
      | v1_xboole_0('#skF_2'(A_189,u1_struct_0(B_190)))
      | ~ v2_tex_2(u1_struct_0(B_190),A_189)
      | ~ v3_tdlat_3(A_189)
      | ~ v2_pre_topc(A_189)
      | v2_struct_0(A_189)
      | ~ m1_pre_topc(B_190,A_189)
      | ~ l1_pre_topc(A_189) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_408,c_2])).

tff(c_791,plain,(
    ! [A_192,B_193] :
      ( m1_subset_1('#skF_2'(A_192,u1_struct_0(B_193)),k1_zfmisc_1(u1_struct_0(A_192)))
      | ~ v3_tex_2('#skF_2'(A_192,u1_struct_0(B_193)),A_192)
      | v1_xboole_0('#skF_2'(A_192,u1_struct_0(B_193)))
      | ~ v2_tex_2(u1_struct_0(B_193),A_192)
      | ~ v3_tdlat_3(A_192)
      | ~ v2_pre_topc(A_192)
      | v2_struct_0(A_192)
      | ~ m1_pre_topc(B_193,A_192)
      | ~ l1_pre_topc(A_192) ) ),
    inference(resolution,[status(thm)],[c_311,c_783])).

tff(c_16,plain,(
    ! [A_21,B_25] :
      ( v4_tex_2('#skF_1'(A_21,B_25),A_21)
      | ~ v3_tex_2(B_25,A_21)
      | ~ m1_subset_1(B_25,k1_zfmisc_1(u1_struct_0(A_21)))
      | v1_xboole_0(B_25)
      | ~ l1_pre_topc(A_21)
      | ~ v2_pre_topc(A_21)
      | v2_struct_0(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_866,plain,(
    ! [A_199,B_200] :
      ( v4_tex_2('#skF_1'(A_199,'#skF_2'(A_199,u1_struct_0(B_200))),A_199)
      | ~ v3_tex_2('#skF_2'(A_199,u1_struct_0(B_200)),A_199)
      | v1_xboole_0('#skF_2'(A_199,u1_struct_0(B_200)))
      | ~ v2_tex_2(u1_struct_0(B_200),A_199)
      | ~ v3_tdlat_3(A_199)
      | ~ v2_pre_topc(A_199)
      | v2_struct_0(A_199)
      | ~ m1_pre_topc(B_200,A_199)
      | ~ l1_pre_topc(A_199) ) ),
    inference(resolution,[status(thm)],[c_791,c_16])).

tff(c_30,plain,(
    ! [C_37] :
      ( ~ v4_tex_2(C_37,'#skF_3')
      | ~ m1_pre_topc('#skF_4',C_37)
      | ~ m1_pre_topc(C_37,'#skF_3')
      | ~ v1_pre_topc(C_37)
      | v2_struct_0(C_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_870,plain,(
    ! [B_200] :
      ( ~ m1_pre_topc('#skF_4','#skF_1'('#skF_3','#skF_2'('#skF_3',u1_struct_0(B_200))))
      | ~ m1_pre_topc('#skF_1'('#skF_3','#skF_2'('#skF_3',u1_struct_0(B_200))),'#skF_3')
      | ~ v1_pre_topc('#skF_1'('#skF_3','#skF_2'('#skF_3',u1_struct_0(B_200))))
      | v2_struct_0('#skF_1'('#skF_3','#skF_2'('#skF_3',u1_struct_0(B_200))))
      | ~ v3_tex_2('#skF_2'('#skF_3',u1_struct_0(B_200)),'#skF_3')
      | v1_xboole_0('#skF_2'('#skF_3',u1_struct_0(B_200)))
      | ~ v2_tex_2(u1_struct_0(B_200),'#skF_3')
      | ~ v3_tdlat_3('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(B_200,'#skF_3')
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_866,c_30])).

tff(c_879,plain,(
    ! [B_200] :
      ( ~ m1_pre_topc('#skF_4','#skF_1'('#skF_3','#skF_2'('#skF_3',u1_struct_0(B_200))))
      | ~ m1_pre_topc('#skF_1'('#skF_3','#skF_2'('#skF_3',u1_struct_0(B_200))),'#skF_3')
      | ~ v1_pre_topc('#skF_1'('#skF_3','#skF_2'('#skF_3',u1_struct_0(B_200))))
      | v2_struct_0('#skF_1'('#skF_3','#skF_2'('#skF_3',u1_struct_0(B_200))))
      | ~ v3_tex_2('#skF_2'('#skF_3',u1_struct_0(B_200)),'#skF_3')
      | v1_xboole_0('#skF_2'('#skF_3',u1_struct_0(B_200)))
      | ~ v2_tex_2(u1_struct_0(B_200),'#skF_3')
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(B_200,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_42,c_40,c_870])).

tff(c_896,plain,(
    ! [B_203] :
      ( ~ m1_pre_topc('#skF_4','#skF_1'('#skF_3','#skF_2'('#skF_3',u1_struct_0(B_203))))
      | ~ m1_pre_topc('#skF_1'('#skF_3','#skF_2'('#skF_3',u1_struct_0(B_203))),'#skF_3')
      | ~ v1_pre_topc('#skF_1'('#skF_3','#skF_2'('#skF_3',u1_struct_0(B_203))))
      | v2_struct_0('#skF_1'('#skF_3','#skF_2'('#skF_3',u1_struct_0(B_203))))
      | ~ v3_tex_2('#skF_2'('#skF_3',u1_struct_0(B_203)),'#skF_3')
      | v1_xboole_0('#skF_2'('#skF_3',u1_struct_0(B_203)))
      | ~ v2_tex_2(u1_struct_0(B_203),'#skF_3')
      | ~ m1_pre_topc(B_203,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_879])).

tff(c_903,plain,(
    ! [B_3] :
      ( ~ m1_pre_topc('#skF_4','#skF_1'('#skF_3','#skF_2'('#skF_3',u1_struct_0(B_3))))
      | ~ v1_pre_topc('#skF_1'('#skF_3','#skF_2'('#skF_3',u1_struct_0(B_3))))
      | v2_struct_0('#skF_1'('#skF_3','#skF_2'('#skF_3',u1_struct_0(B_3))))
      | ~ v3_tex_2('#skF_2'('#skF_3',u1_struct_0(B_3)),'#skF_3')
      | v1_xboole_0('#skF_2'('#skF_3',u1_struct_0(B_3)))
      | ~ v2_tex_2(u1_struct_0(B_3),'#skF_3')
      | ~ v3_tdlat_3('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(B_3,'#skF_3')
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_311,c_896])).

tff(c_909,plain,(
    ! [B_3] :
      ( ~ m1_pre_topc('#skF_4','#skF_1'('#skF_3','#skF_2'('#skF_3',u1_struct_0(B_3))))
      | ~ v1_pre_topc('#skF_1'('#skF_3','#skF_2'('#skF_3',u1_struct_0(B_3))))
      | v2_struct_0('#skF_1'('#skF_3','#skF_2'('#skF_3',u1_struct_0(B_3))))
      | ~ v3_tex_2('#skF_2'('#skF_3',u1_struct_0(B_3)),'#skF_3')
      | v1_xboole_0('#skF_2'('#skF_3',u1_struct_0(B_3)))
      | ~ v2_tex_2(u1_struct_0(B_3),'#skF_3')
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(B_3,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_42,c_40,c_903])).

tff(c_910,plain,(
    ! [B_3] :
      ( ~ m1_pre_topc('#skF_4','#skF_1'('#skF_3','#skF_2'('#skF_3',u1_struct_0(B_3))))
      | ~ v1_pre_topc('#skF_1'('#skF_3','#skF_2'('#skF_3',u1_struct_0(B_3))))
      | v2_struct_0('#skF_1'('#skF_3','#skF_2'('#skF_3',u1_struct_0(B_3))))
      | ~ v3_tex_2('#skF_2'('#skF_3',u1_struct_0(B_3)),'#skF_3')
      | v1_xboole_0('#skF_2'('#skF_3',u1_struct_0(B_3)))
      | ~ v2_tex_2(u1_struct_0(B_3),'#skF_3')
      | ~ m1_pre_topc(B_3,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_909])).

tff(c_2535,plain,
    ( ~ v1_pre_topc('#skF_1'('#skF_3','#skF_2'('#skF_3',u1_struct_0('#skF_4'))))
    | v2_struct_0('#skF_1'('#skF_3','#skF_2'('#skF_3',u1_struct_0('#skF_4'))))
    | ~ v3_tex_2('#skF_2'('#skF_3',u1_struct_0('#skF_4')),'#skF_3')
    | v1_xboole_0('#skF_2'('#skF_3',u1_struct_0('#skF_4')))
    | ~ v2_tex_2(u1_struct_0('#skF_4'),'#skF_3')
    | ~ v3_tdlat_3('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_2515,c_910])).

tff(c_2577,plain,
    ( ~ v1_pre_topc('#skF_1'('#skF_3','#skF_2'('#skF_3',u1_struct_0('#skF_4'))))
    | v2_struct_0('#skF_1'('#skF_3','#skF_2'('#skF_3',u1_struct_0('#skF_4'))))
    | ~ v3_tex_2('#skF_2'('#skF_3',u1_struct_0('#skF_4')),'#skF_3')
    | v1_xboole_0('#skF_2'('#skF_3',u1_struct_0('#skF_4')))
    | ~ v2_tex_2(u1_struct_0('#skF_4'),'#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_32,c_42,c_40,c_2535])).

tff(c_2578,plain,
    ( ~ v1_pre_topc('#skF_1'('#skF_3','#skF_2'('#skF_3',u1_struct_0('#skF_4'))))
    | v2_struct_0('#skF_1'('#skF_3','#skF_2'('#skF_3',u1_struct_0('#skF_4'))))
    | ~ v3_tex_2('#skF_2'('#skF_3',u1_struct_0('#skF_4')),'#skF_3')
    | v1_xboole_0('#skF_2'('#skF_3',u1_struct_0('#skF_4')))
    | ~ v2_tex_2(u1_struct_0('#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_2577])).

tff(c_2586,plain,(
    ~ v2_tex_2(u1_struct_0('#skF_4'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_2578])).

tff(c_2589,plain,
    ( ~ v1_tdlat_3('#skF_4')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_101,c_2586])).

tff(c_2592,plain,
    ( v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_32,c_34,c_2589])).

tff(c_2594,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_36,c_2592])).

tff(c_2596,plain,(
    v2_tex_2(u1_struct_0('#skF_4'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_2578])).

tff(c_74,plain,(
    ! [A_56,B_57] :
      ( v3_tex_2('#skF_2'(A_56,B_57),A_56)
      | ~ v2_tex_2(B_57,A_56)
      | ~ m1_subset_1(B_57,k1_zfmisc_1(u1_struct_0(A_56)))
      | ~ l1_pre_topc(A_56)
      | ~ v3_tdlat_3(A_56)
      | ~ v2_pre_topc(A_56)
      | v2_struct_0(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_77,plain,(
    ! [A_1,B_3] :
      ( v3_tex_2('#skF_2'(A_1,u1_struct_0(B_3)),A_1)
      | ~ v2_tex_2(u1_struct_0(B_3),A_1)
      | ~ v3_tdlat_3(A_1)
      | ~ v2_pre_topc(A_1)
      | v2_struct_0(A_1)
      | ~ m1_pre_topc(B_3,A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(resolution,[status(thm)],[c_2,c_74])).

tff(c_20,plain,(
    ! [A_21,B_25] :
      ( v1_pre_topc('#skF_1'(A_21,B_25))
      | ~ v3_tex_2(B_25,A_21)
      | ~ m1_subset_1(B_25,k1_zfmisc_1(u1_struct_0(A_21)))
      | v1_xboole_0(B_25)
      | ~ l1_pre_topc(A_21)
      | ~ v2_pre_topc(A_21)
      | v2_struct_0(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_284,plain,(
    ! [A_105,B_106] :
      ( v1_pre_topc('#skF_1'(A_105,'#skF_2'(A_105,B_106)))
      | ~ v3_tex_2('#skF_2'(A_105,B_106),A_105)
      | v1_xboole_0('#skF_2'(A_105,B_106))
      | ~ v2_tex_2(B_106,A_105)
      | ~ m1_subset_1(B_106,k1_zfmisc_1(u1_struct_0(A_105)))
      | ~ l1_pre_topc(A_105)
      | ~ v3_tdlat_3(A_105)
      | ~ v2_pre_topc(A_105)
      | v2_struct_0(A_105) ) ),
    inference(resolution,[status(thm)],[c_111,c_20])).

tff(c_292,plain,(
    ! [A_1,B_3] :
      ( v1_pre_topc('#skF_1'(A_1,'#skF_2'(A_1,u1_struct_0(B_3))))
      | ~ v3_tex_2('#skF_2'(A_1,u1_struct_0(B_3)),A_1)
      | v1_xboole_0('#skF_2'(A_1,u1_struct_0(B_3)))
      | ~ v2_tex_2(u1_struct_0(B_3),A_1)
      | ~ v3_tdlat_3(A_1)
      | ~ v2_pre_topc(A_1)
      | v2_struct_0(A_1)
      | ~ m1_pre_topc(B_3,A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(resolution,[status(thm)],[c_2,c_284])).

tff(c_2595,plain,
    ( ~ v3_tex_2('#skF_2'('#skF_3',u1_struct_0('#skF_4')),'#skF_3')
    | ~ v1_pre_topc('#skF_1'('#skF_3','#skF_2'('#skF_3',u1_struct_0('#skF_4'))))
    | v1_xboole_0('#skF_2'('#skF_3',u1_struct_0('#skF_4')))
    | v2_struct_0('#skF_1'('#skF_3','#skF_2'('#skF_3',u1_struct_0('#skF_4')))) ),
    inference(splitRight,[status(thm)],[c_2578])).

tff(c_2604,plain,(
    ~ v1_pre_topc('#skF_1'('#skF_3','#skF_2'('#skF_3',u1_struct_0('#skF_4')))) ),
    inference(splitLeft,[status(thm)],[c_2595])).

tff(c_2632,plain,
    ( ~ v3_tex_2('#skF_2'('#skF_3',u1_struct_0('#skF_4')),'#skF_3')
    | v1_xboole_0('#skF_2'('#skF_3',u1_struct_0('#skF_4')))
    | ~ v2_tex_2(u1_struct_0('#skF_4'),'#skF_3')
    | ~ v3_tdlat_3('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_292,c_2604])).

tff(c_2635,plain,
    ( ~ v3_tex_2('#skF_2'('#skF_3',u1_struct_0('#skF_4')),'#skF_3')
    | v1_xboole_0('#skF_2'('#skF_3',u1_struct_0('#skF_4')))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_32,c_42,c_40,c_2596,c_2632])).

tff(c_2636,plain,
    ( ~ v3_tex_2('#skF_2'('#skF_3',u1_struct_0('#skF_4')),'#skF_3')
    | v1_xboole_0('#skF_2'('#skF_3',u1_struct_0('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_2635])).

tff(c_2637,plain,(
    ~ v3_tex_2('#skF_2'('#skF_3',u1_struct_0('#skF_4')),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_2636])).

tff(c_2643,plain,
    ( ~ v2_tex_2(u1_struct_0('#skF_4'),'#skF_3')
    | ~ v3_tdlat_3('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_77,c_2637])).

tff(c_2650,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_32,c_42,c_40,c_2596,c_2643])).

tff(c_2652,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_2650])).

tff(c_2653,plain,(
    v1_xboole_0('#skF_2'('#skF_3',u1_struct_0('#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_2636])).

tff(c_12,plain,(
    ! [B_20,A_18] :
      ( ~ v3_tex_2(B_20,A_18)
      | ~ m1_subset_1(B_20,k1_zfmisc_1(u1_struct_0(A_18)))
      | ~ v1_xboole_0(B_20)
      | ~ l1_pre_topc(A_18)
      | ~ v2_pre_topc(A_18)
      | v2_struct_0(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_238,plain,(
    ! [A_90,B_91] :
      ( ~ v3_tex_2('#skF_2'(A_90,B_91),A_90)
      | ~ v1_xboole_0('#skF_2'(A_90,B_91))
      | ~ v2_tex_2(B_91,A_90)
      | ~ m1_subset_1(B_91,k1_zfmisc_1(u1_struct_0(A_90)))
      | ~ l1_pre_topc(A_90)
      | ~ v3_tdlat_3(A_90)
      | ~ v2_pre_topc(A_90)
      | v2_struct_0(A_90) ) ),
    inference(resolution,[status(thm)],[c_111,c_12])).

tff(c_242,plain,(
    ! [A_92,B_93] :
      ( ~ v1_xboole_0('#skF_2'(A_92,u1_struct_0(B_93)))
      | ~ m1_subset_1(u1_struct_0(B_93),k1_zfmisc_1(u1_struct_0(A_92)))
      | ~ v2_tex_2(u1_struct_0(B_93),A_92)
      | ~ v3_tdlat_3(A_92)
      | ~ v2_pre_topc(A_92)
      | v2_struct_0(A_92)
      | ~ m1_pre_topc(B_93,A_92)
      | ~ l1_pre_topc(A_92) ) ),
    inference(resolution,[status(thm)],[c_77,c_238])).

tff(c_252,plain,(
    ! [A_1,B_3] :
      ( ~ v1_xboole_0('#skF_2'(A_1,u1_struct_0(B_3)))
      | ~ v2_tex_2(u1_struct_0(B_3),A_1)
      | ~ v3_tdlat_3(A_1)
      | ~ v2_pre_topc(A_1)
      | v2_struct_0(A_1)
      | ~ m1_pre_topc(B_3,A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(resolution,[status(thm)],[c_2,c_242])).

tff(c_2660,plain,
    ( ~ v2_tex_2(u1_struct_0('#skF_4'),'#skF_3')
    | ~ v3_tdlat_3('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_2653,c_252])).

tff(c_2667,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_32,c_42,c_40,c_2596,c_2660])).

tff(c_2669,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_2667])).

tff(c_2670,plain,
    ( ~ v3_tex_2('#skF_2'('#skF_3',u1_struct_0('#skF_4')),'#skF_3')
    | v2_struct_0('#skF_1'('#skF_3','#skF_2'('#skF_3',u1_struct_0('#skF_4'))))
    | v1_xboole_0('#skF_2'('#skF_3',u1_struct_0('#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_2595])).

tff(c_2672,plain,(
    ~ v3_tex_2('#skF_2'('#skF_3',u1_struct_0('#skF_4')),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_2670])).

tff(c_2678,plain,
    ( ~ v2_tex_2(u1_struct_0('#skF_4'),'#skF_3')
    | ~ v3_tdlat_3('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_77,c_2672])).

tff(c_2685,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_32,c_42,c_40,c_2596,c_2678])).

tff(c_2687,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_2685])).

tff(c_2689,plain,(
    v3_tex_2('#skF_2'('#skF_3',u1_struct_0('#skF_4')),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_2670])).

tff(c_139,plain,(
    ! [A_74,B_75] :
      ( ~ v3_tex_2('#skF_2'(A_74,B_75),A_74)
      | ~ v1_xboole_0('#skF_2'(A_74,B_75))
      | ~ v2_tex_2(B_75,A_74)
      | ~ m1_subset_1(B_75,k1_zfmisc_1(u1_struct_0(A_74)))
      | ~ l1_pre_topc(A_74)
      | ~ v3_tdlat_3(A_74)
      | ~ v2_pre_topc(A_74)
      | v2_struct_0(A_74) ) ),
    inference(resolution,[status(thm)],[c_111,c_12])).

tff(c_2691,plain,
    ( ~ v1_xboole_0('#skF_2'('#skF_3',u1_struct_0('#skF_4')))
    | ~ v2_tex_2(u1_struct_0('#skF_4'),'#skF_3')
    | ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3')
    | ~ v3_tdlat_3('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_2689,c_139])).

tff(c_2694,plain,
    ( ~ v1_xboole_0('#skF_2'('#skF_3',u1_struct_0('#skF_4')))
    | ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_2596,c_2691])).

tff(c_2695,plain,
    ( ~ v1_xboole_0('#skF_2'('#skF_3',u1_struct_0('#skF_4')))
    | ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_2694])).

tff(c_2696,plain,(
    ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_2695])).

tff(c_2724,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_2,c_2696])).

tff(c_2728,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_32,c_2724])).

tff(c_2729,plain,(
    ~ v1_xboole_0('#skF_2'('#skF_3',u1_struct_0('#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_2695])).

tff(c_2494,plain,(
    ! [B_3,A_1] :
      ( m1_pre_topc(B_3,'#skF_1'(A_1,'#skF_2'(A_1,u1_struct_0(B_3))))
      | ~ v3_tex_2('#skF_2'(A_1,u1_struct_0(B_3)),A_1)
      | v1_xboole_0('#skF_2'(A_1,u1_struct_0(B_3)))
      | ~ v2_tex_2(u1_struct_0(B_3),A_1)
      | ~ v3_tdlat_3(A_1)
      | ~ v2_pre_topc(A_1)
      | v2_struct_0(A_1)
      | ~ m1_pre_topc(B_3,A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(resolution,[status(thm)],[c_311,c_2479])).

tff(c_2730,plain,(
    m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_2695])).

tff(c_135,plain,(
    ! [A_74,B_75] :
      ( m1_pre_topc('#skF_1'(A_74,'#skF_2'(A_74,B_75)),A_74)
      | ~ v3_tex_2('#skF_2'(A_74,B_75),A_74)
      | v1_xboole_0('#skF_2'(A_74,B_75))
      | ~ v2_tex_2(B_75,A_74)
      | ~ m1_subset_1(B_75,k1_zfmisc_1(u1_struct_0(A_74)))
      | ~ l1_pre_topc(A_74)
      | ~ v3_tdlat_3(A_74)
      | ~ v2_pre_topc(A_74)
      | v2_struct_0(A_74) ) ),
    inference(resolution,[status(thm)],[c_111,c_18])).

tff(c_2737,plain,
    ( m1_pre_topc('#skF_1'('#skF_3','#skF_2'('#skF_3',u1_struct_0('#skF_4'))),'#skF_3')
    | ~ v3_tex_2('#skF_2'('#skF_3',u1_struct_0('#skF_4')),'#skF_3')
    | v1_xboole_0('#skF_2'('#skF_3',u1_struct_0('#skF_4')))
    | ~ v2_tex_2(u1_struct_0('#skF_4'),'#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v3_tdlat_3('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_2730,c_135])).

tff(c_2770,plain,
    ( m1_pre_topc('#skF_1'('#skF_3','#skF_2'('#skF_3',u1_struct_0('#skF_4'))),'#skF_3')
    | v1_xboole_0('#skF_2'('#skF_3',u1_struct_0('#skF_4')))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_2596,c_2689,c_2737])).

tff(c_2771,plain,(
    m1_pre_topc('#skF_1'('#skF_3','#skF_2'('#skF_3',u1_struct_0('#skF_4'))),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_2729,c_2770])).

tff(c_516,plain,(
    ! [A_136,B_137,A_1] :
      ( m1_subset_1('#skF_2'(A_136,u1_struct_0(B_137)),k1_zfmisc_1(u1_struct_0(A_1)))
      | ~ m1_pre_topc('#skF_1'(A_136,'#skF_2'(A_136,u1_struct_0(B_137))),A_1)
      | ~ l1_pre_topc(A_1)
      | ~ v3_tex_2('#skF_2'(A_136,u1_struct_0(B_137)),A_136)
      | v1_xboole_0('#skF_2'(A_136,u1_struct_0(B_137)))
      | ~ v2_tex_2(u1_struct_0(B_137),A_136)
      | ~ v3_tdlat_3(A_136)
      | ~ v2_pre_topc(A_136)
      | v2_struct_0(A_136)
      | ~ m1_pre_topc(B_137,A_136)
      | ~ l1_pre_topc(A_136) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_408,c_2])).

tff(c_2817,plain,
    ( m1_subset_1('#skF_2'('#skF_3',u1_struct_0('#skF_4')),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ v3_tex_2('#skF_2'('#skF_3',u1_struct_0('#skF_4')),'#skF_3')
    | v1_xboole_0('#skF_2'('#skF_3',u1_struct_0('#skF_4')))
    | ~ v2_tex_2(u1_struct_0('#skF_4'),'#skF_3')
    | ~ v3_tdlat_3('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_2771,c_516])).

tff(c_2826,plain,
    ( m1_subset_1('#skF_2'('#skF_3',u1_struct_0('#skF_4')),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | v1_xboole_0('#skF_2'('#skF_3',u1_struct_0('#skF_4')))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_32,c_42,c_40,c_2596,c_2689,c_2817])).

tff(c_2827,plain,(
    m1_subset_1('#skF_2'('#skF_3',u1_struct_0('#skF_4')),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_2729,c_2826])).

tff(c_22,plain,(
    ! [A_21,B_25] :
      ( ~ v2_struct_0('#skF_1'(A_21,B_25))
      | ~ v3_tex_2(B_25,A_21)
      | ~ m1_subset_1(B_25,k1_zfmisc_1(u1_struct_0(A_21)))
      | v1_xboole_0(B_25)
      | ~ l1_pre_topc(A_21)
      | ~ v2_pre_topc(A_21)
      | v2_struct_0(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_2856,plain,
    ( ~ v2_struct_0('#skF_1'('#skF_3','#skF_2'('#skF_3',u1_struct_0('#skF_4'))))
    | ~ v3_tex_2('#skF_2'('#skF_3',u1_struct_0('#skF_4')),'#skF_3')
    | v1_xboole_0('#skF_2'('#skF_3',u1_struct_0('#skF_4')))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_2827,c_22])).

tff(c_2899,plain,
    ( ~ v2_struct_0('#skF_1'('#skF_3','#skF_2'('#skF_3',u1_struct_0('#skF_4'))))
    | v1_xboole_0('#skF_2'('#skF_3',u1_struct_0('#skF_4')))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_38,c_2689,c_2856])).

tff(c_2900,plain,(
    ~ v2_struct_0('#skF_1'('#skF_3','#skF_2'('#skF_3',u1_struct_0('#skF_4')))) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_2729,c_2899])).

tff(c_2671,plain,(
    v1_pre_topc('#skF_1'('#skF_3','#skF_2'('#skF_3',u1_struct_0('#skF_4')))) ),
    inference(splitRight,[status(thm)],[c_2595])).

tff(c_2841,plain,
    ( v4_tex_2('#skF_1'('#skF_3','#skF_2'('#skF_3',u1_struct_0('#skF_4'))),'#skF_3')
    | ~ v3_tex_2('#skF_2'('#skF_3',u1_struct_0('#skF_4')),'#skF_3')
    | v1_xboole_0('#skF_2'('#skF_3',u1_struct_0('#skF_4')))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_2827,c_16])).

tff(c_2875,plain,
    ( v4_tex_2('#skF_1'('#skF_3','#skF_2'('#skF_3',u1_struct_0('#skF_4'))),'#skF_3')
    | v1_xboole_0('#skF_2'('#skF_3',u1_struct_0('#skF_4')))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_38,c_2689,c_2841])).

tff(c_2876,plain,(
    v4_tex_2('#skF_1'('#skF_3','#skF_2'('#skF_3',u1_struct_0('#skF_4'))),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_2729,c_2875])).

tff(c_2907,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_1'('#skF_3','#skF_2'('#skF_3',u1_struct_0('#skF_4'))))
    | ~ m1_pre_topc('#skF_1'('#skF_3','#skF_2'('#skF_3',u1_struct_0('#skF_4'))),'#skF_3')
    | ~ v1_pre_topc('#skF_1'('#skF_3','#skF_2'('#skF_3',u1_struct_0('#skF_4'))))
    | v2_struct_0('#skF_1'('#skF_3','#skF_2'('#skF_3',u1_struct_0('#skF_4')))) ),
    inference(resolution,[status(thm)],[c_2876,c_30])).

tff(c_2910,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_1'('#skF_3','#skF_2'('#skF_3',u1_struct_0('#skF_4'))))
    | v2_struct_0('#skF_1'('#skF_3','#skF_2'('#skF_3',u1_struct_0('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2671,c_2771,c_2907])).

tff(c_2911,plain,(
    ~ m1_pre_topc('#skF_4','#skF_1'('#skF_3','#skF_2'('#skF_3',u1_struct_0('#skF_4')))) ),
    inference(negUnitSimplification,[status(thm)],[c_2900,c_2910])).

tff(c_2939,plain,
    ( ~ v3_tex_2('#skF_2'('#skF_3',u1_struct_0('#skF_4')),'#skF_3')
    | v1_xboole_0('#skF_2'('#skF_3',u1_struct_0('#skF_4')))
    | ~ v2_tex_2(u1_struct_0('#skF_4'),'#skF_3')
    | ~ v3_tdlat_3('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_2494,c_2911])).

tff(c_2942,plain,
    ( v1_xboole_0('#skF_2'('#skF_3',u1_struct_0('#skF_4')))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_32,c_42,c_40,c_2596,c_2689,c_2939])).

tff(c_2944,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_2729,c_2942])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:19:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.53/2.78  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.53/2.79  
% 7.53/2.79  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.53/2.79  %$ v4_tex_2 > v3_tex_2 > v2_tex_2 > r1_tarski > m1_subset_1 > m1_pre_topc > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_tdlat_3 > v1_pre_topc > l1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 7.53/2.79  
% 7.53/2.79  %Foreground sorts:
% 7.53/2.79  
% 7.53/2.79  
% 7.53/2.79  %Background operators:
% 7.53/2.79  
% 7.53/2.79  
% 7.53/2.79  %Foreground operators:
% 7.53/2.79  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 7.53/2.79  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.53/2.79  tff(v4_tex_2, type, v4_tex_2: ($i * $i) > $o).
% 7.53/2.79  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 7.53/2.79  tff(v1_tdlat_3, type, v1_tdlat_3: $i > $o).
% 7.53/2.79  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.53/2.79  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 7.53/2.79  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 7.53/2.79  tff('#skF_3', type, '#skF_3': $i).
% 7.53/2.79  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 7.53/2.79  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.53/2.79  tff(v3_tdlat_3, type, v3_tdlat_3: $i > $o).
% 7.53/2.79  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.53/2.79  tff('#skF_4', type, '#skF_4': $i).
% 7.53/2.79  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.53/2.79  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 7.53/2.79  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 7.53/2.79  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 7.53/2.79  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 7.53/2.79  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 7.53/2.79  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 7.53/2.79  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.53/2.79  
% 7.87/2.81  tff(f_163, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v1_tdlat_3(B)) & m1_pre_topc(B, A)) => (?[C]: ((((~v2_struct_0(C) & v1_pre_topc(C)) & m1_pre_topc(C, A)) & m1_pre_topc(B, C)) & v4_tex_2(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_tex_2)).
% 7.87/2.81  tff(f_32, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 7.87/2.81  tff(f_66, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => (v2_tex_2(C, A) <=> v1_tdlat_3(B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_tex_2)).
% 7.87/2.81  tff(f_133, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ~(v2_tex_2(B, A) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r1_tarski(B, C) & v3_tex_2(C, A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_tex_2)).
% 7.87/2.81  tff(f_110, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ~(v3_tex_2(B, A) & (![C]: (((~v2_struct_0(C) & v1_pre_topc(C)) & m1_pre_topc(C, A)) => ~(v4_tex_2(C, A) & (B = u1_struct_0(C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t53_tex_2)).
% 7.87/2.81  tff(f_46, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_pre_topc(C, A) => (r1_tarski(u1_struct_0(B), u1_struct_0(C)) <=> m1_pre_topc(B, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_tsep_1)).
% 7.87/2.81  tff(f_81, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ~v3_tex_2(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_tex_2)).
% 7.87/2.81  tff(c_44, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_163])).
% 7.87/2.81  tff(c_38, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_163])).
% 7.87/2.81  tff(c_32, plain, (m1_pre_topc('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_163])).
% 7.87/2.81  tff(c_2, plain, (![B_3, A_1]: (m1_subset_1(u1_struct_0(B_3), k1_zfmisc_1(u1_struct_0(A_1))) | ~m1_pre_topc(B_3, A_1) | ~l1_pre_topc(A_1))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.87/2.81  tff(c_42, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_163])).
% 7.87/2.81  tff(c_40, plain, (v3_tdlat_3('#skF_3')), inference(cnfTransformation, [status(thm)], [f_163])).
% 7.87/2.81  tff(c_36, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_163])).
% 7.87/2.81  tff(c_34, plain, (v1_tdlat_3('#skF_4')), inference(cnfTransformation, [status(thm)], [f_163])).
% 7.87/2.81  tff(c_97, plain, (![B_68, A_69]: (v2_tex_2(u1_struct_0(B_68), A_69) | ~v1_tdlat_3(B_68) | ~m1_subset_1(u1_struct_0(B_68), k1_zfmisc_1(u1_struct_0(A_69))) | ~m1_pre_topc(B_68, A_69) | v2_struct_0(B_68) | ~l1_pre_topc(A_69) | v2_struct_0(A_69))), inference(cnfTransformation, [status(thm)], [f_66])).
% 7.87/2.81  tff(c_101, plain, (![B_3, A_1]: (v2_tex_2(u1_struct_0(B_3), A_1) | ~v1_tdlat_3(B_3) | v2_struct_0(B_3) | v2_struct_0(A_1) | ~m1_pre_topc(B_3, A_1) | ~l1_pre_topc(A_1))), inference(resolution, [status(thm)], [c_2, c_97])).
% 7.87/2.81  tff(c_111, plain, (![A_74, B_75]: (m1_subset_1('#skF_2'(A_74, B_75), k1_zfmisc_1(u1_struct_0(A_74))) | ~v2_tex_2(B_75, A_74) | ~m1_subset_1(B_75, k1_zfmisc_1(u1_struct_0(A_74))) | ~l1_pre_topc(A_74) | ~v3_tdlat_3(A_74) | ~v2_pre_topc(A_74) | v2_struct_0(A_74))), inference(cnfTransformation, [status(thm)], [f_133])).
% 7.87/2.81  tff(c_18, plain, (![A_21, B_25]: (m1_pre_topc('#skF_1'(A_21, B_25), A_21) | ~v3_tex_2(B_25, A_21) | ~m1_subset_1(B_25, k1_zfmisc_1(u1_struct_0(A_21))) | v1_xboole_0(B_25) | ~l1_pre_topc(A_21) | ~v2_pre_topc(A_21) | v2_struct_0(A_21))), inference(cnfTransformation, [status(thm)], [f_110])).
% 7.87/2.81  tff(c_303, plain, (![A_111, B_112]: (m1_pre_topc('#skF_1'(A_111, '#skF_2'(A_111, B_112)), A_111) | ~v3_tex_2('#skF_2'(A_111, B_112), A_111) | v1_xboole_0('#skF_2'(A_111, B_112)) | ~v2_tex_2(B_112, A_111) | ~m1_subset_1(B_112, k1_zfmisc_1(u1_struct_0(A_111))) | ~l1_pre_topc(A_111) | ~v3_tdlat_3(A_111) | ~v2_pre_topc(A_111) | v2_struct_0(A_111))), inference(resolution, [status(thm)], [c_111, c_18])).
% 7.87/2.81  tff(c_311, plain, (![A_1, B_3]: (m1_pre_topc('#skF_1'(A_1, '#skF_2'(A_1, u1_struct_0(B_3))), A_1) | ~v3_tex_2('#skF_2'(A_1, u1_struct_0(B_3)), A_1) | v1_xboole_0('#skF_2'(A_1, u1_struct_0(B_3))) | ~v2_tex_2(u1_struct_0(B_3), A_1) | ~v3_tdlat_3(A_1) | ~v2_pre_topc(A_1) | v2_struct_0(A_1) | ~m1_pre_topc(B_3, A_1) | ~l1_pre_topc(A_1))), inference(resolution, [status(thm)], [c_2, c_303])).
% 7.87/2.81  tff(c_82, plain, (![B_60, A_61]: (r1_tarski(B_60, '#skF_2'(A_61, B_60)) | ~v2_tex_2(B_60, A_61) | ~m1_subset_1(B_60, k1_zfmisc_1(u1_struct_0(A_61))) | ~l1_pre_topc(A_61) | ~v3_tdlat_3(A_61) | ~v2_pre_topc(A_61) | v2_struct_0(A_61))), inference(cnfTransformation, [status(thm)], [f_133])).
% 7.87/2.81  tff(c_85, plain, (![B_3, A_1]: (r1_tarski(u1_struct_0(B_3), '#skF_2'(A_1, u1_struct_0(B_3))) | ~v2_tex_2(u1_struct_0(B_3), A_1) | ~v3_tdlat_3(A_1) | ~v2_pre_topc(A_1) | v2_struct_0(A_1) | ~m1_pre_topc(B_3, A_1) | ~l1_pre_topc(A_1))), inference(resolution, [status(thm)], [c_2, c_82])).
% 7.87/2.81  tff(c_14, plain, (![A_21, B_25]: (u1_struct_0('#skF_1'(A_21, B_25))=B_25 | ~v3_tex_2(B_25, A_21) | ~m1_subset_1(B_25, k1_zfmisc_1(u1_struct_0(A_21))) | v1_xboole_0(B_25) | ~l1_pre_topc(A_21) | ~v2_pre_topc(A_21) | v2_struct_0(A_21))), inference(cnfTransformation, [status(thm)], [f_110])).
% 7.87/2.81  tff(c_312, plain, (![A_113, B_114]: (u1_struct_0('#skF_1'(A_113, '#skF_2'(A_113, B_114)))='#skF_2'(A_113, B_114) | ~v3_tex_2('#skF_2'(A_113, B_114), A_113) | v1_xboole_0('#skF_2'(A_113, B_114)) | ~v2_tex_2(B_114, A_113) | ~m1_subset_1(B_114, k1_zfmisc_1(u1_struct_0(A_113))) | ~l1_pre_topc(A_113) | ~v3_tdlat_3(A_113) | ~v2_pre_topc(A_113) | v2_struct_0(A_113))), inference(resolution, [status(thm)], [c_111, c_14])).
% 7.87/2.81  tff(c_408, plain, (![A_136, B_137]: (u1_struct_0('#skF_1'(A_136, '#skF_2'(A_136, u1_struct_0(B_137))))='#skF_2'(A_136, u1_struct_0(B_137)) | ~v3_tex_2('#skF_2'(A_136, u1_struct_0(B_137)), A_136) | v1_xboole_0('#skF_2'(A_136, u1_struct_0(B_137))) | ~v2_tex_2(u1_struct_0(B_137), A_136) | ~v3_tdlat_3(A_136) | ~v2_pre_topc(A_136) | v2_struct_0(A_136) | ~m1_pre_topc(B_137, A_136) | ~l1_pre_topc(A_136))), inference(resolution, [status(thm)], [c_2, c_312])).
% 7.87/2.81  tff(c_6, plain, (![B_8, C_10, A_4]: (m1_pre_topc(B_8, C_10) | ~r1_tarski(u1_struct_0(B_8), u1_struct_0(C_10)) | ~m1_pre_topc(C_10, A_4) | ~m1_pre_topc(B_8, A_4) | ~l1_pre_topc(A_4) | ~v2_pre_topc(A_4))), inference(cnfTransformation, [status(thm)], [f_46])).
% 7.87/2.81  tff(c_2449, plain, (![B_330, A_331, B_332, A_333]: (m1_pre_topc(B_330, '#skF_1'(A_331, '#skF_2'(A_331, u1_struct_0(B_332)))) | ~r1_tarski(u1_struct_0(B_330), '#skF_2'(A_331, u1_struct_0(B_332))) | ~m1_pre_topc('#skF_1'(A_331, '#skF_2'(A_331, u1_struct_0(B_332))), A_333) | ~m1_pre_topc(B_330, A_333) | ~l1_pre_topc(A_333) | ~v2_pre_topc(A_333) | ~v3_tex_2('#skF_2'(A_331, u1_struct_0(B_332)), A_331) | v1_xboole_0('#skF_2'(A_331, u1_struct_0(B_332))) | ~v2_tex_2(u1_struct_0(B_332), A_331) | ~v3_tdlat_3(A_331) | ~v2_pre_topc(A_331) | v2_struct_0(A_331) | ~m1_pre_topc(B_332, A_331) | ~l1_pre_topc(A_331))), inference(superposition, [status(thm), theory('equality')], [c_408, c_6])).
% 7.87/2.81  tff(c_2479, plain, (![B_334, A_335, A_336]: (m1_pre_topc(B_334, '#skF_1'(A_335, '#skF_2'(A_335, u1_struct_0(B_334)))) | ~m1_pre_topc('#skF_1'(A_335, '#skF_2'(A_335, u1_struct_0(B_334))), A_336) | ~m1_pre_topc(B_334, A_336) | ~l1_pre_topc(A_336) | ~v2_pre_topc(A_336) | ~v3_tex_2('#skF_2'(A_335, u1_struct_0(B_334)), A_335) | v1_xboole_0('#skF_2'(A_335, u1_struct_0(B_334))) | ~v2_tex_2(u1_struct_0(B_334), A_335) | ~v3_tdlat_3(A_335) | ~v2_pre_topc(A_335) | v2_struct_0(A_335) | ~m1_pre_topc(B_334, A_335) | ~l1_pre_topc(A_335))), inference(resolution, [status(thm)], [c_85, c_2449])).
% 7.87/2.81  tff(c_2515, plain, (![B_339, A_340]: (m1_pre_topc(B_339, '#skF_1'(A_340, '#skF_2'(A_340, u1_struct_0(B_339)))) | ~v3_tex_2('#skF_2'(A_340, u1_struct_0(B_339)), A_340) | v1_xboole_0('#skF_2'(A_340, u1_struct_0(B_339))) | ~v2_tex_2(u1_struct_0(B_339), A_340) | ~v3_tdlat_3(A_340) | ~v2_pre_topc(A_340) | v2_struct_0(A_340) | ~m1_pre_topc(B_339, A_340) | ~l1_pre_topc(A_340))), inference(resolution, [status(thm)], [c_311, c_2479])).
% 7.87/2.81  tff(c_783, plain, (![A_189, B_190, A_191]: (m1_subset_1('#skF_2'(A_189, u1_struct_0(B_190)), k1_zfmisc_1(u1_struct_0(A_191))) | ~m1_pre_topc('#skF_1'(A_189, '#skF_2'(A_189, u1_struct_0(B_190))), A_191) | ~l1_pre_topc(A_191) | ~v3_tex_2('#skF_2'(A_189, u1_struct_0(B_190)), A_189) | v1_xboole_0('#skF_2'(A_189, u1_struct_0(B_190))) | ~v2_tex_2(u1_struct_0(B_190), A_189) | ~v3_tdlat_3(A_189) | ~v2_pre_topc(A_189) | v2_struct_0(A_189) | ~m1_pre_topc(B_190, A_189) | ~l1_pre_topc(A_189))), inference(superposition, [status(thm), theory('equality')], [c_408, c_2])).
% 7.87/2.81  tff(c_791, plain, (![A_192, B_193]: (m1_subset_1('#skF_2'(A_192, u1_struct_0(B_193)), k1_zfmisc_1(u1_struct_0(A_192))) | ~v3_tex_2('#skF_2'(A_192, u1_struct_0(B_193)), A_192) | v1_xboole_0('#skF_2'(A_192, u1_struct_0(B_193))) | ~v2_tex_2(u1_struct_0(B_193), A_192) | ~v3_tdlat_3(A_192) | ~v2_pre_topc(A_192) | v2_struct_0(A_192) | ~m1_pre_topc(B_193, A_192) | ~l1_pre_topc(A_192))), inference(resolution, [status(thm)], [c_311, c_783])).
% 7.87/2.81  tff(c_16, plain, (![A_21, B_25]: (v4_tex_2('#skF_1'(A_21, B_25), A_21) | ~v3_tex_2(B_25, A_21) | ~m1_subset_1(B_25, k1_zfmisc_1(u1_struct_0(A_21))) | v1_xboole_0(B_25) | ~l1_pre_topc(A_21) | ~v2_pre_topc(A_21) | v2_struct_0(A_21))), inference(cnfTransformation, [status(thm)], [f_110])).
% 7.87/2.81  tff(c_866, plain, (![A_199, B_200]: (v4_tex_2('#skF_1'(A_199, '#skF_2'(A_199, u1_struct_0(B_200))), A_199) | ~v3_tex_2('#skF_2'(A_199, u1_struct_0(B_200)), A_199) | v1_xboole_0('#skF_2'(A_199, u1_struct_0(B_200))) | ~v2_tex_2(u1_struct_0(B_200), A_199) | ~v3_tdlat_3(A_199) | ~v2_pre_topc(A_199) | v2_struct_0(A_199) | ~m1_pre_topc(B_200, A_199) | ~l1_pre_topc(A_199))), inference(resolution, [status(thm)], [c_791, c_16])).
% 7.87/2.81  tff(c_30, plain, (![C_37]: (~v4_tex_2(C_37, '#skF_3') | ~m1_pre_topc('#skF_4', C_37) | ~m1_pre_topc(C_37, '#skF_3') | ~v1_pre_topc(C_37) | v2_struct_0(C_37))), inference(cnfTransformation, [status(thm)], [f_163])).
% 7.87/2.81  tff(c_870, plain, (![B_200]: (~m1_pre_topc('#skF_4', '#skF_1'('#skF_3', '#skF_2'('#skF_3', u1_struct_0(B_200)))) | ~m1_pre_topc('#skF_1'('#skF_3', '#skF_2'('#skF_3', u1_struct_0(B_200))), '#skF_3') | ~v1_pre_topc('#skF_1'('#skF_3', '#skF_2'('#skF_3', u1_struct_0(B_200)))) | v2_struct_0('#skF_1'('#skF_3', '#skF_2'('#skF_3', u1_struct_0(B_200)))) | ~v3_tex_2('#skF_2'('#skF_3', u1_struct_0(B_200)), '#skF_3') | v1_xboole_0('#skF_2'('#skF_3', u1_struct_0(B_200))) | ~v2_tex_2(u1_struct_0(B_200), '#skF_3') | ~v3_tdlat_3('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~m1_pre_topc(B_200, '#skF_3') | ~l1_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_866, c_30])).
% 7.87/2.81  tff(c_879, plain, (![B_200]: (~m1_pre_topc('#skF_4', '#skF_1'('#skF_3', '#skF_2'('#skF_3', u1_struct_0(B_200)))) | ~m1_pre_topc('#skF_1'('#skF_3', '#skF_2'('#skF_3', u1_struct_0(B_200))), '#skF_3') | ~v1_pre_topc('#skF_1'('#skF_3', '#skF_2'('#skF_3', u1_struct_0(B_200)))) | v2_struct_0('#skF_1'('#skF_3', '#skF_2'('#skF_3', u1_struct_0(B_200)))) | ~v3_tex_2('#skF_2'('#skF_3', u1_struct_0(B_200)), '#skF_3') | v1_xboole_0('#skF_2'('#skF_3', u1_struct_0(B_200))) | ~v2_tex_2(u1_struct_0(B_200), '#skF_3') | v2_struct_0('#skF_3') | ~m1_pre_topc(B_200, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_42, c_40, c_870])).
% 7.87/2.81  tff(c_896, plain, (![B_203]: (~m1_pre_topc('#skF_4', '#skF_1'('#skF_3', '#skF_2'('#skF_3', u1_struct_0(B_203)))) | ~m1_pre_topc('#skF_1'('#skF_3', '#skF_2'('#skF_3', u1_struct_0(B_203))), '#skF_3') | ~v1_pre_topc('#skF_1'('#skF_3', '#skF_2'('#skF_3', u1_struct_0(B_203)))) | v2_struct_0('#skF_1'('#skF_3', '#skF_2'('#skF_3', u1_struct_0(B_203)))) | ~v3_tex_2('#skF_2'('#skF_3', u1_struct_0(B_203)), '#skF_3') | v1_xboole_0('#skF_2'('#skF_3', u1_struct_0(B_203))) | ~v2_tex_2(u1_struct_0(B_203), '#skF_3') | ~m1_pre_topc(B_203, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_44, c_879])).
% 7.87/2.81  tff(c_903, plain, (![B_3]: (~m1_pre_topc('#skF_4', '#skF_1'('#skF_3', '#skF_2'('#skF_3', u1_struct_0(B_3)))) | ~v1_pre_topc('#skF_1'('#skF_3', '#skF_2'('#skF_3', u1_struct_0(B_3)))) | v2_struct_0('#skF_1'('#skF_3', '#skF_2'('#skF_3', u1_struct_0(B_3)))) | ~v3_tex_2('#skF_2'('#skF_3', u1_struct_0(B_3)), '#skF_3') | v1_xboole_0('#skF_2'('#skF_3', u1_struct_0(B_3))) | ~v2_tex_2(u1_struct_0(B_3), '#skF_3') | ~v3_tdlat_3('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~m1_pre_topc(B_3, '#skF_3') | ~l1_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_311, c_896])).
% 7.87/2.81  tff(c_909, plain, (![B_3]: (~m1_pre_topc('#skF_4', '#skF_1'('#skF_3', '#skF_2'('#skF_3', u1_struct_0(B_3)))) | ~v1_pre_topc('#skF_1'('#skF_3', '#skF_2'('#skF_3', u1_struct_0(B_3)))) | v2_struct_0('#skF_1'('#skF_3', '#skF_2'('#skF_3', u1_struct_0(B_3)))) | ~v3_tex_2('#skF_2'('#skF_3', u1_struct_0(B_3)), '#skF_3') | v1_xboole_0('#skF_2'('#skF_3', u1_struct_0(B_3))) | ~v2_tex_2(u1_struct_0(B_3), '#skF_3') | v2_struct_0('#skF_3') | ~m1_pre_topc(B_3, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_42, c_40, c_903])).
% 7.87/2.81  tff(c_910, plain, (![B_3]: (~m1_pre_topc('#skF_4', '#skF_1'('#skF_3', '#skF_2'('#skF_3', u1_struct_0(B_3)))) | ~v1_pre_topc('#skF_1'('#skF_3', '#skF_2'('#skF_3', u1_struct_0(B_3)))) | v2_struct_0('#skF_1'('#skF_3', '#skF_2'('#skF_3', u1_struct_0(B_3)))) | ~v3_tex_2('#skF_2'('#skF_3', u1_struct_0(B_3)), '#skF_3') | v1_xboole_0('#skF_2'('#skF_3', u1_struct_0(B_3))) | ~v2_tex_2(u1_struct_0(B_3), '#skF_3') | ~m1_pre_topc(B_3, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_44, c_909])).
% 7.87/2.81  tff(c_2535, plain, (~v1_pre_topc('#skF_1'('#skF_3', '#skF_2'('#skF_3', u1_struct_0('#skF_4')))) | v2_struct_0('#skF_1'('#skF_3', '#skF_2'('#skF_3', u1_struct_0('#skF_4')))) | ~v3_tex_2('#skF_2'('#skF_3', u1_struct_0('#skF_4')), '#skF_3') | v1_xboole_0('#skF_2'('#skF_3', u1_struct_0('#skF_4'))) | ~v2_tex_2(u1_struct_0('#skF_4'), '#skF_3') | ~v3_tdlat_3('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_2515, c_910])).
% 7.87/2.81  tff(c_2577, plain, (~v1_pre_topc('#skF_1'('#skF_3', '#skF_2'('#skF_3', u1_struct_0('#skF_4')))) | v2_struct_0('#skF_1'('#skF_3', '#skF_2'('#skF_3', u1_struct_0('#skF_4')))) | ~v3_tex_2('#skF_2'('#skF_3', u1_struct_0('#skF_4')), '#skF_3') | v1_xboole_0('#skF_2'('#skF_3', u1_struct_0('#skF_4'))) | ~v2_tex_2(u1_struct_0('#skF_4'), '#skF_3') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_32, c_42, c_40, c_2535])).
% 7.87/2.81  tff(c_2578, plain, (~v1_pre_topc('#skF_1'('#skF_3', '#skF_2'('#skF_3', u1_struct_0('#skF_4')))) | v2_struct_0('#skF_1'('#skF_3', '#skF_2'('#skF_3', u1_struct_0('#skF_4')))) | ~v3_tex_2('#skF_2'('#skF_3', u1_struct_0('#skF_4')), '#skF_3') | v1_xboole_0('#skF_2'('#skF_3', u1_struct_0('#skF_4'))) | ~v2_tex_2(u1_struct_0('#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_44, c_2577])).
% 7.87/2.81  tff(c_2586, plain, (~v2_tex_2(u1_struct_0('#skF_4'), '#skF_3')), inference(splitLeft, [status(thm)], [c_2578])).
% 7.87/2.81  tff(c_2589, plain, (~v1_tdlat_3('#skF_4') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_101, c_2586])).
% 7.87/2.81  tff(c_2592, plain, (v2_struct_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_32, c_34, c_2589])).
% 7.87/2.81  tff(c_2594, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_36, c_2592])).
% 7.87/2.81  tff(c_2596, plain, (v2_tex_2(u1_struct_0('#skF_4'), '#skF_3')), inference(splitRight, [status(thm)], [c_2578])).
% 7.87/2.81  tff(c_74, plain, (![A_56, B_57]: (v3_tex_2('#skF_2'(A_56, B_57), A_56) | ~v2_tex_2(B_57, A_56) | ~m1_subset_1(B_57, k1_zfmisc_1(u1_struct_0(A_56))) | ~l1_pre_topc(A_56) | ~v3_tdlat_3(A_56) | ~v2_pre_topc(A_56) | v2_struct_0(A_56))), inference(cnfTransformation, [status(thm)], [f_133])).
% 7.87/2.82  tff(c_77, plain, (![A_1, B_3]: (v3_tex_2('#skF_2'(A_1, u1_struct_0(B_3)), A_1) | ~v2_tex_2(u1_struct_0(B_3), A_1) | ~v3_tdlat_3(A_1) | ~v2_pre_topc(A_1) | v2_struct_0(A_1) | ~m1_pre_topc(B_3, A_1) | ~l1_pre_topc(A_1))), inference(resolution, [status(thm)], [c_2, c_74])).
% 7.87/2.82  tff(c_20, plain, (![A_21, B_25]: (v1_pre_topc('#skF_1'(A_21, B_25)) | ~v3_tex_2(B_25, A_21) | ~m1_subset_1(B_25, k1_zfmisc_1(u1_struct_0(A_21))) | v1_xboole_0(B_25) | ~l1_pre_topc(A_21) | ~v2_pre_topc(A_21) | v2_struct_0(A_21))), inference(cnfTransformation, [status(thm)], [f_110])).
% 7.87/2.82  tff(c_284, plain, (![A_105, B_106]: (v1_pre_topc('#skF_1'(A_105, '#skF_2'(A_105, B_106))) | ~v3_tex_2('#skF_2'(A_105, B_106), A_105) | v1_xboole_0('#skF_2'(A_105, B_106)) | ~v2_tex_2(B_106, A_105) | ~m1_subset_1(B_106, k1_zfmisc_1(u1_struct_0(A_105))) | ~l1_pre_topc(A_105) | ~v3_tdlat_3(A_105) | ~v2_pre_topc(A_105) | v2_struct_0(A_105))), inference(resolution, [status(thm)], [c_111, c_20])).
% 7.87/2.82  tff(c_292, plain, (![A_1, B_3]: (v1_pre_topc('#skF_1'(A_1, '#skF_2'(A_1, u1_struct_0(B_3)))) | ~v3_tex_2('#skF_2'(A_1, u1_struct_0(B_3)), A_1) | v1_xboole_0('#skF_2'(A_1, u1_struct_0(B_3))) | ~v2_tex_2(u1_struct_0(B_3), A_1) | ~v3_tdlat_3(A_1) | ~v2_pre_topc(A_1) | v2_struct_0(A_1) | ~m1_pre_topc(B_3, A_1) | ~l1_pre_topc(A_1))), inference(resolution, [status(thm)], [c_2, c_284])).
% 7.87/2.82  tff(c_2595, plain, (~v3_tex_2('#skF_2'('#skF_3', u1_struct_0('#skF_4')), '#skF_3') | ~v1_pre_topc('#skF_1'('#skF_3', '#skF_2'('#skF_3', u1_struct_0('#skF_4')))) | v1_xboole_0('#skF_2'('#skF_3', u1_struct_0('#skF_4'))) | v2_struct_0('#skF_1'('#skF_3', '#skF_2'('#skF_3', u1_struct_0('#skF_4'))))), inference(splitRight, [status(thm)], [c_2578])).
% 7.87/2.82  tff(c_2604, plain, (~v1_pre_topc('#skF_1'('#skF_3', '#skF_2'('#skF_3', u1_struct_0('#skF_4'))))), inference(splitLeft, [status(thm)], [c_2595])).
% 7.87/2.82  tff(c_2632, plain, (~v3_tex_2('#skF_2'('#skF_3', u1_struct_0('#skF_4')), '#skF_3') | v1_xboole_0('#skF_2'('#skF_3', u1_struct_0('#skF_4'))) | ~v2_tex_2(u1_struct_0('#skF_4'), '#skF_3') | ~v3_tdlat_3('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_292, c_2604])).
% 7.87/2.82  tff(c_2635, plain, (~v3_tex_2('#skF_2'('#skF_3', u1_struct_0('#skF_4')), '#skF_3') | v1_xboole_0('#skF_2'('#skF_3', u1_struct_0('#skF_4'))) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_32, c_42, c_40, c_2596, c_2632])).
% 7.87/2.82  tff(c_2636, plain, (~v3_tex_2('#skF_2'('#skF_3', u1_struct_0('#skF_4')), '#skF_3') | v1_xboole_0('#skF_2'('#skF_3', u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_44, c_2635])).
% 7.87/2.82  tff(c_2637, plain, (~v3_tex_2('#skF_2'('#skF_3', u1_struct_0('#skF_4')), '#skF_3')), inference(splitLeft, [status(thm)], [c_2636])).
% 7.87/2.82  tff(c_2643, plain, (~v2_tex_2(u1_struct_0('#skF_4'), '#skF_3') | ~v3_tdlat_3('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_77, c_2637])).
% 7.87/2.82  tff(c_2650, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_32, c_42, c_40, c_2596, c_2643])).
% 7.87/2.82  tff(c_2652, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_2650])).
% 7.87/2.82  tff(c_2653, plain, (v1_xboole_0('#skF_2'('#skF_3', u1_struct_0('#skF_4')))), inference(splitRight, [status(thm)], [c_2636])).
% 7.87/2.82  tff(c_12, plain, (![B_20, A_18]: (~v3_tex_2(B_20, A_18) | ~m1_subset_1(B_20, k1_zfmisc_1(u1_struct_0(A_18))) | ~v1_xboole_0(B_20) | ~l1_pre_topc(A_18) | ~v2_pre_topc(A_18) | v2_struct_0(A_18))), inference(cnfTransformation, [status(thm)], [f_81])).
% 7.87/2.82  tff(c_238, plain, (![A_90, B_91]: (~v3_tex_2('#skF_2'(A_90, B_91), A_90) | ~v1_xboole_0('#skF_2'(A_90, B_91)) | ~v2_tex_2(B_91, A_90) | ~m1_subset_1(B_91, k1_zfmisc_1(u1_struct_0(A_90))) | ~l1_pre_topc(A_90) | ~v3_tdlat_3(A_90) | ~v2_pre_topc(A_90) | v2_struct_0(A_90))), inference(resolution, [status(thm)], [c_111, c_12])).
% 7.87/2.82  tff(c_242, plain, (![A_92, B_93]: (~v1_xboole_0('#skF_2'(A_92, u1_struct_0(B_93))) | ~m1_subset_1(u1_struct_0(B_93), k1_zfmisc_1(u1_struct_0(A_92))) | ~v2_tex_2(u1_struct_0(B_93), A_92) | ~v3_tdlat_3(A_92) | ~v2_pre_topc(A_92) | v2_struct_0(A_92) | ~m1_pre_topc(B_93, A_92) | ~l1_pre_topc(A_92))), inference(resolution, [status(thm)], [c_77, c_238])).
% 7.87/2.82  tff(c_252, plain, (![A_1, B_3]: (~v1_xboole_0('#skF_2'(A_1, u1_struct_0(B_3))) | ~v2_tex_2(u1_struct_0(B_3), A_1) | ~v3_tdlat_3(A_1) | ~v2_pre_topc(A_1) | v2_struct_0(A_1) | ~m1_pre_topc(B_3, A_1) | ~l1_pre_topc(A_1))), inference(resolution, [status(thm)], [c_2, c_242])).
% 7.87/2.82  tff(c_2660, plain, (~v2_tex_2(u1_struct_0('#skF_4'), '#skF_3') | ~v3_tdlat_3('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_2653, c_252])).
% 7.87/2.82  tff(c_2667, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_32, c_42, c_40, c_2596, c_2660])).
% 7.87/2.82  tff(c_2669, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_2667])).
% 7.87/2.82  tff(c_2670, plain, (~v3_tex_2('#skF_2'('#skF_3', u1_struct_0('#skF_4')), '#skF_3') | v2_struct_0('#skF_1'('#skF_3', '#skF_2'('#skF_3', u1_struct_0('#skF_4')))) | v1_xboole_0('#skF_2'('#skF_3', u1_struct_0('#skF_4')))), inference(splitRight, [status(thm)], [c_2595])).
% 7.87/2.82  tff(c_2672, plain, (~v3_tex_2('#skF_2'('#skF_3', u1_struct_0('#skF_4')), '#skF_3')), inference(splitLeft, [status(thm)], [c_2670])).
% 7.87/2.82  tff(c_2678, plain, (~v2_tex_2(u1_struct_0('#skF_4'), '#skF_3') | ~v3_tdlat_3('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_77, c_2672])).
% 7.87/2.82  tff(c_2685, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_32, c_42, c_40, c_2596, c_2678])).
% 7.87/2.82  tff(c_2687, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_2685])).
% 7.87/2.82  tff(c_2689, plain, (v3_tex_2('#skF_2'('#skF_3', u1_struct_0('#skF_4')), '#skF_3')), inference(splitRight, [status(thm)], [c_2670])).
% 7.87/2.82  tff(c_139, plain, (![A_74, B_75]: (~v3_tex_2('#skF_2'(A_74, B_75), A_74) | ~v1_xboole_0('#skF_2'(A_74, B_75)) | ~v2_tex_2(B_75, A_74) | ~m1_subset_1(B_75, k1_zfmisc_1(u1_struct_0(A_74))) | ~l1_pre_topc(A_74) | ~v3_tdlat_3(A_74) | ~v2_pre_topc(A_74) | v2_struct_0(A_74))), inference(resolution, [status(thm)], [c_111, c_12])).
% 7.87/2.82  tff(c_2691, plain, (~v1_xboole_0('#skF_2'('#skF_3', u1_struct_0('#skF_4'))) | ~v2_tex_2(u1_struct_0('#skF_4'), '#skF_3') | ~m1_subset_1(u1_struct_0('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v3_tdlat_3('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_2689, c_139])).
% 7.87/2.82  tff(c_2694, plain, (~v1_xboole_0('#skF_2'('#skF_3', u1_struct_0('#skF_4'))) | ~m1_subset_1(u1_struct_0('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_2596, c_2691])).
% 7.87/2.82  tff(c_2695, plain, (~v1_xboole_0('#skF_2'('#skF_3', u1_struct_0('#skF_4'))) | ~m1_subset_1(u1_struct_0('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_44, c_2694])).
% 7.87/2.82  tff(c_2696, plain, (~m1_subset_1(u1_struct_0('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(splitLeft, [status(thm)], [c_2695])).
% 7.87/2.82  tff(c_2724, plain, (~m1_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_2, c_2696])).
% 7.87/2.82  tff(c_2728, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_32, c_2724])).
% 7.87/2.82  tff(c_2729, plain, (~v1_xboole_0('#skF_2'('#skF_3', u1_struct_0('#skF_4')))), inference(splitRight, [status(thm)], [c_2695])).
% 7.87/2.82  tff(c_2494, plain, (![B_3, A_1]: (m1_pre_topc(B_3, '#skF_1'(A_1, '#skF_2'(A_1, u1_struct_0(B_3)))) | ~v3_tex_2('#skF_2'(A_1, u1_struct_0(B_3)), A_1) | v1_xboole_0('#skF_2'(A_1, u1_struct_0(B_3))) | ~v2_tex_2(u1_struct_0(B_3), A_1) | ~v3_tdlat_3(A_1) | ~v2_pre_topc(A_1) | v2_struct_0(A_1) | ~m1_pre_topc(B_3, A_1) | ~l1_pre_topc(A_1))), inference(resolution, [status(thm)], [c_311, c_2479])).
% 7.87/2.82  tff(c_2730, plain, (m1_subset_1(u1_struct_0('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(splitRight, [status(thm)], [c_2695])).
% 7.87/2.82  tff(c_135, plain, (![A_74, B_75]: (m1_pre_topc('#skF_1'(A_74, '#skF_2'(A_74, B_75)), A_74) | ~v3_tex_2('#skF_2'(A_74, B_75), A_74) | v1_xboole_0('#skF_2'(A_74, B_75)) | ~v2_tex_2(B_75, A_74) | ~m1_subset_1(B_75, k1_zfmisc_1(u1_struct_0(A_74))) | ~l1_pre_topc(A_74) | ~v3_tdlat_3(A_74) | ~v2_pre_topc(A_74) | v2_struct_0(A_74))), inference(resolution, [status(thm)], [c_111, c_18])).
% 7.87/2.82  tff(c_2737, plain, (m1_pre_topc('#skF_1'('#skF_3', '#skF_2'('#skF_3', u1_struct_0('#skF_4'))), '#skF_3') | ~v3_tex_2('#skF_2'('#skF_3', u1_struct_0('#skF_4')), '#skF_3') | v1_xboole_0('#skF_2'('#skF_3', u1_struct_0('#skF_4'))) | ~v2_tex_2(u1_struct_0('#skF_4'), '#skF_3') | ~l1_pre_topc('#skF_3') | ~v3_tdlat_3('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_2730, c_135])).
% 7.87/2.82  tff(c_2770, plain, (m1_pre_topc('#skF_1'('#skF_3', '#skF_2'('#skF_3', u1_struct_0('#skF_4'))), '#skF_3') | v1_xboole_0('#skF_2'('#skF_3', u1_struct_0('#skF_4'))) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_2596, c_2689, c_2737])).
% 7.87/2.82  tff(c_2771, plain, (m1_pre_topc('#skF_1'('#skF_3', '#skF_2'('#skF_3', u1_struct_0('#skF_4'))), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_44, c_2729, c_2770])).
% 7.87/2.82  tff(c_516, plain, (![A_136, B_137, A_1]: (m1_subset_1('#skF_2'(A_136, u1_struct_0(B_137)), k1_zfmisc_1(u1_struct_0(A_1))) | ~m1_pre_topc('#skF_1'(A_136, '#skF_2'(A_136, u1_struct_0(B_137))), A_1) | ~l1_pre_topc(A_1) | ~v3_tex_2('#skF_2'(A_136, u1_struct_0(B_137)), A_136) | v1_xboole_0('#skF_2'(A_136, u1_struct_0(B_137))) | ~v2_tex_2(u1_struct_0(B_137), A_136) | ~v3_tdlat_3(A_136) | ~v2_pre_topc(A_136) | v2_struct_0(A_136) | ~m1_pre_topc(B_137, A_136) | ~l1_pre_topc(A_136))), inference(superposition, [status(thm), theory('equality')], [c_408, c_2])).
% 7.87/2.82  tff(c_2817, plain, (m1_subset_1('#skF_2'('#skF_3', u1_struct_0('#skF_4')), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~v3_tex_2('#skF_2'('#skF_3', u1_struct_0('#skF_4')), '#skF_3') | v1_xboole_0('#skF_2'('#skF_3', u1_struct_0('#skF_4'))) | ~v2_tex_2(u1_struct_0('#skF_4'), '#skF_3') | ~v3_tdlat_3('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_2771, c_516])).
% 7.87/2.82  tff(c_2826, plain, (m1_subset_1('#skF_2'('#skF_3', u1_struct_0('#skF_4')), k1_zfmisc_1(u1_struct_0('#skF_3'))) | v1_xboole_0('#skF_2'('#skF_3', u1_struct_0('#skF_4'))) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_32, c_42, c_40, c_2596, c_2689, c_2817])).
% 7.87/2.82  tff(c_2827, plain, (m1_subset_1('#skF_2'('#skF_3', u1_struct_0('#skF_4')), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_44, c_2729, c_2826])).
% 7.87/2.82  tff(c_22, plain, (![A_21, B_25]: (~v2_struct_0('#skF_1'(A_21, B_25)) | ~v3_tex_2(B_25, A_21) | ~m1_subset_1(B_25, k1_zfmisc_1(u1_struct_0(A_21))) | v1_xboole_0(B_25) | ~l1_pre_topc(A_21) | ~v2_pre_topc(A_21) | v2_struct_0(A_21))), inference(cnfTransformation, [status(thm)], [f_110])).
% 7.87/2.82  tff(c_2856, plain, (~v2_struct_0('#skF_1'('#skF_3', '#skF_2'('#skF_3', u1_struct_0('#skF_4')))) | ~v3_tex_2('#skF_2'('#skF_3', u1_struct_0('#skF_4')), '#skF_3') | v1_xboole_0('#skF_2'('#skF_3', u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_2827, c_22])).
% 7.87/2.82  tff(c_2899, plain, (~v2_struct_0('#skF_1'('#skF_3', '#skF_2'('#skF_3', u1_struct_0('#skF_4')))) | v1_xboole_0('#skF_2'('#skF_3', u1_struct_0('#skF_4'))) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_38, c_2689, c_2856])).
% 7.87/2.82  tff(c_2900, plain, (~v2_struct_0('#skF_1'('#skF_3', '#skF_2'('#skF_3', u1_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_44, c_2729, c_2899])).
% 7.87/2.82  tff(c_2671, plain, (v1_pre_topc('#skF_1'('#skF_3', '#skF_2'('#skF_3', u1_struct_0('#skF_4'))))), inference(splitRight, [status(thm)], [c_2595])).
% 7.87/2.82  tff(c_2841, plain, (v4_tex_2('#skF_1'('#skF_3', '#skF_2'('#skF_3', u1_struct_0('#skF_4'))), '#skF_3') | ~v3_tex_2('#skF_2'('#skF_3', u1_struct_0('#skF_4')), '#skF_3') | v1_xboole_0('#skF_2'('#skF_3', u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_2827, c_16])).
% 7.87/2.82  tff(c_2875, plain, (v4_tex_2('#skF_1'('#skF_3', '#skF_2'('#skF_3', u1_struct_0('#skF_4'))), '#skF_3') | v1_xboole_0('#skF_2'('#skF_3', u1_struct_0('#skF_4'))) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_38, c_2689, c_2841])).
% 7.87/2.82  tff(c_2876, plain, (v4_tex_2('#skF_1'('#skF_3', '#skF_2'('#skF_3', u1_struct_0('#skF_4'))), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_44, c_2729, c_2875])).
% 7.87/2.82  tff(c_2907, plain, (~m1_pre_topc('#skF_4', '#skF_1'('#skF_3', '#skF_2'('#skF_3', u1_struct_0('#skF_4')))) | ~m1_pre_topc('#skF_1'('#skF_3', '#skF_2'('#skF_3', u1_struct_0('#skF_4'))), '#skF_3') | ~v1_pre_topc('#skF_1'('#skF_3', '#skF_2'('#skF_3', u1_struct_0('#skF_4')))) | v2_struct_0('#skF_1'('#skF_3', '#skF_2'('#skF_3', u1_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_2876, c_30])).
% 7.87/2.82  tff(c_2910, plain, (~m1_pre_topc('#skF_4', '#skF_1'('#skF_3', '#skF_2'('#skF_3', u1_struct_0('#skF_4')))) | v2_struct_0('#skF_1'('#skF_3', '#skF_2'('#skF_3', u1_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_2671, c_2771, c_2907])).
% 7.87/2.82  tff(c_2911, plain, (~m1_pre_topc('#skF_4', '#skF_1'('#skF_3', '#skF_2'('#skF_3', u1_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_2900, c_2910])).
% 7.87/2.82  tff(c_2939, plain, (~v3_tex_2('#skF_2'('#skF_3', u1_struct_0('#skF_4')), '#skF_3') | v1_xboole_0('#skF_2'('#skF_3', u1_struct_0('#skF_4'))) | ~v2_tex_2(u1_struct_0('#skF_4'), '#skF_3') | ~v3_tdlat_3('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_2494, c_2911])).
% 7.87/2.82  tff(c_2942, plain, (v1_xboole_0('#skF_2'('#skF_3', u1_struct_0('#skF_4'))) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_32, c_42, c_40, c_2596, c_2689, c_2939])).
% 7.87/2.82  tff(c_2944, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_2729, c_2942])).
% 7.87/2.82  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.87/2.82  
% 7.87/2.82  Inference rules
% 7.87/2.82  ----------------------
% 7.87/2.82  #Ref     : 0
% 7.87/2.82  #Sup     : 829
% 7.87/2.82  #Fact    : 0
% 7.87/2.82  #Define  : 0
% 7.87/2.82  #Split   : 7
% 7.87/2.82  #Chain   : 0
% 7.87/2.82  #Close   : 0
% 7.87/2.82  
% 7.87/2.82  Ordering : KBO
% 7.87/2.82  
% 7.87/2.82  Simplification rules
% 7.87/2.82  ----------------------
% 7.87/2.82  #Subsume      : 68
% 7.87/2.82  #Demod        : 220
% 7.87/2.82  #Tautology    : 37
% 7.87/2.82  #SimpNegUnit  : 65
% 7.87/2.82  #BackRed      : 0
% 7.87/2.82  
% 7.87/2.82  #Partial instantiations: 0
% 7.87/2.82  #Strategies tried      : 1
% 7.87/2.82  
% 7.87/2.82  Timing (in seconds)
% 7.87/2.82  ----------------------
% 7.87/2.82  Preprocessing        : 0.34
% 7.87/2.82  Parsing              : 0.19
% 7.87/2.82  CNF conversion       : 0.03
% 7.87/2.82  Main loop            : 1.63
% 7.87/2.82  Inferencing          : 0.44
% 7.87/2.82  Reduction            : 0.32
% 7.87/2.82  Demodulation         : 0.21
% 7.87/2.82  BG Simplification    : 0.06
% 7.87/2.82  Subsumption          : 0.74
% 7.87/2.82  Abstraction          : 0.06
% 7.87/2.82  MUC search           : 0.00
% 7.87/2.82  Cooper               : 0.00
% 7.87/2.82  Total                : 2.02
% 7.87/2.82  Index Insertion      : 0.00
% 7.87/2.82  Index Deletion       : 0.00
% 7.87/2.82  Index Matching       : 0.00
% 7.87/2.82  BG Taut test         : 0.00
%------------------------------------------------------------------------------
