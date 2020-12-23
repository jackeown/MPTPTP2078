%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:39 EST 2020

% Result     : Theorem 3.45s
% Output     : CNFRefutation 3.45s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 237 expanded)
%              Number of leaves         :   47 ( 106 expanded)
%              Depth                    :   15
%              Number of atoms          :  255 (1122 expanded)
%              Number of equality atoms :   34 ( 162 expanded)
%              Maximal formula depth    :   20 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_pre_topc > v3_borsuk_1 > v1_funct_2 > v4_tex_2 > v3_tex_2 > m1_subset_1 > m1_pre_topc > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_pre_topc > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k8_relset_1 > k2_enumset1 > k7_domain_1 > k1_enumset1 > k6_domain_1 > k2_zfmisc_1 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

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

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v3_tex_2,type,(
    v3_tex_2: ( $i * $i ) > $o )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k7_domain_1,type,(
    k7_domain_1: ( $i * $i * $i ) > $i )).

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

tff(f_197,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tex_2)).

tff(f_72,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_88,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_46,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_105,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ( v4_tex_2(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( C = u1_struct_0(B)
                 => v3_tex_2(C,A) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_tex_2)).

tff(f_120,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( v1_xboole_0(B)
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
         => ~ v3_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_tex_2)).

tff(f_27,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A)
        & m1_subset_1(C,A) )
     => k7_domain_1(A,B,C) = k2_tarski(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_domain_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A)
        & m1_subset_1(C,A) )
     => m1_subset_1(k7_domain_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_domain_1)).

tff(f_158,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_tex_2)).

tff(c_62,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_58,plain,(
    m1_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_64,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_44,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_110,plain,(
    ! [A_128,B_129] :
      ( k6_domain_1(A_128,B_129) = k1_tarski(B_129)
      | ~ m1_subset_1(B_129,A_128)
      | v1_xboole_0(A_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_122,plain,
    ( k6_domain_1(u1_struct_0('#skF_2'),'#skF_6') = k1_tarski('#skF_6')
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_44,c_110])).

tff(c_343,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_122])).

tff(c_349,plain,(
    ! [B_200,A_201] :
      ( m1_subset_1(u1_struct_0(B_200),k1_zfmisc_1(u1_struct_0(A_201)))
      | ~ m1_pre_topc(B_200,A_201)
      | ~ l1_pre_topc(A_201) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_16,plain,(
    ! [B_31,A_29] :
      ( v1_xboole_0(B_31)
      | ~ m1_subset_1(B_31,k1_zfmisc_1(A_29))
      | ~ v1_xboole_0(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_367,plain,(
    ! [B_206,A_207] :
      ( v1_xboole_0(u1_struct_0(B_206))
      | ~ v1_xboole_0(u1_struct_0(A_207))
      | ~ m1_pre_topc(B_206,A_207)
      | ~ l1_pre_topc(A_207) ) ),
    inference(resolution,[status(thm)],[c_349,c_16])).

tff(c_369,plain,(
    ! [B_206] :
      ( v1_xboole_0(u1_struct_0(B_206))
      | ~ m1_pre_topc(B_206,'#skF_2')
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_343,c_367])).

tff(c_382,plain,(
    ! [B_213] :
      ( v1_xboole_0(u1_struct_0(B_213))
      | ~ m1_pre_topc(B_213,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_369])).

tff(c_70,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_68,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_60,plain,(
    v4_tex_2('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_42,plain,(
    '#skF_5' = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_46,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_71,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_46])).

tff(c_121,plain,
    ( k6_domain_1(u1_struct_0('#skF_3'),'#skF_6') = k1_tarski('#skF_6')
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_71,c_110])).

tff(c_123,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_121])).

tff(c_26,plain,(
    ! [B_49,A_47] :
      ( m1_subset_1(u1_struct_0(B_49),k1_zfmisc_1(u1_struct_0(A_47)))
      | ~ m1_pre_topc(B_49,A_47)
      | ~ l1_pre_topc(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_290,plain,(
    ! [B_188,A_189] :
      ( v3_tex_2(u1_struct_0(B_188),A_189)
      | ~ m1_subset_1(u1_struct_0(B_188),k1_zfmisc_1(u1_struct_0(A_189)))
      | ~ v4_tex_2(B_188,A_189)
      | ~ m1_pre_topc(B_188,A_189)
      | ~ l1_pre_topc(A_189)
      | v2_struct_0(A_189) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_295,plain,(
    ! [B_190,A_191] :
      ( v3_tex_2(u1_struct_0(B_190),A_191)
      | ~ v4_tex_2(B_190,A_191)
      | v2_struct_0(A_191)
      | ~ m1_pre_topc(B_190,A_191)
      | ~ l1_pre_topc(A_191) ) ),
    inference(resolution,[status(thm)],[c_26,c_290])).

tff(c_220,plain,(
    ! [B_165,A_166] :
      ( ~ v3_tex_2(B_165,A_166)
      | ~ m1_subset_1(B_165,k1_zfmisc_1(u1_struct_0(A_166)))
      | ~ v1_xboole_0(B_165)
      | ~ l1_pre_topc(A_166)
      | ~ v2_pre_topc(A_166)
      | v2_struct_0(A_166) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_229,plain,(
    ! [B_49,A_47] :
      ( ~ v3_tex_2(u1_struct_0(B_49),A_47)
      | ~ v1_xboole_0(u1_struct_0(B_49))
      | ~ v2_pre_topc(A_47)
      | v2_struct_0(A_47)
      | ~ m1_pre_topc(B_49,A_47)
      | ~ l1_pre_topc(A_47) ) ),
    inference(resolution,[status(thm)],[c_26,c_220])).

tff(c_300,plain,(
    ! [B_192,A_193] :
      ( ~ v1_xboole_0(u1_struct_0(B_192))
      | ~ v2_pre_topc(A_193)
      | ~ v4_tex_2(B_192,A_193)
      | v2_struct_0(A_193)
      | ~ m1_pre_topc(B_192,A_193)
      | ~ l1_pre_topc(A_193) ) ),
    inference(resolution,[status(thm)],[c_295,c_229])).

tff(c_327,plain,(
    ! [A_199] :
      ( ~ v2_pre_topc(A_199)
      | ~ v4_tex_2('#skF_3',A_199)
      | v2_struct_0(A_199)
      | ~ m1_pre_topc('#skF_3',A_199)
      | ~ l1_pre_topc(A_199) ) ),
    inference(resolution,[status(thm)],[c_123,c_300])).

tff(c_334,plain,
    ( ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_60,c_327])).

tff(c_338,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_58,c_68,c_334])).

tff(c_340,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_338])).

tff(c_342,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_121])).

tff(c_387,plain,(
    ~ m1_pre_topc('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_382,c_342])).

tff(c_392,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_387])).

tff(c_393,plain,(
    k6_domain_1(u1_struct_0('#skF_2'),'#skF_6') = k1_tarski('#skF_6') ),
    inference(splitRight,[status(thm)],[c_122])).

tff(c_341,plain,(
    k6_domain_1(u1_struct_0('#skF_3'),'#skF_6') = k1_tarski('#skF_6') ),
    inference(splitRight,[status(thm)],[c_121])).

tff(c_40,plain,(
    k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4',k6_domain_1(u1_struct_0('#skF_3'),'#skF_5')) != k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_72,plain,(
    k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4',k6_domain_1(u1_struct_0('#skF_3'),'#skF_6')) != k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40])).

tff(c_395,plain,(
    k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4',k1_tarski('#skF_6')) != k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_341,c_72])).

tff(c_433,plain,(
    k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4',k1_tarski('#skF_6')) != k2_pre_topc('#skF_2',k1_tarski('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_393,c_395])).

tff(c_56,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_54,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_52,plain,(
    v5_pre_topc('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_48,plain,(
    v3_borsuk_1('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_2,plain,(
    ! [A_1] : k2_tarski(A_1,A_1) = k1_tarski(A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_461,plain,(
    ! [A_241,B_242,C_243] :
      ( k7_domain_1(A_241,B_242,C_243) = k2_tarski(B_242,C_243)
      | ~ m1_subset_1(C_243,A_241)
      | ~ m1_subset_1(B_242,A_241)
      | v1_xboole_0(A_241) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_469,plain,(
    ! [B_242] :
      ( k7_domain_1(u1_struct_0('#skF_3'),B_242,'#skF_6') = k2_tarski(B_242,'#skF_6')
      | ~ m1_subset_1(B_242,u1_struct_0('#skF_3'))
      | v1_xboole_0(u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_71,c_461])).

tff(c_482,plain,(
    ! [B_244] :
      ( k7_domain_1(u1_struct_0('#skF_3'),B_244,'#skF_6') = k2_tarski(B_244,'#skF_6')
      | ~ m1_subset_1(B_244,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_342,c_469])).

tff(c_485,plain,(
    k7_domain_1(u1_struct_0('#skF_3'),'#skF_6','#skF_6') = k2_tarski('#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_71,c_482])).

tff(c_487,plain,(
    k7_domain_1(u1_struct_0('#skF_3'),'#skF_6','#skF_6') = k1_tarski('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_485])).

tff(c_20,plain,(
    ! [A_39,B_40,C_41] :
      ( m1_subset_1(k7_domain_1(A_39,B_40,C_41),k1_zfmisc_1(A_39))
      | ~ m1_subset_1(C_41,A_39)
      | ~ m1_subset_1(B_40,A_39)
      | v1_xboole_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_491,plain,
    ( m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3'))
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_487,c_20])).

tff(c_495,plain,
    ( m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_71,c_491])).

tff(c_496,plain,(
    m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_342,c_495])).

tff(c_50,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_66,plain,(
    v3_tdlat_3('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_394,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_122])).

tff(c_471,plain,(
    ! [B_242] :
      ( k7_domain_1(u1_struct_0('#skF_2'),B_242,'#skF_6') = k2_tarski(B_242,'#skF_6')
      | ~ m1_subset_1(B_242,u1_struct_0('#skF_2'))
      | v1_xboole_0(u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_44,c_461])).

tff(c_530,plain,(
    ! [B_249] :
      ( k7_domain_1(u1_struct_0('#skF_2'),B_249,'#skF_6') = k2_tarski(B_249,'#skF_6')
      | ~ m1_subset_1(B_249,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_394,c_471])).

tff(c_533,plain,(
    k7_domain_1(u1_struct_0('#skF_2'),'#skF_6','#skF_6') = k2_tarski('#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_44,c_530])).

tff(c_535,plain,(
    k7_domain_1(u1_struct_0('#skF_2'),'#skF_6','#skF_6') = k1_tarski('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_533])).

tff(c_539,plain,
    ( m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_2'))
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_535,c_20])).

tff(c_543,plain,
    ( m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_44,c_539])).

tff(c_544,plain,(
    m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_394,c_543])).

tff(c_749,plain,(
    ! [A_293,B_294,C_295,E_296] :
      ( k8_relset_1(u1_struct_0(A_293),u1_struct_0(B_294),C_295,E_296) = k2_pre_topc(A_293,E_296)
      | ~ m1_subset_1(E_296,k1_zfmisc_1(u1_struct_0(A_293)))
      | ~ m1_subset_1(E_296,k1_zfmisc_1(u1_struct_0(B_294)))
      | ~ v3_borsuk_1(C_295,A_293,B_294)
      | ~ m1_subset_1(C_295,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_293),u1_struct_0(B_294))))
      | ~ v5_pre_topc(C_295,A_293,B_294)
      | ~ v1_funct_2(C_295,u1_struct_0(A_293),u1_struct_0(B_294))
      | ~ v1_funct_1(C_295)
      | ~ m1_pre_topc(B_294,A_293)
      | ~ v4_tex_2(B_294,A_293)
      | v2_struct_0(B_294)
      | ~ l1_pre_topc(A_293)
      | ~ v3_tdlat_3(A_293)
      | ~ v2_pre_topc(A_293)
      | v2_struct_0(A_293) ) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_757,plain,(
    ! [B_294,C_295] :
      ( k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0(B_294),C_295,k1_tarski('#skF_6')) = k2_pre_topc('#skF_2',k1_tarski('#skF_6'))
      | ~ m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0(B_294)))
      | ~ v3_borsuk_1(C_295,'#skF_2',B_294)
      | ~ m1_subset_1(C_295,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0(B_294))))
      | ~ v5_pre_topc(C_295,'#skF_2',B_294)
      | ~ v1_funct_2(C_295,u1_struct_0('#skF_2'),u1_struct_0(B_294))
      | ~ v1_funct_1(C_295)
      | ~ m1_pre_topc(B_294,'#skF_2')
      | ~ v4_tex_2(B_294,'#skF_2')
      | v2_struct_0(B_294)
      | ~ l1_pre_topc('#skF_2')
      | ~ v3_tdlat_3('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_544,c_749])).

tff(c_772,plain,(
    ! [B_294,C_295] :
      ( k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0(B_294),C_295,k1_tarski('#skF_6')) = k2_pre_topc('#skF_2',k1_tarski('#skF_6'))
      | ~ m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0(B_294)))
      | ~ v3_borsuk_1(C_295,'#skF_2',B_294)
      | ~ m1_subset_1(C_295,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0(B_294))))
      | ~ v5_pre_topc(C_295,'#skF_2',B_294)
      | ~ v1_funct_2(C_295,u1_struct_0('#skF_2'),u1_struct_0(B_294))
      | ~ v1_funct_1(C_295)
      | ~ m1_pre_topc(B_294,'#skF_2')
      | ~ v4_tex_2(B_294,'#skF_2')
      | v2_struct_0(B_294)
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_64,c_757])).

tff(c_837,plain,(
    ! [B_306,C_307] :
      ( k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0(B_306),C_307,k1_tarski('#skF_6')) = k2_pre_topc('#skF_2',k1_tarski('#skF_6'))
      | ~ m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0(B_306)))
      | ~ v3_borsuk_1(C_307,'#skF_2',B_306)
      | ~ m1_subset_1(C_307,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0(B_306))))
      | ~ v5_pre_topc(C_307,'#skF_2',B_306)
      | ~ v1_funct_2(C_307,u1_struct_0('#skF_2'),u1_struct_0(B_306))
      | ~ v1_funct_1(C_307)
      | ~ m1_pre_topc(B_306,'#skF_2')
      | ~ v4_tex_2(B_306,'#skF_2')
      | v2_struct_0(B_306) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_772])).

tff(c_844,plain,
    ( k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4',k1_tarski('#skF_6')) = k2_pre_topc('#skF_2',k1_tarski('#skF_6'))
    | ~ m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ v3_borsuk_1('#skF_4','#skF_2','#skF_3')
    | ~ v5_pre_topc('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ v4_tex_2('#skF_3','#skF_2')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_837])).

tff(c_848,plain,
    ( k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4',k1_tarski('#skF_6')) = k2_pre_topc('#skF_2',k1_tarski('#skF_6'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_56,c_54,c_52,c_48,c_496,c_844])).

tff(c_850,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_433,c_848])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:18:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.45/1.55  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.45/1.56  
% 3.45/1.56  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.45/1.56  %$ v5_pre_topc > v3_borsuk_1 > v1_funct_2 > v4_tex_2 > v3_tex_2 > m1_subset_1 > m1_pre_topc > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_pre_topc > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k8_relset_1 > k2_enumset1 > k7_domain_1 > k1_enumset1 > k6_domain_1 > k2_zfmisc_1 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 3.45/1.56  
% 3.45/1.56  %Foreground sorts:
% 3.45/1.56  
% 3.45/1.56  
% 3.45/1.56  %Background operators:
% 3.45/1.56  
% 3.45/1.56  
% 3.45/1.56  %Foreground operators:
% 3.45/1.56  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.45/1.56  tff(v3_borsuk_1, type, v3_borsuk_1: ($i * $i * $i) > $o).
% 3.45/1.56  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.45/1.56  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.45/1.56  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.45/1.56  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 3.45/1.56  tff(v4_tex_2, type, v4_tex_2: ($i * $i) > $o).
% 3.45/1.56  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.45/1.56  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.45/1.56  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 3.45/1.56  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.45/1.56  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.45/1.56  tff('#skF_5', type, '#skF_5': $i).
% 3.45/1.56  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 3.45/1.56  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.45/1.56  tff('#skF_6', type, '#skF_6': $i).
% 3.45/1.56  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.45/1.56  tff('#skF_2', type, '#skF_2': $i).
% 3.45/1.56  tff(k7_domain_1, type, k7_domain_1: ($i * $i * $i) > $i).
% 3.45/1.56  tff('#skF_3', type, '#skF_3': $i).
% 3.45/1.56  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.45/1.56  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.45/1.56  tff(v3_tdlat_3, type, v3_tdlat_3: $i > $o).
% 3.45/1.56  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.45/1.56  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.45/1.56  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.45/1.56  tff('#skF_4', type, '#skF_4': $i).
% 3.45/1.56  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.45/1.56  tff(v5_pre_topc, type, v5_pre_topc: ($i * $i * $i) > $o).
% 3.45/1.56  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.45/1.56  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.45/1.56  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.45/1.56  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.45/1.56  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.45/1.56  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.45/1.56  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 3.45/1.56  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.45/1.56  
% 3.45/1.58  tff(f_197, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v4_tex_2(B, A)) & m1_pre_topc(B, A)) => (![C]: ((((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & v5_pre_topc(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (v3_borsuk_1(C, A, B) => (![D]: (m1_subset_1(D, u1_struct_0(B)) => (![E]: (m1_subset_1(E, u1_struct_0(A)) => ((D = E) => (k8_relset_1(u1_struct_0(A), u1_struct_0(B), C, k6_domain_1(u1_struct_0(B), D)) = k2_pre_topc(A, k6_domain_1(u1_struct_0(A), E))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_tex_2)).
% 3.45/1.58  tff(f_72, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 3.45/1.58  tff(f_88, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 3.45/1.58  tff(f_46, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_subset_1)).
% 3.45/1.58  tff(f_105, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (v4_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => v3_tex_2(C, A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_tex_2)).
% 3.45/1.58  tff(f_120, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ~v3_tex_2(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_tex_2)).
% 3.45/1.58  tff(f_27, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 3.45/1.58  tff(f_81, axiom, (![A, B, C]: (((~v1_xboole_0(A) & m1_subset_1(B, A)) & m1_subset_1(C, A)) => (k7_domain_1(A, B, C) = k2_tarski(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_domain_1)).
% 3.45/1.58  tff(f_65, axiom, (![A, B, C]: (((~v1_xboole_0(A) & m1_subset_1(B, A)) & m1_subset_1(C, A)) => m1_subset_1(k7_domain_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_domain_1)).
% 3.45/1.58  tff(f_158, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v4_tex_2(B, A)) & m1_pre_topc(B, A)) => (![C]: ((((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & v5_pre_topc(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (v3_borsuk_1(C, A, B) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => (![E]: (m1_subset_1(E, k1_zfmisc_1(u1_struct_0(A))) => ((D = E) => (k8_relset_1(u1_struct_0(A), u1_struct_0(B), C, D) = k2_pre_topc(A, E)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t76_tex_2)).
% 3.45/1.58  tff(c_62, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_197])).
% 3.45/1.58  tff(c_58, plain, (m1_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_197])).
% 3.45/1.58  tff(c_64, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_197])).
% 3.45/1.58  tff(c_44, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_197])).
% 3.45/1.58  tff(c_110, plain, (![A_128, B_129]: (k6_domain_1(A_128, B_129)=k1_tarski(B_129) | ~m1_subset_1(B_129, A_128) | v1_xboole_0(A_128))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.45/1.58  tff(c_122, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_6')=k1_tarski('#skF_6') | v1_xboole_0(u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_44, c_110])).
% 3.45/1.58  tff(c_343, plain, (v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_122])).
% 3.45/1.58  tff(c_349, plain, (![B_200, A_201]: (m1_subset_1(u1_struct_0(B_200), k1_zfmisc_1(u1_struct_0(A_201))) | ~m1_pre_topc(B_200, A_201) | ~l1_pre_topc(A_201))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.45/1.58  tff(c_16, plain, (![B_31, A_29]: (v1_xboole_0(B_31) | ~m1_subset_1(B_31, k1_zfmisc_1(A_29)) | ~v1_xboole_0(A_29))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.45/1.58  tff(c_367, plain, (![B_206, A_207]: (v1_xboole_0(u1_struct_0(B_206)) | ~v1_xboole_0(u1_struct_0(A_207)) | ~m1_pre_topc(B_206, A_207) | ~l1_pre_topc(A_207))), inference(resolution, [status(thm)], [c_349, c_16])).
% 3.45/1.58  tff(c_369, plain, (![B_206]: (v1_xboole_0(u1_struct_0(B_206)) | ~m1_pre_topc(B_206, '#skF_2') | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_343, c_367])).
% 3.45/1.58  tff(c_382, plain, (![B_213]: (v1_xboole_0(u1_struct_0(B_213)) | ~m1_pre_topc(B_213, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_369])).
% 3.45/1.58  tff(c_70, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_197])).
% 3.45/1.58  tff(c_68, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_197])).
% 3.45/1.58  tff(c_60, plain, (v4_tex_2('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_197])).
% 3.45/1.58  tff(c_42, plain, ('#skF_5'='#skF_6'), inference(cnfTransformation, [status(thm)], [f_197])).
% 3.45/1.58  tff(c_46, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_197])).
% 3.45/1.58  tff(c_71, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_46])).
% 3.45/1.58  tff(c_121, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_6')=k1_tarski('#skF_6') | v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_71, c_110])).
% 3.45/1.58  tff(c_123, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_121])).
% 3.45/1.58  tff(c_26, plain, (![B_49, A_47]: (m1_subset_1(u1_struct_0(B_49), k1_zfmisc_1(u1_struct_0(A_47))) | ~m1_pre_topc(B_49, A_47) | ~l1_pre_topc(A_47))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.45/1.58  tff(c_290, plain, (![B_188, A_189]: (v3_tex_2(u1_struct_0(B_188), A_189) | ~m1_subset_1(u1_struct_0(B_188), k1_zfmisc_1(u1_struct_0(A_189))) | ~v4_tex_2(B_188, A_189) | ~m1_pre_topc(B_188, A_189) | ~l1_pre_topc(A_189) | v2_struct_0(A_189))), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.45/1.58  tff(c_295, plain, (![B_190, A_191]: (v3_tex_2(u1_struct_0(B_190), A_191) | ~v4_tex_2(B_190, A_191) | v2_struct_0(A_191) | ~m1_pre_topc(B_190, A_191) | ~l1_pre_topc(A_191))), inference(resolution, [status(thm)], [c_26, c_290])).
% 3.45/1.58  tff(c_220, plain, (![B_165, A_166]: (~v3_tex_2(B_165, A_166) | ~m1_subset_1(B_165, k1_zfmisc_1(u1_struct_0(A_166))) | ~v1_xboole_0(B_165) | ~l1_pre_topc(A_166) | ~v2_pre_topc(A_166) | v2_struct_0(A_166))), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.45/1.58  tff(c_229, plain, (![B_49, A_47]: (~v3_tex_2(u1_struct_0(B_49), A_47) | ~v1_xboole_0(u1_struct_0(B_49)) | ~v2_pre_topc(A_47) | v2_struct_0(A_47) | ~m1_pre_topc(B_49, A_47) | ~l1_pre_topc(A_47))), inference(resolution, [status(thm)], [c_26, c_220])).
% 3.45/1.58  tff(c_300, plain, (![B_192, A_193]: (~v1_xboole_0(u1_struct_0(B_192)) | ~v2_pre_topc(A_193) | ~v4_tex_2(B_192, A_193) | v2_struct_0(A_193) | ~m1_pre_topc(B_192, A_193) | ~l1_pre_topc(A_193))), inference(resolution, [status(thm)], [c_295, c_229])).
% 3.45/1.58  tff(c_327, plain, (![A_199]: (~v2_pre_topc(A_199) | ~v4_tex_2('#skF_3', A_199) | v2_struct_0(A_199) | ~m1_pre_topc('#skF_3', A_199) | ~l1_pre_topc(A_199))), inference(resolution, [status(thm)], [c_123, c_300])).
% 3.45/1.58  tff(c_334, plain, (~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_60, c_327])).
% 3.45/1.58  tff(c_338, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_58, c_68, c_334])).
% 3.45/1.58  tff(c_340, plain, $false, inference(negUnitSimplification, [status(thm)], [c_70, c_338])).
% 3.45/1.58  tff(c_342, plain, (~v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_121])).
% 3.45/1.58  tff(c_387, plain, (~m1_pre_topc('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_382, c_342])).
% 3.45/1.58  tff(c_392, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_387])).
% 3.45/1.58  tff(c_393, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_6')=k1_tarski('#skF_6')), inference(splitRight, [status(thm)], [c_122])).
% 3.45/1.58  tff(c_341, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_6')=k1_tarski('#skF_6')), inference(splitRight, [status(thm)], [c_121])).
% 3.45/1.58  tff(c_40, plain, (k8_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4', k6_domain_1(u1_struct_0('#skF_3'), '#skF_5'))!=k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_197])).
% 3.45/1.58  tff(c_72, plain, (k8_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4', k6_domain_1(u1_struct_0('#skF_3'), '#skF_6'))!=k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40])).
% 3.45/1.58  tff(c_395, plain, (k8_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4', k1_tarski('#skF_6'))!=k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_341, c_72])).
% 3.45/1.58  tff(c_433, plain, (k8_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4', k1_tarski('#skF_6'))!=k2_pre_topc('#skF_2', k1_tarski('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_393, c_395])).
% 3.45/1.58  tff(c_56, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_197])).
% 3.45/1.58  tff(c_54, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_197])).
% 3.45/1.58  tff(c_52, plain, (v5_pre_topc('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_197])).
% 3.45/1.58  tff(c_48, plain, (v3_borsuk_1('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_197])).
% 3.45/1.58  tff(c_2, plain, (![A_1]: (k2_tarski(A_1, A_1)=k1_tarski(A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.45/1.58  tff(c_461, plain, (![A_241, B_242, C_243]: (k7_domain_1(A_241, B_242, C_243)=k2_tarski(B_242, C_243) | ~m1_subset_1(C_243, A_241) | ~m1_subset_1(B_242, A_241) | v1_xboole_0(A_241))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.45/1.58  tff(c_469, plain, (![B_242]: (k7_domain_1(u1_struct_0('#skF_3'), B_242, '#skF_6')=k2_tarski(B_242, '#skF_6') | ~m1_subset_1(B_242, u1_struct_0('#skF_3')) | v1_xboole_0(u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_71, c_461])).
% 3.45/1.58  tff(c_482, plain, (![B_244]: (k7_domain_1(u1_struct_0('#skF_3'), B_244, '#skF_6')=k2_tarski(B_244, '#skF_6') | ~m1_subset_1(B_244, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_342, c_469])).
% 3.45/1.58  tff(c_485, plain, (k7_domain_1(u1_struct_0('#skF_3'), '#skF_6', '#skF_6')=k2_tarski('#skF_6', '#skF_6')), inference(resolution, [status(thm)], [c_71, c_482])).
% 3.45/1.58  tff(c_487, plain, (k7_domain_1(u1_struct_0('#skF_3'), '#skF_6', '#skF_6')=k1_tarski('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_485])).
% 3.45/1.58  tff(c_20, plain, (![A_39, B_40, C_41]: (m1_subset_1(k7_domain_1(A_39, B_40, C_41), k1_zfmisc_1(A_39)) | ~m1_subset_1(C_41, A_39) | ~m1_subset_1(B_40, A_39) | v1_xboole_0(A_39))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.45/1.58  tff(c_491, plain, (m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_3')) | v1_xboole_0(u1_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_487, c_20])).
% 3.45/1.58  tff(c_495, plain, (m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | v1_xboole_0(u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_71, c_71, c_491])).
% 3.45/1.58  tff(c_496, plain, (m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_342, c_495])).
% 3.45/1.58  tff(c_50, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_197])).
% 3.45/1.58  tff(c_66, plain, (v3_tdlat_3('#skF_2')), inference(cnfTransformation, [status(thm)], [f_197])).
% 3.45/1.58  tff(c_394, plain, (~v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_122])).
% 3.45/1.58  tff(c_471, plain, (![B_242]: (k7_domain_1(u1_struct_0('#skF_2'), B_242, '#skF_6')=k2_tarski(B_242, '#skF_6') | ~m1_subset_1(B_242, u1_struct_0('#skF_2')) | v1_xboole_0(u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_44, c_461])).
% 3.45/1.58  tff(c_530, plain, (![B_249]: (k7_domain_1(u1_struct_0('#skF_2'), B_249, '#skF_6')=k2_tarski(B_249, '#skF_6') | ~m1_subset_1(B_249, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_394, c_471])).
% 3.45/1.58  tff(c_533, plain, (k7_domain_1(u1_struct_0('#skF_2'), '#skF_6', '#skF_6')=k2_tarski('#skF_6', '#skF_6')), inference(resolution, [status(thm)], [c_44, c_530])).
% 3.45/1.58  tff(c_535, plain, (k7_domain_1(u1_struct_0('#skF_2'), '#skF_6', '#skF_6')=k1_tarski('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_533])).
% 3.45/1.58  tff(c_539, plain, (m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_2')) | v1_xboole_0(u1_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_535, c_20])).
% 3.45/1.58  tff(c_543, plain, (m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | v1_xboole_0(u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_44, c_539])).
% 3.45/1.58  tff(c_544, plain, (m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_394, c_543])).
% 3.45/1.58  tff(c_749, plain, (![A_293, B_294, C_295, E_296]: (k8_relset_1(u1_struct_0(A_293), u1_struct_0(B_294), C_295, E_296)=k2_pre_topc(A_293, E_296) | ~m1_subset_1(E_296, k1_zfmisc_1(u1_struct_0(A_293))) | ~m1_subset_1(E_296, k1_zfmisc_1(u1_struct_0(B_294))) | ~v3_borsuk_1(C_295, A_293, B_294) | ~m1_subset_1(C_295, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_293), u1_struct_0(B_294)))) | ~v5_pre_topc(C_295, A_293, B_294) | ~v1_funct_2(C_295, u1_struct_0(A_293), u1_struct_0(B_294)) | ~v1_funct_1(C_295) | ~m1_pre_topc(B_294, A_293) | ~v4_tex_2(B_294, A_293) | v2_struct_0(B_294) | ~l1_pre_topc(A_293) | ~v3_tdlat_3(A_293) | ~v2_pre_topc(A_293) | v2_struct_0(A_293))), inference(cnfTransformation, [status(thm)], [f_158])).
% 3.45/1.58  tff(c_757, plain, (![B_294, C_295]: (k8_relset_1(u1_struct_0('#skF_2'), u1_struct_0(B_294), C_295, k1_tarski('#skF_6'))=k2_pre_topc('#skF_2', k1_tarski('#skF_6')) | ~m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0(B_294))) | ~v3_borsuk_1(C_295, '#skF_2', B_294) | ~m1_subset_1(C_295, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0(B_294)))) | ~v5_pre_topc(C_295, '#skF_2', B_294) | ~v1_funct_2(C_295, u1_struct_0('#skF_2'), u1_struct_0(B_294)) | ~v1_funct_1(C_295) | ~m1_pre_topc(B_294, '#skF_2') | ~v4_tex_2(B_294, '#skF_2') | v2_struct_0(B_294) | ~l1_pre_topc('#skF_2') | ~v3_tdlat_3('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_544, c_749])).
% 3.45/1.58  tff(c_772, plain, (![B_294, C_295]: (k8_relset_1(u1_struct_0('#skF_2'), u1_struct_0(B_294), C_295, k1_tarski('#skF_6'))=k2_pre_topc('#skF_2', k1_tarski('#skF_6')) | ~m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0(B_294))) | ~v3_borsuk_1(C_295, '#skF_2', B_294) | ~m1_subset_1(C_295, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0(B_294)))) | ~v5_pre_topc(C_295, '#skF_2', B_294) | ~v1_funct_2(C_295, u1_struct_0('#skF_2'), u1_struct_0(B_294)) | ~v1_funct_1(C_295) | ~m1_pre_topc(B_294, '#skF_2') | ~v4_tex_2(B_294, '#skF_2') | v2_struct_0(B_294) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_64, c_757])).
% 3.45/1.58  tff(c_837, plain, (![B_306, C_307]: (k8_relset_1(u1_struct_0('#skF_2'), u1_struct_0(B_306), C_307, k1_tarski('#skF_6'))=k2_pre_topc('#skF_2', k1_tarski('#skF_6')) | ~m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0(B_306))) | ~v3_borsuk_1(C_307, '#skF_2', B_306) | ~m1_subset_1(C_307, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0(B_306)))) | ~v5_pre_topc(C_307, '#skF_2', B_306) | ~v1_funct_2(C_307, u1_struct_0('#skF_2'), u1_struct_0(B_306)) | ~v1_funct_1(C_307) | ~m1_pre_topc(B_306, '#skF_2') | ~v4_tex_2(B_306, '#skF_2') | v2_struct_0(B_306))), inference(negUnitSimplification, [status(thm)], [c_70, c_772])).
% 3.45/1.58  tff(c_844, plain, (k8_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4', k1_tarski('#skF_6'))=k2_pre_topc('#skF_2', k1_tarski('#skF_6')) | ~m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~v3_borsuk_1('#skF_4', '#skF_2', '#skF_3') | ~v5_pre_topc('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_2') | ~v4_tex_2('#skF_3', '#skF_2') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_50, c_837])).
% 3.45/1.58  tff(c_848, plain, (k8_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4', k1_tarski('#skF_6'))=k2_pre_topc('#skF_2', k1_tarski('#skF_6')) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_56, c_54, c_52, c_48, c_496, c_844])).
% 3.45/1.58  tff(c_850, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_433, c_848])).
% 3.45/1.58  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.45/1.58  
% 3.45/1.58  Inference rules
% 3.45/1.58  ----------------------
% 3.45/1.58  #Ref     : 0
% 3.45/1.58  #Sup     : 174
% 3.45/1.58  #Fact    : 0
% 3.45/1.58  #Define  : 0
% 3.45/1.58  #Split   : 13
% 3.45/1.58  #Chain   : 0
% 3.45/1.58  #Close   : 0
% 3.45/1.58  
% 3.45/1.58  Ordering : KBO
% 3.45/1.58  
% 3.45/1.58  Simplification rules
% 3.45/1.58  ----------------------
% 3.45/1.58  #Subsume      : 17
% 3.45/1.58  #Demod        : 56
% 3.45/1.58  #Tautology    : 65
% 3.45/1.58  #SimpNegUnit  : 16
% 3.45/1.58  #BackRed      : 2
% 3.45/1.58  
% 3.45/1.58  #Partial instantiations: 0
% 3.45/1.58  #Strategies tried      : 1
% 3.45/1.58  
% 3.45/1.58  Timing (in seconds)
% 3.45/1.58  ----------------------
% 3.45/1.59  Preprocessing        : 0.36
% 3.45/1.59  Parsing              : 0.18
% 3.45/1.59  CNF conversion       : 0.03
% 3.45/1.59  Main loop            : 0.42
% 3.45/1.59  Inferencing          : 0.16
% 3.45/1.59  Reduction            : 0.12
% 3.45/1.59  Demodulation         : 0.09
% 3.45/1.59  BG Simplification    : 0.03
% 3.45/1.59  Subsumption          : 0.07
% 3.45/1.59  Abstraction          : 0.02
% 3.45/1.59  MUC search           : 0.00
% 3.45/1.59  Cooper               : 0.00
% 3.45/1.59  Total                : 0.81
% 3.45/1.59  Index Insertion      : 0.00
% 3.45/1.59  Index Deletion       : 0.00
% 3.45/1.59  Index Matching       : 0.00
% 3.45/1.59  BG Taut test         : 0.00
%------------------------------------------------------------------------------
