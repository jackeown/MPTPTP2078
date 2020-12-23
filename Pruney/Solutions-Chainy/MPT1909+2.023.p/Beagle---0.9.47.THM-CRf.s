%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:40 EST 2020

% Result     : Theorem 4.70s
% Output     : CNFRefutation 4.70s
% Verified   : 
% Statistics : Number of formulae       :  140 ( 270 expanded)
%              Number of leaves         :   54 ( 120 expanded)
%              Depth                    :   15
%              Number of atoms          :  297 (1236 expanded)
%              Number of equality atoms :   34 ( 170 expanded)
%              Maximal formula depth    :   20 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_pre_topc > v3_borsuk_1 > v1_funct_2 > v4_tex_2 > v3_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_pre_topc > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k8_relset_1 > k2_enumset1 > k7_domain_1 > k1_enumset1 > k6_domain_1 > k2_zfmisc_1 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_8 > #skF_4 > #skF_2

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

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(v4_tex_2,type,(
    v4_tex_2: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

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

tff(v3_tex_2,type,(
    v3_tex_2: ( $i * $i ) > $o )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k7_domain_1,type,(
    k7_domain_1: ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v3_tdlat_3,type,(
    v3_tdlat_3: $i > $o )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_207,negated_conjecture,(
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

tff(f_82,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_98,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_115,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_tex_2)).

tff(f_66,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(B)))
             => m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_pre_topc)).

tff(f_130,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( v1_xboole_0(B)
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
         => ~ v3_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_tex_2)).

tff(f_40,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_91,axiom,(
    ! [A,B,C] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A)
        & m1_subset_1(C,A) )
     => k7_domain_1(A,B,C) = k2_tarski(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_domain_1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A)
        & m1_subset_1(C,A) )
     => m1_subset_1(k7_domain_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_domain_1)).

tff(f_168,axiom,(
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

tff(c_74,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_207])).

tff(c_70,plain,(
    m1_pre_topc('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_207])).

tff(c_76,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_207])).

tff(c_56,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_207])).

tff(c_174,plain,(
    ! [A_155,B_156] :
      ( k6_domain_1(A_155,B_156) = k1_tarski(B_156)
      | ~ m1_subset_1(B_156,A_155)
      | v1_xboole_0(A_155) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_190,plain,
    ( k6_domain_1(u1_struct_0('#skF_4'),'#skF_8') = k1_tarski('#skF_8')
    | v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_56,c_174])).

tff(c_1039,plain,(
    v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_190])).

tff(c_1040,plain,(
    ! [B_293,A_294] :
      ( m1_subset_1(u1_struct_0(B_293),k1_zfmisc_1(u1_struct_0(A_294)))
      | ~ m1_pre_topc(B_293,A_294)
      | ~ l1_pre_topc(A_294) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_26,plain,(
    ! [A_38,B_39] :
      ( r1_tarski(A_38,B_39)
      | ~ m1_subset_1(A_38,k1_zfmisc_1(B_39)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_1049,plain,(
    ! [B_295,A_296] :
      ( r1_tarski(u1_struct_0(B_295),u1_struct_0(A_296))
      | ~ m1_pre_topc(B_295,A_296)
      | ~ l1_pre_topc(A_296) ) ),
    inference(resolution,[status(thm)],[c_1040,c_26])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_135,plain,(
    ! [C_144,B_145,A_146] :
      ( r2_hidden(C_144,B_145)
      | ~ r2_hidden(C_144,A_146)
      | ~ r1_tarski(A_146,B_145) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_152,plain,(
    ! [A_151,B_152] :
      ( r2_hidden('#skF_1'(A_151),B_152)
      | ~ r1_tarski(A_151,B_152)
      | v1_xboole_0(A_151) ) ),
    inference(resolution,[status(thm)],[c_4,c_135])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_159,plain,(
    ! [B_152,A_151] :
      ( ~ v1_xboole_0(B_152)
      | ~ r1_tarski(A_151,B_152)
      | v1_xboole_0(A_151) ) ),
    inference(resolution,[status(thm)],[c_152,c_2])).

tff(c_1098,plain,(
    ! [A_312,B_313] :
      ( ~ v1_xboole_0(u1_struct_0(A_312))
      | v1_xboole_0(u1_struct_0(B_313))
      | ~ m1_pre_topc(B_313,A_312)
      | ~ l1_pre_topc(A_312) ) ),
    inference(resolution,[status(thm)],[c_1049,c_159])).

tff(c_1100,plain,(
    ! [B_313] :
      ( v1_xboole_0(u1_struct_0(B_313))
      | ~ m1_pre_topc(B_313,'#skF_4')
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1039,c_1098])).

tff(c_1104,plain,(
    ! [B_314] :
      ( v1_xboole_0(u1_struct_0(B_314))
      | ~ m1_pre_topc(B_314,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_1100])).

tff(c_82,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_207])).

tff(c_72,plain,(
    v4_tex_2('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_207])).

tff(c_38,plain,(
    ! [B_57,A_55] :
      ( m1_subset_1(u1_struct_0(B_57),k1_zfmisc_1(u1_struct_0(A_55)))
      | ~ m1_pre_topc(B_57,A_55)
      | ~ l1_pre_topc(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_984,plain,(
    ! [B_289,A_290] :
      ( v3_tex_2(u1_struct_0(B_289),A_290)
      | ~ m1_subset_1(u1_struct_0(B_289),k1_zfmisc_1(u1_struct_0(A_290)))
      | ~ v4_tex_2(B_289,A_290)
      | ~ m1_pre_topc(B_289,A_290)
      | ~ l1_pre_topc(A_290)
      | v2_struct_0(A_290) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_1006,plain,(
    ! [B_291,A_292] :
      ( v3_tex_2(u1_struct_0(B_291),A_292)
      | ~ v4_tex_2(B_291,A_292)
      | v2_struct_0(A_292)
      | ~ m1_pre_topc(B_291,A_292)
      | ~ l1_pre_topc(A_292) ) ),
    inference(resolution,[status(thm)],[c_38,c_984])).

tff(c_54,plain,(
    '#skF_7' = '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_207])).

tff(c_58,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_207])).

tff(c_83,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_58])).

tff(c_189,plain,
    ( k6_domain_1(u1_struct_0('#skF_5'),'#skF_8') = k1_tarski('#skF_8')
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_83,c_174])).

tff(c_191,plain,(
    v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_189])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_2'(A_5,B_6),A_5)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_129,plain,(
    ! [A_142,B_143] :
      ( ~ r2_hidden('#skF_2'(A_142,B_143),B_143)
      | r1_tarski(A_142,B_143) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_134,plain,(
    ! [A_5] : r1_tarski(A_5,A_5) ),
    inference(resolution,[status(thm)],[c_10,c_129])).

tff(c_80,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_207])).

tff(c_28,plain,(
    ! [A_38,B_39] :
      ( m1_subset_1(A_38,k1_zfmisc_1(B_39))
      | ~ r1_tarski(A_38,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_317,plain,(
    ! [C_191,A_192,B_193] :
      ( m1_subset_1(C_191,k1_zfmisc_1(u1_struct_0(A_192)))
      | ~ m1_subset_1(C_191,k1_zfmisc_1(u1_struct_0(B_193)))
      | ~ m1_pre_topc(B_193,A_192)
      | ~ l1_pre_topc(A_192) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_356,plain,(
    ! [A_201,A_202,B_203] :
      ( m1_subset_1(A_201,k1_zfmisc_1(u1_struct_0(A_202)))
      | ~ m1_pre_topc(B_203,A_202)
      | ~ l1_pre_topc(A_202)
      | ~ r1_tarski(A_201,u1_struct_0(B_203)) ) ),
    inference(resolution,[status(thm)],[c_28,c_317])).

tff(c_358,plain,(
    ! [A_201] :
      ( m1_subset_1(A_201,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4')
      | ~ r1_tarski(A_201,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_70,c_356])).

tff(c_361,plain,(
    ! [A_201] :
      ( m1_subset_1(A_201,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r1_tarski(A_201,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_358])).

tff(c_679,plain,(
    ! [B_245,A_246] :
      ( ~ v3_tex_2(B_245,A_246)
      | ~ m1_subset_1(B_245,k1_zfmisc_1(u1_struct_0(A_246)))
      | ~ v1_xboole_0(B_245)
      | ~ l1_pre_topc(A_246)
      | ~ v2_pre_topc(A_246)
      | v2_struct_0(A_246) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_689,plain,(
    ! [A_201] :
      ( ~ v3_tex_2(A_201,'#skF_4')
      | ~ v1_xboole_0(A_201)
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ r1_tarski(A_201,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_361,c_679])).

tff(c_701,plain,(
    ! [A_201] :
      ( ~ v3_tex_2(A_201,'#skF_4')
      | ~ v1_xboole_0(A_201)
      | v2_struct_0('#skF_4')
      | ~ r1_tarski(A_201,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_76,c_689])).

tff(c_705,plain,(
    ! [A_247] :
      ( ~ v3_tex_2(A_247,'#skF_4')
      | ~ v1_xboole_0(A_247)
      | ~ r1_tarski(A_247,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_701])).

tff(c_725,plain,
    ( ~ v3_tex_2(u1_struct_0('#skF_5'),'#skF_4')
    | ~ v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_134,c_705])).

tff(c_739,plain,(
    ~ v3_tex_2(u1_struct_0('#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_191,c_725])).

tff(c_1020,plain,
    ( ~ v4_tex_2('#skF_5','#skF_4')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_5','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_1006,c_739])).

tff(c_1029,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_70,c_72,c_1020])).

tff(c_1031,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_1029])).

tff(c_1033,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_189])).

tff(c_1109,plain,(
    ~ m1_pre_topc('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_1104,c_1033])).

tff(c_1114,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_1109])).

tff(c_1115,plain,(
    k6_domain_1(u1_struct_0('#skF_4'),'#skF_8') = k1_tarski('#skF_8') ),
    inference(splitRight,[status(thm)],[c_190])).

tff(c_1032,plain,(
    k6_domain_1(u1_struct_0('#skF_5'),'#skF_8') = k1_tarski('#skF_8') ),
    inference(splitRight,[status(thm)],[c_189])).

tff(c_52,plain,(
    k8_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6',k6_domain_1(u1_struct_0('#skF_5'),'#skF_7')) != k2_pre_topc('#skF_4',k6_domain_1(u1_struct_0('#skF_4'),'#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_207])).

tff(c_84,plain,(
    k8_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6',k6_domain_1(u1_struct_0('#skF_5'),'#skF_8')) != k2_pre_topc('#skF_4',k6_domain_1(u1_struct_0('#skF_4'),'#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52])).

tff(c_1034,plain,(
    k8_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6',k1_tarski('#skF_8')) != k2_pre_topc('#skF_4',k6_domain_1(u1_struct_0('#skF_4'),'#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1032,c_84])).

tff(c_1172,plain,(
    k8_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6',k1_tarski('#skF_8')) != k2_pre_topc('#skF_4',k1_tarski('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1115,c_1034])).

tff(c_68,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_207])).

tff(c_66,plain,(
    v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_207])).

tff(c_64,plain,(
    v5_pre_topc('#skF_6','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_207])).

tff(c_60,plain,(
    v3_borsuk_1('#skF_6','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_207])).

tff(c_12,plain,(
    ! [A_10] : k2_tarski(A_10,A_10) = k1_tarski(A_10) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_1465,plain,(
    ! [A_388,B_389,C_390] :
      ( k7_domain_1(A_388,B_389,C_390) = k2_tarski(B_389,C_390)
      | ~ m1_subset_1(C_390,A_388)
      | ~ m1_subset_1(B_389,A_388)
      | v1_xboole_0(A_388) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_1479,plain,(
    ! [B_389] :
      ( k7_domain_1(u1_struct_0('#skF_5'),B_389,'#skF_8') = k2_tarski(B_389,'#skF_8')
      | ~ m1_subset_1(B_389,u1_struct_0('#skF_5'))
      | v1_xboole_0(u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_83,c_1465])).

tff(c_1496,plain,(
    ! [B_391] :
      ( k7_domain_1(u1_struct_0('#skF_5'),B_391,'#skF_8') = k2_tarski(B_391,'#skF_8')
      | ~ m1_subset_1(B_391,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1033,c_1479])).

tff(c_1499,plain,(
    k7_domain_1(u1_struct_0('#skF_5'),'#skF_8','#skF_8') = k2_tarski('#skF_8','#skF_8') ),
    inference(resolution,[status(thm)],[c_83,c_1496])).

tff(c_1501,plain,(
    k7_domain_1(u1_struct_0('#skF_5'),'#skF_8','#skF_8') = k1_tarski('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_1499])).

tff(c_32,plain,(
    ! [A_47,B_48,C_49] :
      ( m1_subset_1(k7_domain_1(A_47,B_48,C_49),k1_zfmisc_1(A_47))
      | ~ m1_subset_1(C_49,A_47)
      | ~ m1_subset_1(B_48,A_47)
      | v1_xboole_0(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_1508,plain,
    ( m1_subset_1(k1_tarski('#skF_8'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1501,c_32])).

tff(c_1515,plain,
    ( m1_subset_1(k1_tarski('#skF_8'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_83,c_1508])).

tff(c_1516,plain,(
    m1_subset_1(k1_tarski('#skF_8'),k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_1033,c_1515])).

tff(c_62,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5')))) ),
    inference(cnfTransformation,[status(thm)],[f_207])).

tff(c_78,plain,(
    v3_tdlat_3('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_207])).

tff(c_1116,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_190])).

tff(c_1481,plain,(
    ! [B_389] :
      ( k7_domain_1(u1_struct_0('#skF_4'),B_389,'#skF_8') = k2_tarski(B_389,'#skF_8')
      | ~ m1_subset_1(B_389,u1_struct_0('#skF_4'))
      | v1_xboole_0(u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_56,c_1465])).

tff(c_1723,plain,(
    ! [B_408] :
      ( k7_domain_1(u1_struct_0('#skF_4'),B_408,'#skF_8') = k2_tarski(B_408,'#skF_8')
      | ~ m1_subset_1(B_408,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1116,c_1481])).

tff(c_1726,plain,(
    k7_domain_1(u1_struct_0('#skF_4'),'#skF_8','#skF_8') = k2_tarski('#skF_8','#skF_8') ),
    inference(resolution,[status(thm)],[c_56,c_1723])).

tff(c_1728,plain,(
    k7_domain_1(u1_struct_0('#skF_4'),'#skF_8','#skF_8') = k1_tarski('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_1726])).

tff(c_1735,plain,
    ( m1_subset_1(k1_tarski('#skF_8'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_4'))
    | v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1728,c_32])).

tff(c_1742,plain,
    ( m1_subset_1(k1_tarski('#skF_8'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_56,c_1735])).

tff(c_1743,plain,(
    m1_subset_1(k1_tarski('#skF_8'),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_1116,c_1742])).

tff(c_2130,plain,(
    ! [A_437,B_438,C_439,E_440] :
      ( k8_relset_1(u1_struct_0(A_437),u1_struct_0(B_438),C_439,E_440) = k2_pre_topc(A_437,E_440)
      | ~ m1_subset_1(E_440,k1_zfmisc_1(u1_struct_0(A_437)))
      | ~ m1_subset_1(E_440,k1_zfmisc_1(u1_struct_0(B_438)))
      | ~ v3_borsuk_1(C_439,A_437,B_438)
      | ~ m1_subset_1(C_439,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_437),u1_struct_0(B_438))))
      | ~ v5_pre_topc(C_439,A_437,B_438)
      | ~ v1_funct_2(C_439,u1_struct_0(A_437),u1_struct_0(B_438))
      | ~ v1_funct_1(C_439)
      | ~ m1_pre_topc(B_438,A_437)
      | ~ v4_tex_2(B_438,A_437)
      | v2_struct_0(B_438)
      | ~ l1_pre_topc(A_437)
      | ~ v3_tdlat_3(A_437)
      | ~ v2_pre_topc(A_437)
      | v2_struct_0(A_437) ) ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_2136,plain,(
    ! [B_438,C_439] :
      ( k8_relset_1(u1_struct_0('#skF_4'),u1_struct_0(B_438),C_439,k1_tarski('#skF_8')) = k2_pre_topc('#skF_4',k1_tarski('#skF_8'))
      | ~ m1_subset_1(k1_tarski('#skF_8'),k1_zfmisc_1(u1_struct_0(B_438)))
      | ~ v3_borsuk_1(C_439,'#skF_4',B_438)
      | ~ m1_subset_1(C_439,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_438))))
      | ~ v5_pre_topc(C_439,'#skF_4',B_438)
      | ~ v1_funct_2(C_439,u1_struct_0('#skF_4'),u1_struct_0(B_438))
      | ~ v1_funct_1(C_439)
      | ~ m1_pre_topc(B_438,'#skF_4')
      | ~ v4_tex_2(B_438,'#skF_4')
      | v2_struct_0(B_438)
      | ~ l1_pre_topc('#skF_4')
      | ~ v3_tdlat_3('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1743,c_2130])).

tff(c_2157,plain,(
    ! [B_438,C_439] :
      ( k8_relset_1(u1_struct_0('#skF_4'),u1_struct_0(B_438),C_439,k1_tarski('#skF_8')) = k2_pre_topc('#skF_4',k1_tarski('#skF_8'))
      | ~ m1_subset_1(k1_tarski('#skF_8'),k1_zfmisc_1(u1_struct_0(B_438)))
      | ~ v3_borsuk_1(C_439,'#skF_4',B_438)
      | ~ m1_subset_1(C_439,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_438))))
      | ~ v5_pre_topc(C_439,'#skF_4',B_438)
      | ~ v1_funct_2(C_439,u1_struct_0('#skF_4'),u1_struct_0(B_438))
      | ~ v1_funct_1(C_439)
      | ~ m1_pre_topc(B_438,'#skF_4')
      | ~ v4_tex_2(B_438,'#skF_4')
      | v2_struct_0(B_438)
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_76,c_2136])).

tff(c_2303,plain,(
    ! [B_452,C_453] :
      ( k8_relset_1(u1_struct_0('#skF_4'),u1_struct_0(B_452),C_453,k1_tarski('#skF_8')) = k2_pre_topc('#skF_4',k1_tarski('#skF_8'))
      | ~ m1_subset_1(k1_tarski('#skF_8'),k1_zfmisc_1(u1_struct_0(B_452)))
      | ~ v3_borsuk_1(C_453,'#skF_4',B_452)
      | ~ m1_subset_1(C_453,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_452))))
      | ~ v5_pre_topc(C_453,'#skF_4',B_452)
      | ~ v1_funct_2(C_453,u1_struct_0('#skF_4'),u1_struct_0(B_452))
      | ~ v1_funct_1(C_453)
      | ~ m1_pre_topc(B_452,'#skF_4')
      | ~ v4_tex_2(B_452,'#skF_4')
      | v2_struct_0(B_452) ) ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_2157])).

tff(c_2310,plain,
    ( k8_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6',k1_tarski('#skF_8')) = k2_pre_topc('#skF_4',k1_tarski('#skF_8'))
    | ~ m1_subset_1(k1_tarski('#skF_8'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ v3_borsuk_1('#skF_6','#skF_4','#skF_5')
    | ~ v5_pre_topc('#skF_6','#skF_4','#skF_5')
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_5'))
    | ~ v1_funct_1('#skF_6')
    | ~ m1_pre_topc('#skF_5','#skF_4')
    | ~ v4_tex_2('#skF_5','#skF_4')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_62,c_2303])).

tff(c_2318,plain,
    ( k8_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6',k1_tarski('#skF_8')) = k2_pre_topc('#skF_4',k1_tarski('#skF_8'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_68,c_66,c_64,c_60,c_1516,c_2310])).

tff(c_2320,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_1172,c_2318])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 09:58:19 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.70/1.87  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.70/1.88  
% 4.70/1.88  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.70/1.88  %$ v5_pre_topc > v3_borsuk_1 > v1_funct_2 > v4_tex_2 > v3_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_pre_topc > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k8_relset_1 > k2_enumset1 > k7_domain_1 > k1_enumset1 > k6_domain_1 > k2_zfmisc_1 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_8 > #skF_4 > #skF_2
% 4.70/1.88  
% 4.70/1.88  %Foreground sorts:
% 4.70/1.88  
% 4.70/1.88  
% 4.70/1.88  %Background operators:
% 4.70/1.88  
% 4.70/1.88  
% 4.70/1.88  %Foreground operators:
% 4.70/1.88  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.70/1.88  tff(v3_borsuk_1, type, v3_borsuk_1: ($i * $i * $i) > $o).
% 4.70/1.88  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.70/1.88  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.70/1.88  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.70/1.88  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.70/1.88  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 4.70/1.88  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.70/1.88  tff(v4_tex_2, type, v4_tex_2: ($i * $i) > $o).
% 4.70/1.88  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.70/1.88  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.70/1.88  tff('#skF_7', type, '#skF_7': $i).
% 4.70/1.88  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.70/1.88  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 4.70/1.88  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.70/1.88  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.70/1.88  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.70/1.88  tff('#skF_5', type, '#skF_5': $i).
% 4.70/1.88  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 4.70/1.88  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.70/1.88  tff('#skF_6', type, '#skF_6': $i).
% 4.70/1.88  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.70/1.88  tff(k7_domain_1, type, k7_domain_1: ($i * $i * $i) > $i).
% 4.70/1.88  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.70/1.88  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.70/1.88  tff(v3_tdlat_3, type, v3_tdlat_3: $i > $o).
% 4.70/1.88  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 4.70/1.88  tff('#skF_8', type, '#skF_8': $i).
% 4.70/1.88  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.70/1.88  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.70/1.88  tff('#skF_4', type, '#skF_4': $i).
% 4.70/1.88  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.70/1.88  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.70/1.88  tff(v5_pre_topc, type, v5_pre_topc: ($i * $i * $i) > $o).
% 4.70/1.88  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 4.70/1.88  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.70/1.88  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 4.70/1.88  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.70/1.88  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.70/1.88  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 4.70/1.88  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.70/1.88  
% 4.70/1.90  tff(f_207, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v4_tex_2(B, A)) & m1_pre_topc(B, A)) => (![C]: ((((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & v5_pre_topc(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (v3_borsuk_1(C, A, B) => (![D]: (m1_subset_1(D, u1_struct_0(B)) => (![E]: (m1_subset_1(E, u1_struct_0(A)) => ((D = E) => (k8_relset_1(u1_struct_0(A), u1_struct_0(B), C, k6_domain_1(u1_struct_0(B), D)) = k2_pre_topc(A, k6_domain_1(u1_struct_0(A), E))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_tex_2)).
% 4.70/1.90  tff(f_82, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 4.70/1.90  tff(f_98, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 4.70/1.90  tff(f_56, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 4.70/1.90  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 4.70/1.90  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 4.70/1.90  tff(f_115, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (v4_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => v3_tex_2(C, A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_tex_2)).
% 4.70/1.90  tff(f_66, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B))) => m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_pre_topc)).
% 4.70/1.90  tff(f_130, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ~v3_tex_2(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_tex_2)).
% 4.70/1.90  tff(f_40, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 4.70/1.90  tff(f_91, axiom, (![A, B, C]: (((~v1_xboole_0(A) & m1_subset_1(B, A)) & m1_subset_1(C, A)) => (k7_domain_1(A, B, C) = k2_tarski(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_domain_1)).
% 4.70/1.90  tff(f_75, axiom, (![A, B, C]: (((~v1_xboole_0(A) & m1_subset_1(B, A)) & m1_subset_1(C, A)) => m1_subset_1(k7_domain_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_domain_1)).
% 4.70/1.90  tff(f_168, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v4_tex_2(B, A)) & m1_pre_topc(B, A)) => (![C]: ((((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & v5_pre_topc(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (v3_borsuk_1(C, A, B) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => (![E]: (m1_subset_1(E, k1_zfmisc_1(u1_struct_0(A))) => ((D = E) => (k8_relset_1(u1_struct_0(A), u1_struct_0(B), C, D) = k2_pre_topc(A, E)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t76_tex_2)).
% 4.70/1.90  tff(c_74, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_207])).
% 4.70/1.90  tff(c_70, plain, (m1_pre_topc('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_207])).
% 4.70/1.90  tff(c_76, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_207])).
% 4.70/1.90  tff(c_56, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_207])).
% 4.70/1.90  tff(c_174, plain, (![A_155, B_156]: (k6_domain_1(A_155, B_156)=k1_tarski(B_156) | ~m1_subset_1(B_156, A_155) | v1_xboole_0(A_155))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.70/1.90  tff(c_190, plain, (k6_domain_1(u1_struct_0('#skF_4'), '#skF_8')=k1_tarski('#skF_8') | v1_xboole_0(u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_56, c_174])).
% 4.70/1.90  tff(c_1039, plain, (v1_xboole_0(u1_struct_0('#skF_4'))), inference(splitLeft, [status(thm)], [c_190])).
% 4.70/1.90  tff(c_1040, plain, (![B_293, A_294]: (m1_subset_1(u1_struct_0(B_293), k1_zfmisc_1(u1_struct_0(A_294))) | ~m1_pre_topc(B_293, A_294) | ~l1_pre_topc(A_294))), inference(cnfTransformation, [status(thm)], [f_98])).
% 4.70/1.90  tff(c_26, plain, (![A_38, B_39]: (r1_tarski(A_38, B_39) | ~m1_subset_1(A_38, k1_zfmisc_1(B_39)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.70/1.90  tff(c_1049, plain, (![B_295, A_296]: (r1_tarski(u1_struct_0(B_295), u1_struct_0(A_296)) | ~m1_pre_topc(B_295, A_296) | ~l1_pre_topc(A_296))), inference(resolution, [status(thm)], [c_1040, c_26])).
% 4.70/1.90  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.70/1.90  tff(c_135, plain, (![C_144, B_145, A_146]: (r2_hidden(C_144, B_145) | ~r2_hidden(C_144, A_146) | ~r1_tarski(A_146, B_145))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.70/1.90  tff(c_152, plain, (![A_151, B_152]: (r2_hidden('#skF_1'(A_151), B_152) | ~r1_tarski(A_151, B_152) | v1_xboole_0(A_151))), inference(resolution, [status(thm)], [c_4, c_135])).
% 4.70/1.90  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.70/1.90  tff(c_159, plain, (![B_152, A_151]: (~v1_xboole_0(B_152) | ~r1_tarski(A_151, B_152) | v1_xboole_0(A_151))), inference(resolution, [status(thm)], [c_152, c_2])).
% 4.70/1.90  tff(c_1098, plain, (![A_312, B_313]: (~v1_xboole_0(u1_struct_0(A_312)) | v1_xboole_0(u1_struct_0(B_313)) | ~m1_pre_topc(B_313, A_312) | ~l1_pre_topc(A_312))), inference(resolution, [status(thm)], [c_1049, c_159])).
% 4.70/1.90  tff(c_1100, plain, (![B_313]: (v1_xboole_0(u1_struct_0(B_313)) | ~m1_pre_topc(B_313, '#skF_4') | ~l1_pre_topc('#skF_4'))), inference(resolution, [status(thm)], [c_1039, c_1098])).
% 4.70/1.90  tff(c_1104, plain, (![B_314]: (v1_xboole_0(u1_struct_0(B_314)) | ~m1_pre_topc(B_314, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_1100])).
% 4.70/1.90  tff(c_82, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_207])).
% 4.70/1.90  tff(c_72, plain, (v4_tex_2('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_207])).
% 4.70/1.90  tff(c_38, plain, (![B_57, A_55]: (m1_subset_1(u1_struct_0(B_57), k1_zfmisc_1(u1_struct_0(A_55))) | ~m1_pre_topc(B_57, A_55) | ~l1_pre_topc(A_55))), inference(cnfTransformation, [status(thm)], [f_98])).
% 4.70/1.90  tff(c_984, plain, (![B_289, A_290]: (v3_tex_2(u1_struct_0(B_289), A_290) | ~m1_subset_1(u1_struct_0(B_289), k1_zfmisc_1(u1_struct_0(A_290))) | ~v4_tex_2(B_289, A_290) | ~m1_pre_topc(B_289, A_290) | ~l1_pre_topc(A_290) | v2_struct_0(A_290))), inference(cnfTransformation, [status(thm)], [f_115])).
% 4.70/1.90  tff(c_1006, plain, (![B_291, A_292]: (v3_tex_2(u1_struct_0(B_291), A_292) | ~v4_tex_2(B_291, A_292) | v2_struct_0(A_292) | ~m1_pre_topc(B_291, A_292) | ~l1_pre_topc(A_292))), inference(resolution, [status(thm)], [c_38, c_984])).
% 4.70/1.90  tff(c_54, plain, ('#skF_7'='#skF_8'), inference(cnfTransformation, [status(thm)], [f_207])).
% 4.70/1.90  tff(c_58, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_207])).
% 4.70/1.90  tff(c_83, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_58])).
% 4.70/1.90  tff(c_189, plain, (k6_domain_1(u1_struct_0('#skF_5'), '#skF_8')=k1_tarski('#skF_8') | v1_xboole_0(u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_83, c_174])).
% 4.70/1.90  tff(c_191, plain, (v1_xboole_0(u1_struct_0('#skF_5'))), inference(splitLeft, [status(thm)], [c_189])).
% 4.70/1.90  tff(c_10, plain, (![A_5, B_6]: (r2_hidden('#skF_2'(A_5, B_6), A_5) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.70/1.90  tff(c_129, plain, (![A_142, B_143]: (~r2_hidden('#skF_2'(A_142, B_143), B_143) | r1_tarski(A_142, B_143))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.70/1.90  tff(c_134, plain, (![A_5]: (r1_tarski(A_5, A_5))), inference(resolution, [status(thm)], [c_10, c_129])).
% 4.70/1.90  tff(c_80, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_207])).
% 4.70/1.90  tff(c_28, plain, (![A_38, B_39]: (m1_subset_1(A_38, k1_zfmisc_1(B_39)) | ~r1_tarski(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.70/1.90  tff(c_317, plain, (![C_191, A_192, B_193]: (m1_subset_1(C_191, k1_zfmisc_1(u1_struct_0(A_192))) | ~m1_subset_1(C_191, k1_zfmisc_1(u1_struct_0(B_193))) | ~m1_pre_topc(B_193, A_192) | ~l1_pre_topc(A_192))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.70/1.90  tff(c_356, plain, (![A_201, A_202, B_203]: (m1_subset_1(A_201, k1_zfmisc_1(u1_struct_0(A_202))) | ~m1_pre_topc(B_203, A_202) | ~l1_pre_topc(A_202) | ~r1_tarski(A_201, u1_struct_0(B_203)))), inference(resolution, [status(thm)], [c_28, c_317])).
% 4.70/1.90  tff(c_358, plain, (![A_201]: (m1_subset_1(A_201, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4') | ~r1_tarski(A_201, u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_70, c_356])).
% 4.70/1.90  tff(c_361, plain, (![A_201]: (m1_subset_1(A_201, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r1_tarski(A_201, u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_358])).
% 4.70/1.90  tff(c_679, plain, (![B_245, A_246]: (~v3_tex_2(B_245, A_246) | ~m1_subset_1(B_245, k1_zfmisc_1(u1_struct_0(A_246))) | ~v1_xboole_0(B_245) | ~l1_pre_topc(A_246) | ~v2_pre_topc(A_246) | v2_struct_0(A_246))), inference(cnfTransformation, [status(thm)], [f_130])).
% 4.70/1.90  tff(c_689, plain, (![A_201]: (~v3_tex_2(A_201, '#skF_4') | ~v1_xboole_0(A_201) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~r1_tarski(A_201, u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_361, c_679])).
% 4.70/1.90  tff(c_701, plain, (![A_201]: (~v3_tex_2(A_201, '#skF_4') | ~v1_xboole_0(A_201) | v2_struct_0('#skF_4') | ~r1_tarski(A_201, u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_76, c_689])).
% 4.70/1.90  tff(c_705, plain, (![A_247]: (~v3_tex_2(A_247, '#skF_4') | ~v1_xboole_0(A_247) | ~r1_tarski(A_247, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_82, c_701])).
% 4.70/1.90  tff(c_725, plain, (~v3_tex_2(u1_struct_0('#skF_5'), '#skF_4') | ~v1_xboole_0(u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_134, c_705])).
% 4.70/1.90  tff(c_739, plain, (~v3_tex_2(u1_struct_0('#skF_5'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_191, c_725])).
% 4.70/1.90  tff(c_1020, plain, (~v4_tex_2('#skF_5', '#skF_4') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_1006, c_739])).
% 4.70/1.90  tff(c_1029, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_70, c_72, c_1020])).
% 4.70/1.90  tff(c_1031, plain, $false, inference(negUnitSimplification, [status(thm)], [c_82, c_1029])).
% 4.70/1.90  tff(c_1033, plain, (~v1_xboole_0(u1_struct_0('#skF_5'))), inference(splitRight, [status(thm)], [c_189])).
% 4.70/1.90  tff(c_1109, plain, (~m1_pre_topc('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_1104, c_1033])).
% 4.70/1.90  tff(c_1114, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_1109])).
% 4.70/1.90  tff(c_1115, plain, (k6_domain_1(u1_struct_0('#skF_4'), '#skF_8')=k1_tarski('#skF_8')), inference(splitRight, [status(thm)], [c_190])).
% 4.70/1.90  tff(c_1032, plain, (k6_domain_1(u1_struct_0('#skF_5'), '#skF_8')=k1_tarski('#skF_8')), inference(splitRight, [status(thm)], [c_189])).
% 4.70/1.90  tff(c_52, plain, (k8_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6', k6_domain_1(u1_struct_0('#skF_5'), '#skF_7'))!=k2_pre_topc('#skF_4', k6_domain_1(u1_struct_0('#skF_4'), '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_207])).
% 4.70/1.90  tff(c_84, plain, (k8_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6', k6_domain_1(u1_struct_0('#skF_5'), '#skF_8'))!=k2_pre_topc('#skF_4', k6_domain_1(u1_struct_0('#skF_4'), '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52])).
% 4.70/1.90  tff(c_1034, plain, (k8_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6', k1_tarski('#skF_8'))!=k2_pre_topc('#skF_4', k6_domain_1(u1_struct_0('#skF_4'), '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_1032, c_84])).
% 4.70/1.90  tff(c_1172, plain, (k8_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6', k1_tarski('#skF_8'))!=k2_pre_topc('#skF_4', k1_tarski('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_1115, c_1034])).
% 4.70/1.90  tff(c_68, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_207])).
% 4.70/1.90  tff(c_66, plain, (v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_207])).
% 4.70/1.90  tff(c_64, plain, (v5_pre_topc('#skF_6', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_207])).
% 4.70/1.90  tff(c_60, plain, (v3_borsuk_1('#skF_6', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_207])).
% 4.70/1.90  tff(c_12, plain, (![A_10]: (k2_tarski(A_10, A_10)=k1_tarski(A_10))), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.70/1.90  tff(c_1465, plain, (![A_388, B_389, C_390]: (k7_domain_1(A_388, B_389, C_390)=k2_tarski(B_389, C_390) | ~m1_subset_1(C_390, A_388) | ~m1_subset_1(B_389, A_388) | v1_xboole_0(A_388))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.70/1.90  tff(c_1479, plain, (![B_389]: (k7_domain_1(u1_struct_0('#skF_5'), B_389, '#skF_8')=k2_tarski(B_389, '#skF_8') | ~m1_subset_1(B_389, u1_struct_0('#skF_5')) | v1_xboole_0(u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_83, c_1465])).
% 4.70/1.90  tff(c_1496, plain, (![B_391]: (k7_domain_1(u1_struct_0('#skF_5'), B_391, '#skF_8')=k2_tarski(B_391, '#skF_8') | ~m1_subset_1(B_391, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_1033, c_1479])).
% 4.70/1.90  tff(c_1499, plain, (k7_domain_1(u1_struct_0('#skF_5'), '#skF_8', '#skF_8')=k2_tarski('#skF_8', '#skF_8')), inference(resolution, [status(thm)], [c_83, c_1496])).
% 4.70/1.90  tff(c_1501, plain, (k7_domain_1(u1_struct_0('#skF_5'), '#skF_8', '#skF_8')=k1_tarski('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_1499])).
% 4.70/1.90  tff(c_32, plain, (![A_47, B_48, C_49]: (m1_subset_1(k7_domain_1(A_47, B_48, C_49), k1_zfmisc_1(A_47)) | ~m1_subset_1(C_49, A_47) | ~m1_subset_1(B_48, A_47) | v1_xboole_0(A_47))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.70/1.90  tff(c_1508, plain, (m1_subset_1(k1_tarski('#skF_8'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | v1_xboole_0(u1_struct_0('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_1501, c_32])).
% 4.70/1.90  tff(c_1515, plain, (m1_subset_1(k1_tarski('#skF_8'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | v1_xboole_0(u1_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_83, c_83, c_1508])).
% 4.70/1.90  tff(c_1516, plain, (m1_subset_1(k1_tarski('#skF_8'), k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_1033, c_1515])).
% 4.70/1.90  tff(c_62, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'))))), inference(cnfTransformation, [status(thm)], [f_207])).
% 4.70/1.90  tff(c_78, plain, (v3_tdlat_3('#skF_4')), inference(cnfTransformation, [status(thm)], [f_207])).
% 4.70/1.90  tff(c_1116, plain, (~v1_xboole_0(u1_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_190])).
% 4.70/1.90  tff(c_1481, plain, (![B_389]: (k7_domain_1(u1_struct_0('#skF_4'), B_389, '#skF_8')=k2_tarski(B_389, '#skF_8') | ~m1_subset_1(B_389, u1_struct_0('#skF_4')) | v1_xboole_0(u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_56, c_1465])).
% 4.70/1.90  tff(c_1723, plain, (![B_408]: (k7_domain_1(u1_struct_0('#skF_4'), B_408, '#skF_8')=k2_tarski(B_408, '#skF_8') | ~m1_subset_1(B_408, u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_1116, c_1481])).
% 4.70/1.90  tff(c_1726, plain, (k7_domain_1(u1_struct_0('#skF_4'), '#skF_8', '#skF_8')=k2_tarski('#skF_8', '#skF_8')), inference(resolution, [status(thm)], [c_56, c_1723])).
% 4.70/1.90  tff(c_1728, plain, (k7_domain_1(u1_struct_0('#skF_4'), '#skF_8', '#skF_8')=k1_tarski('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_1726])).
% 4.70/1.90  tff(c_1735, plain, (m1_subset_1(k1_tarski('#skF_8'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_4')) | v1_xboole_0(u1_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1728, c_32])).
% 4.70/1.90  tff(c_1742, plain, (m1_subset_1(k1_tarski('#skF_8'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | v1_xboole_0(u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_56, c_1735])).
% 4.70/1.90  tff(c_1743, plain, (m1_subset_1(k1_tarski('#skF_8'), k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_1116, c_1742])).
% 4.70/1.90  tff(c_2130, plain, (![A_437, B_438, C_439, E_440]: (k8_relset_1(u1_struct_0(A_437), u1_struct_0(B_438), C_439, E_440)=k2_pre_topc(A_437, E_440) | ~m1_subset_1(E_440, k1_zfmisc_1(u1_struct_0(A_437))) | ~m1_subset_1(E_440, k1_zfmisc_1(u1_struct_0(B_438))) | ~v3_borsuk_1(C_439, A_437, B_438) | ~m1_subset_1(C_439, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_437), u1_struct_0(B_438)))) | ~v5_pre_topc(C_439, A_437, B_438) | ~v1_funct_2(C_439, u1_struct_0(A_437), u1_struct_0(B_438)) | ~v1_funct_1(C_439) | ~m1_pre_topc(B_438, A_437) | ~v4_tex_2(B_438, A_437) | v2_struct_0(B_438) | ~l1_pre_topc(A_437) | ~v3_tdlat_3(A_437) | ~v2_pre_topc(A_437) | v2_struct_0(A_437))), inference(cnfTransformation, [status(thm)], [f_168])).
% 4.70/1.90  tff(c_2136, plain, (![B_438, C_439]: (k8_relset_1(u1_struct_0('#skF_4'), u1_struct_0(B_438), C_439, k1_tarski('#skF_8'))=k2_pre_topc('#skF_4', k1_tarski('#skF_8')) | ~m1_subset_1(k1_tarski('#skF_8'), k1_zfmisc_1(u1_struct_0(B_438))) | ~v3_borsuk_1(C_439, '#skF_4', B_438) | ~m1_subset_1(C_439, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_438)))) | ~v5_pre_topc(C_439, '#skF_4', B_438) | ~v1_funct_2(C_439, u1_struct_0('#skF_4'), u1_struct_0(B_438)) | ~v1_funct_1(C_439) | ~m1_pre_topc(B_438, '#skF_4') | ~v4_tex_2(B_438, '#skF_4') | v2_struct_0(B_438) | ~l1_pre_topc('#skF_4') | ~v3_tdlat_3('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_1743, c_2130])).
% 4.70/1.90  tff(c_2157, plain, (![B_438, C_439]: (k8_relset_1(u1_struct_0('#skF_4'), u1_struct_0(B_438), C_439, k1_tarski('#skF_8'))=k2_pre_topc('#skF_4', k1_tarski('#skF_8')) | ~m1_subset_1(k1_tarski('#skF_8'), k1_zfmisc_1(u1_struct_0(B_438))) | ~v3_borsuk_1(C_439, '#skF_4', B_438) | ~m1_subset_1(C_439, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_438)))) | ~v5_pre_topc(C_439, '#skF_4', B_438) | ~v1_funct_2(C_439, u1_struct_0('#skF_4'), u1_struct_0(B_438)) | ~v1_funct_1(C_439) | ~m1_pre_topc(B_438, '#skF_4') | ~v4_tex_2(B_438, '#skF_4') | v2_struct_0(B_438) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_76, c_2136])).
% 4.70/1.90  tff(c_2303, plain, (![B_452, C_453]: (k8_relset_1(u1_struct_0('#skF_4'), u1_struct_0(B_452), C_453, k1_tarski('#skF_8'))=k2_pre_topc('#skF_4', k1_tarski('#skF_8')) | ~m1_subset_1(k1_tarski('#skF_8'), k1_zfmisc_1(u1_struct_0(B_452))) | ~v3_borsuk_1(C_453, '#skF_4', B_452) | ~m1_subset_1(C_453, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_452)))) | ~v5_pre_topc(C_453, '#skF_4', B_452) | ~v1_funct_2(C_453, u1_struct_0('#skF_4'), u1_struct_0(B_452)) | ~v1_funct_1(C_453) | ~m1_pre_topc(B_452, '#skF_4') | ~v4_tex_2(B_452, '#skF_4') | v2_struct_0(B_452))), inference(negUnitSimplification, [status(thm)], [c_82, c_2157])).
% 4.70/1.90  tff(c_2310, plain, (k8_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6', k1_tarski('#skF_8'))=k2_pre_topc('#skF_4', k1_tarski('#skF_8')) | ~m1_subset_1(k1_tarski('#skF_8'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~v3_borsuk_1('#skF_6', '#skF_4', '#skF_5') | ~v5_pre_topc('#skF_6', '#skF_4', '#skF_5') | ~v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_5')) | ~v1_funct_1('#skF_6') | ~m1_pre_topc('#skF_5', '#skF_4') | ~v4_tex_2('#skF_5', '#skF_4') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_62, c_2303])).
% 4.70/1.90  tff(c_2318, plain, (k8_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6', k1_tarski('#skF_8'))=k2_pre_topc('#skF_4', k1_tarski('#skF_8')) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_68, c_66, c_64, c_60, c_1516, c_2310])).
% 4.70/1.90  tff(c_2320, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_1172, c_2318])).
% 4.70/1.90  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.70/1.90  
% 4.70/1.90  Inference rules
% 4.70/1.90  ----------------------
% 4.70/1.90  #Ref     : 0
% 4.70/1.90  #Sup     : 512
% 4.70/1.90  #Fact    : 0
% 4.70/1.90  #Define  : 0
% 4.70/1.90  #Split   : 20
% 4.70/1.90  #Chain   : 0
% 4.70/1.90  #Close   : 0
% 4.70/1.90  
% 4.70/1.90  Ordering : KBO
% 4.70/1.90  
% 4.70/1.90  Simplification rules
% 4.70/1.90  ----------------------
% 4.70/1.90  #Subsume      : 186
% 4.70/1.90  #Demod        : 100
% 4.70/1.90  #Tautology    : 84
% 4.70/1.90  #SimpNegUnit  : 53
% 4.70/1.90  #BackRed      : 14
% 4.70/1.90  
% 4.70/1.90  #Partial instantiations: 0
% 4.70/1.90  #Strategies tried      : 1
% 4.70/1.90  
% 4.70/1.90  Timing (in seconds)
% 4.70/1.90  ----------------------
% 4.70/1.91  Preprocessing        : 0.38
% 4.70/1.91  Parsing              : 0.20
% 4.70/1.91  CNF conversion       : 0.03
% 4.70/1.91  Main loop            : 0.72
% 4.70/1.91  Inferencing          : 0.24
% 4.70/1.91  Reduction            : 0.22
% 4.70/1.91  Demodulation         : 0.15
% 4.70/1.91  BG Simplification    : 0.03
% 4.70/1.91  Subsumption          : 0.17
% 4.70/1.91  Abstraction          : 0.03
% 4.70/1.91  MUC search           : 0.00
% 4.70/1.91  Cooper               : 0.00
% 4.70/1.91  Total                : 1.16
% 4.70/1.91  Index Insertion      : 0.00
% 4.70/1.91  Index Deletion       : 0.00
% 4.70/1.91  Index Matching       : 0.00
% 4.70/1.91  BG Taut test         : 0.00
%------------------------------------------------------------------------------
