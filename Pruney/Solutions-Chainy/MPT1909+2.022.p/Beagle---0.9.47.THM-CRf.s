%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:40 EST 2020

% Result     : Theorem 4.88s
% Output     : CNFRefutation 4.88s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 232 expanded)
%              Number of leaves         :   51 ( 106 expanded)
%              Depth                    :   12
%              Number of atoms          :  269 (1040 expanded)
%              Number of equality atoms :   22 ( 135 expanded)
%              Maximal formula depth    :   20 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_pre_topc > v3_borsuk_1 > v1_funct_2 > v4_tex_2 > v3_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_pre_topc > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k8_relset_1 > k2_enumset1 > k1_enumset1 > k6_domain_1 > k2_zfmisc_1 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_8 > #skF_4 > #skF_2

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

tff(f_196,negated_conjecture,(
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

tff(f_80,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_87,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_104,axiom,(
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

tff(f_66,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(B)))
             => m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_pre_topc)).

tff(f_119,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( v1_xboole_0(B)
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
         => ~ v3_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_tex_2)).

tff(f_73,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_157,axiom,(
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

tff(c_72,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_68,plain,(
    m1_pre_topc('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_74,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_54,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_172,plain,(
    ! [A_151,B_152] :
      ( k6_domain_1(A_151,B_152) = k1_tarski(B_152)
      | ~ m1_subset_1(B_152,A_151)
      | v1_xboole_0(A_151) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_188,plain,
    ( k6_domain_1(u1_struct_0('#skF_4'),'#skF_8') = k1_tarski('#skF_8')
    | v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_54,c_172])).

tff(c_1032,plain,(
    v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_188])).

tff(c_1080,plain,(
    ! [B_295,A_296] :
      ( m1_subset_1(u1_struct_0(B_295),k1_zfmisc_1(u1_struct_0(A_296)))
      | ~ m1_pre_topc(B_295,A_296)
      | ~ l1_pre_topc(A_296) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_26,plain,(
    ! [A_38,B_39] :
      ( r1_tarski(A_38,B_39)
      | ~ m1_subset_1(A_38,k1_zfmisc_1(B_39)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_1089,plain,(
    ! [B_297,A_298] :
      ( r1_tarski(u1_struct_0(B_297),u1_struct_0(A_298))
      | ~ m1_pre_topc(B_297,A_298)
      | ~ l1_pre_topc(A_298) ) ),
    inference(resolution,[status(thm)],[c_1080,c_26])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_143,plain,(
    ! [C_144,B_145,A_146] :
      ( r2_hidden(C_144,B_145)
      | ~ r2_hidden(C_144,A_146)
      | ~ r1_tarski(A_146,B_145) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_150,plain,(
    ! [A_147,B_148] :
      ( r2_hidden('#skF_1'(A_147),B_148)
      | ~ r1_tarski(A_147,B_148)
      | v1_xboole_0(A_147) ) ),
    inference(resolution,[status(thm)],[c_4,c_143])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_157,plain,(
    ! [B_148,A_147] :
      ( ~ v1_xboole_0(B_148)
      | ~ r1_tarski(A_147,B_148)
      | v1_xboole_0(A_147) ) ),
    inference(resolution,[status(thm)],[c_150,c_2])).

tff(c_1127,plain,(
    ! [A_305,B_306] :
      ( ~ v1_xboole_0(u1_struct_0(A_305))
      | v1_xboole_0(u1_struct_0(B_306))
      | ~ m1_pre_topc(B_306,A_305)
      | ~ l1_pre_topc(A_305) ) ),
    inference(resolution,[status(thm)],[c_1089,c_157])).

tff(c_1129,plain,(
    ! [B_306] :
      ( v1_xboole_0(u1_struct_0(B_306))
      | ~ m1_pre_topc(B_306,'#skF_4')
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1032,c_1127])).

tff(c_1133,plain,(
    ! [B_307] :
      ( v1_xboole_0(u1_struct_0(B_307))
      | ~ m1_pre_topc(B_307,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_1129])).

tff(c_80,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_70,plain,(
    v4_tex_2('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_36,plain,(
    ! [B_53,A_51] :
      ( m1_subset_1(u1_struct_0(B_53),k1_zfmisc_1(u1_struct_0(A_51)))
      | ~ m1_pre_topc(B_53,A_51)
      | ~ l1_pre_topc(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_977,plain,(
    ! [B_283,A_284] :
      ( v3_tex_2(u1_struct_0(B_283),A_284)
      | ~ m1_subset_1(u1_struct_0(B_283),k1_zfmisc_1(u1_struct_0(A_284)))
      | ~ v4_tex_2(B_283,A_284)
      | ~ m1_pre_topc(B_283,A_284)
      | ~ l1_pre_topc(A_284)
      | v2_struct_0(A_284) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_999,plain,(
    ! [B_285,A_286] :
      ( v3_tex_2(u1_struct_0(B_285),A_286)
      | ~ v4_tex_2(B_285,A_286)
      | v2_struct_0(A_286)
      | ~ m1_pre_topc(B_285,A_286)
      | ~ l1_pre_topc(A_286) ) ),
    inference(resolution,[status(thm)],[c_36,c_977])).

tff(c_52,plain,(
    '#skF_7' = '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_56,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_81,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_56])).

tff(c_187,plain,
    ( k6_domain_1(u1_struct_0('#skF_5'),'#skF_8') = k1_tarski('#skF_8')
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_81,c_172])).

tff(c_189,plain,(
    v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_187])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_2'(A_5,B_6),A_5)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_127,plain,(
    ! [A_138,B_139] :
      ( ~ r2_hidden('#skF_2'(A_138,B_139),B_139)
      | r1_tarski(A_138,B_139) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_132,plain,(
    ! [A_5] : r1_tarski(A_5,A_5) ),
    inference(resolution,[status(thm)],[c_10,c_127])).

tff(c_78,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_28,plain,(
    ! [A_38,B_39] :
      ( m1_subset_1(A_38,k1_zfmisc_1(B_39))
      | ~ r1_tarski(A_38,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_396,plain,(
    ! [C_204,A_205,B_206] :
      ( m1_subset_1(C_204,k1_zfmisc_1(u1_struct_0(A_205)))
      | ~ m1_subset_1(C_204,k1_zfmisc_1(u1_struct_0(B_206)))
      | ~ m1_pre_topc(B_206,A_205)
      | ~ l1_pre_topc(A_205) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_417,plain,(
    ! [A_213,A_214,B_215] :
      ( m1_subset_1(A_213,k1_zfmisc_1(u1_struct_0(A_214)))
      | ~ m1_pre_topc(B_215,A_214)
      | ~ l1_pre_topc(A_214)
      | ~ r1_tarski(A_213,u1_struct_0(B_215)) ) ),
    inference(resolution,[status(thm)],[c_28,c_396])).

tff(c_419,plain,(
    ! [A_213] :
      ( m1_subset_1(A_213,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4')
      | ~ r1_tarski(A_213,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_68,c_417])).

tff(c_422,plain,(
    ! [A_213] :
      ( m1_subset_1(A_213,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r1_tarski(A_213,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_419])).

tff(c_694,plain,(
    ! [B_242,A_243] :
      ( ~ v3_tex_2(B_242,A_243)
      | ~ m1_subset_1(B_242,k1_zfmisc_1(u1_struct_0(A_243)))
      | ~ v1_xboole_0(B_242)
      | ~ l1_pre_topc(A_243)
      | ~ v2_pre_topc(A_243)
      | v2_struct_0(A_243) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_700,plain,(
    ! [A_213] :
      ( ~ v3_tex_2(A_213,'#skF_4')
      | ~ v1_xboole_0(A_213)
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ r1_tarski(A_213,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_422,c_694])).

tff(c_715,plain,(
    ! [A_213] :
      ( ~ v3_tex_2(A_213,'#skF_4')
      | ~ v1_xboole_0(A_213)
      | v2_struct_0('#skF_4')
      | ~ r1_tarski(A_213,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_74,c_700])).

tff(c_720,plain,(
    ! [A_244] :
      ( ~ v3_tex_2(A_244,'#skF_4')
      | ~ v1_xboole_0(A_244)
      | ~ r1_tarski(A_244,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_715])).

tff(c_740,plain,
    ( ~ v3_tex_2(u1_struct_0('#skF_5'),'#skF_4')
    | ~ v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_132,c_720])).

tff(c_754,plain,(
    ~ v3_tex_2(u1_struct_0('#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_189,c_740])).

tff(c_1013,plain,
    ( ~ v4_tex_2('#skF_5','#skF_4')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_5','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_999,c_754])).

tff(c_1022,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_68,c_70,c_1013])).

tff(c_1024,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_1022])).

tff(c_1026,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_187])).

tff(c_1138,plain,(
    ~ m1_pre_topc('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_1133,c_1026])).

tff(c_1143,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_1138])).

tff(c_1144,plain,(
    k6_domain_1(u1_struct_0('#skF_4'),'#skF_8') = k1_tarski('#skF_8') ),
    inference(splitRight,[status(thm)],[c_188])).

tff(c_1025,plain,(
    k6_domain_1(u1_struct_0('#skF_5'),'#skF_8') = k1_tarski('#skF_8') ),
    inference(splitRight,[status(thm)],[c_187])).

tff(c_50,plain,(
    k8_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6',k6_domain_1(u1_struct_0('#skF_5'),'#skF_7')) != k2_pre_topc('#skF_4',k6_domain_1(u1_struct_0('#skF_4'),'#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_82,plain,(
    k8_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6',k6_domain_1(u1_struct_0('#skF_5'),'#skF_8')) != k2_pre_topc('#skF_4',k6_domain_1(u1_struct_0('#skF_4'),'#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50])).

tff(c_1027,plain,(
    k8_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6',k1_tarski('#skF_8')) != k2_pre_topc('#skF_4',k6_domain_1(u1_struct_0('#skF_4'),'#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1025,c_82])).

tff(c_1258,plain,(
    k8_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6',k1_tarski('#skF_8')) != k2_pre_topc('#skF_4',k1_tarski('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1144,c_1027])).

tff(c_66,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_64,plain,(
    v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_62,plain,(
    v5_pre_topc('#skF_6','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_58,plain,(
    v3_borsuk_1('#skF_6','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_1174,plain,(
    ! [A_316,B_317] :
      ( m1_subset_1(k6_domain_1(A_316,B_317),k1_zfmisc_1(A_316))
      | ~ m1_subset_1(B_317,A_316)
      | v1_xboole_0(A_316) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1186,plain,
    ( m1_subset_1(k1_tarski('#skF_8'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1025,c_1174])).

tff(c_1193,plain,
    ( m1_subset_1(k1_tarski('#skF_8'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_1186])).

tff(c_1194,plain,(
    m1_subset_1(k1_tarski('#skF_8'),k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_1026,c_1193])).

tff(c_60,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5')))) ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_76,plain,(
    v3_tdlat_3('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_1145,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_188])).

tff(c_1183,plain,
    ( m1_subset_1(k1_tarski('#skF_8'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_4'))
    | v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1144,c_1174])).

tff(c_1190,plain,
    ( m1_subset_1(k1_tarski('#skF_8'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_1183])).

tff(c_1191,plain,(
    m1_subset_1(k1_tarski('#skF_8'),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_1145,c_1190])).

tff(c_2326,plain,(
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
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_2340,plain,(
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
    inference(resolution,[status(thm)],[c_1191,c_2326])).

tff(c_2361,plain,(
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
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_74,c_2340])).

tff(c_2414,plain,(
    ! [B_446,C_447] :
      ( k8_relset_1(u1_struct_0('#skF_4'),u1_struct_0(B_446),C_447,k1_tarski('#skF_8')) = k2_pre_topc('#skF_4',k1_tarski('#skF_8'))
      | ~ m1_subset_1(k1_tarski('#skF_8'),k1_zfmisc_1(u1_struct_0(B_446)))
      | ~ v3_borsuk_1(C_447,'#skF_4',B_446)
      | ~ m1_subset_1(C_447,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_446))))
      | ~ v5_pre_topc(C_447,'#skF_4',B_446)
      | ~ v1_funct_2(C_447,u1_struct_0('#skF_4'),u1_struct_0(B_446))
      | ~ v1_funct_1(C_447)
      | ~ m1_pre_topc(B_446,'#skF_4')
      | ~ v4_tex_2(B_446,'#skF_4')
      | v2_struct_0(B_446) ) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_2361])).

tff(c_2421,plain,
    ( k8_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6',k1_tarski('#skF_8')) = k2_pre_topc('#skF_4',k1_tarski('#skF_8'))
    | ~ m1_subset_1(k1_tarski('#skF_8'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ v3_borsuk_1('#skF_6','#skF_4','#skF_5')
    | ~ v5_pre_topc('#skF_6','#skF_4','#skF_5')
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_5'))
    | ~ v1_funct_1('#skF_6')
    | ~ m1_pre_topc('#skF_5','#skF_4')
    | ~ v4_tex_2('#skF_5','#skF_4')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_60,c_2414])).

tff(c_2429,plain,
    ( k8_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6',k1_tarski('#skF_8')) = k2_pre_topc('#skF_4',k1_tarski('#skF_8'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_64,c_62,c_58,c_1194,c_2421])).

tff(c_2431,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_1258,c_2429])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:17:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.88/1.86  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.88/1.87  
% 4.88/1.87  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.88/1.87  %$ v5_pre_topc > v3_borsuk_1 > v1_funct_2 > v4_tex_2 > v3_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_pre_topc > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k8_relset_1 > k2_enumset1 > k1_enumset1 > k6_domain_1 > k2_zfmisc_1 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_8 > #skF_4 > #skF_2
% 4.88/1.87  
% 4.88/1.87  %Foreground sorts:
% 4.88/1.87  
% 4.88/1.87  
% 4.88/1.87  %Background operators:
% 4.88/1.87  
% 4.88/1.87  
% 4.88/1.87  %Foreground operators:
% 4.88/1.87  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.88/1.87  tff(v3_borsuk_1, type, v3_borsuk_1: ($i * $i * $i) > $o).
% 4.88/1.87  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.88/1.87  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.88/1.87  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.88/1.87  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.88/1.87  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 4.88/1.87  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.88/1.87  tff(v4_tex_2, type, v4_tex_2: ($i * $i) > $o).
% 4.88/1.87  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.88/1.87  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.88/1.87  tff('#skF_7', type, '#skF_7': $i).
% 4.88/1.87  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.88/1.87  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 4.88/1.87  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.88/1.87  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.88/1.87  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.88/1.87  tff('#skF_5', type, '#skF_5': $i).
% 4.88/1.87  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 4.88/1.87  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.88/1.87  tff('#skF_6', type, '#skF_6': $i).
% 4.88/1.87  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.88/1.87  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.88/1.87  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.88/1.87  tff(v3_tdlat_3, type, v3_tdlat_3: $i > $o).
% 4.88/1.87  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 4.88/1.87  tff('#skF_8', type, '#skF_8': $i).
% 4.88/1.87  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.88/1.87  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.88/1.87  tff('#skF_4', type, '#skF_4': $i).
% 4.88/1.87  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.88/1.87  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.88/1.87  tff(v5_pre_topc, type, v5_pre_topc: ($i * $i * $i) > $o).
% 4.88/1.87  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 4.88/1.87  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.88/1.87  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 4.88/1.87  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.88/1.87  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.88/1.87  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 4.88/1.87  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.88/1.87  
% 4.88/1.89  tff(f_196, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v4_tex_2(B, A)) & m1_pre_topc(B, A)) => (![C]: ((((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & v5_pre_topc(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (v3_borsuk_1(C, A, B) => (![D]: (m1_subset_1(D, u1_struct_0(B)) => (![E]: (m1_subset_1(E, u1_struct_0(A)) => ((D = E) => (k8_relset_1(u1_struct_0(A), u1_struct_0(B), C, k6_domain_1(u1_struct_0(B), D)) = k2_pre_topc(A, k6_domain_1(u1_struct_0(A), E))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_tex_2)).
% 4.88/1.89  tff(f_80, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 4.88/1.89  tff(f_87, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 4.88/1.89  tff(f_56, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 4.88/1.89  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 4.88/1.89  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 4.88/1.89  tff(f_104, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (v4_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => v3_tex_2(C, A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_tex_2)).
% 4.88/1.89  tff(f_66, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B))) => m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_pre_topc)).
% 4.88/1.89  tff(f_119, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ~v3_tex_2(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_tex_2)).
% 4.88/1.89  tff(f_73, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 4.88/1.89  tff(f_157, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v4_tex_2(B, A)) & m1_pre_topc(B, A)) => (![C]: ((((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & v5_pre_topc(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (v3_borsuk_1(C, A, B) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => (![E]: (m1_subset_1(E, k1_zfmisc_1(u1_struct_0(A))) => ((D = E) => (k8_relset_1(u1_struct_0(A), u1_struct_0(B), C, D) = k2_pre_topc(A, E)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t76_tex_2)).
% 4.88/1.89  tff(c_72, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_196])).
% 4.88/1.89  tff(c_68, plain, (m1_pre_topc('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_196])).
% 4.88/1.89  tff(c_74, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_196])).
% 4.88/1.89  tff(c_54, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_196])).
% 4.88/1.89  tff(c_172, plain, (![A_151, B_152]: (k6_domain_1(A_151, B_152)=k1_tarski(B_152) | ~m1_subset_1(B_152, A_151) | v1_xboole_0(A_151))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.88/1.89  tff(c_188, plain, (k6_domain_1(u1_struct_0('#skF_4'), '#skF_8')=k1_tarski('#skF_8') | v1_xboole_0(u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_54, c_172])).
% 4.88/1.89  tff(c_1032, plain, (v1_xboole_0(u1_struct_0('#skF_4'))), inference(splitLeft, [status(thm)], [c_188])).
% 4.88/1.89  tff(c_1080, plain, (![B_295, A_296]: (m1_subset_1(u1_struct_0(B_295), k1_zfmisc_1(u1_struct_0(A_296))) | ~m1_pre_topc(B_295, A_296) | ~l1_pre_topc(A_296))), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.88/1.89  tff(c_26, plain, (![A_38, B_39]: (r1_tarski(A_38, B_39) | ~m1_subset_1(A_38, k1_zfmisc_1(B_39)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.88/1.89  tff(c_1089, plain, (![B_297, A_298]: (r1_tarski(u1_struct_0(B_297), u1_struct_0(A_298)) | ~m1_pre_topc(B_297, A_298) | ~l1_pre_topc(A_298))), inference(resolution, [status(thm)], [c_1080, c_26])).
% 4.88/1.89  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.88/1.89  tff(c_143, plain, (![C_144, B_145, A_146]: (r2_hidden(C_144, B_145) | ~r2_hidden(C_144, A_146) | ~r1_tarski(A_146, B_145))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.88/1.89  tff(c_150, plain, (![A_147, B_148]: (r2_hidden('#skF_1'(A_147), B_148) | ~r1_tarski(A_147, B_148) | v1_xboole_0(A_147))), inference(resolution, [status(thm)], [c_4, c_143])).
% 4.88/1.89  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.88/1.89  tff(c_157, plain, (![B_148, A_147]: (~v1_xboole_0(B_148) | ~r1_tarski(A_147, B_148) | v1_xboole_0(A_147))), inference(resolution, [status(thm)], [c_150, c_2])).
% 4.88/1.89  tff(c_1127, plain, (![A_305, B_306]: (~v1_xboole_0(u1_struct_0(A_305)) | v1_xboole_0(u1_struct_0(B_306)) | ~m1_pre_topc(B_306, A_305) | ~l1_pre_topc(A_305))), inference(resolution, [status(thm)], [c_1089, c_157])).
% 4.88/1.89  tff(c_1129, plain, (![B_306]: (v1_xboole_0(u1_struct_0(B_306)) | ~m1_pre_topc(B_306, '#skF_4') | ~l1_pre_topc('#skF_4'))), inference(resolution, [status(thm)], [c_1032, c_1127])).
% 4.88/1.89  tff(c_1133, plain, (![B_307]: (v1_xboole_0(u1_struct_0(B_307)) | ~m1_pre_topc(B_307, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_1129])).
% 4.88/1.89  tff(c_80, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_196])).
% 4.88/1.89  tff(c_70, plain, (v4_tex_2('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_196])).
% 4.88/1.89  tff(c_36, plain, (![B_53, A_51]: (m1_subset_1(u1_struct_0(B_53), k1_zfmisc_1(u1_struct_0(A_51))) | ~m1_pre_topc(B_53, A_51) | ~l1_pre_topc(A_51))), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.88/1.89  tff(c_977, plain, (![B_283, A_284]: (v3_tex_2(u1_struct_0(B_283), A_284) | ~m1_subset_1(u1_struct_0(B_283), k1_zfmisc_1(u1_struct_0(A_284))) | ~v4_tex_2(B_283, A_284) | ~m1_pre_topc(B_283, A_284) | ~l1_pre_topc(A_284) | v2_struct_0(A_284))), inference(cnfTransformation, [status(thm)], [f_104])).
% 4.88/1.89  tff(c_999, plain, (![B_285, A_286]: (v3_tex_2(u1_struct_0(B_285), A_286) | ~v4_tex_2(B_285, A_286) | v2_struct_0(A_286) | ~m1_pre_topc(B_285, A_286) | ~l1_pre_topc(A_286))), inference(resolution, [status(thm)], [c_36, c_977])).
% 4.88/1.89  tff(c_52, plain, ('#skF_7'='#skF_8'), inference(cnfTransformation, [status(thm)], [f_196])).
% 4.88/1.89  tff(c_56, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_196])).
% 4.88/1.89  tff(c_81, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_56])).
% 4.88/1.89  tff(c_187, plain, (k6_domain_1(u1_struct_0('#skF_5'), '#skF_8')=k1_tarski('#skF_8') | v1_xboole_0(u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_81, c_172])).
% 4.88/1.89  tff(c_189, plain, (v1_xboole_0(u1_struct_0('#skF_5'))), inference(splitLeft, [status(thm)], [c_187])).
% 4.88/1.89  tff(c_10, plain, (![A_5, B_6]: (r2_hidden('#skF_2'(A_5, B_6), A_5) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.88/1.89  tff(c_127, plain, (![A_138, B_139]: (~r2_hidden('#skF_2'(A_138, B_139), B_139) | r1_tarski(A_138, B_139))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.88/1.89  tff(c_132, plain, (![A_5]: (r1_tarski(A_5, A_5))), inference(resolution, [status(thm)], [c_10, c_127])).
% 4.88/1.89  tff(c_78, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_196])).
% 4.88/1.89  tff(c_28, plain, (![A_38, B_39]: (m1_subset_1(A_38, k1_zfmisc_1(B_39)) | ~r1_tarski(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.88/1.89  tff(c_396, plain, (![C_204, A_205, B_206]: (m1_subset_1(C_204, k1_zfmisc_1(u1_struct_0(A_205))) | ~m1_subset_1(C_204, k1_zfmisc_1(u1_struct_0(B_206))) | ~m1_pre_topc(B_206, A_205) | ~l1_pre_topc(A_205))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.88/1.89  tff(c_417, plain, (![A_213, A_214, B_215]: (m1_subset_1(A_213, k1_zfmisc_1(u1_struct_0(A_214))) | ~m1_pre_topc(B_215, A_214) | ~l1_pre_topc(A_214) | ~r1_tarski(A_213, u1_struct_0(B_215)))), inference(resolution, [status(thm)], [c_28, c_396])).
% 4.88/1.89  tff(c_419, plain, (![A_213]: (m1_subset_1(A_213, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4') | ~r1_tarski(A_213, u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_68, c_417])).
% 4.88/1.89  tff(c_422, plain, (![A_213]: (m1_subset_1(A_213, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r1_tarski(A_213, u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_419])).
% 4.88/1.89  tff(c_694, plain, (![B_242, A_243]: (~v3_tex_2(B_242, A_243) | ~m1_subset_1(B_242, k1_zfmisc_1(u1_struct_0(A_243))) | ~v1_xboole_0(B_242) | ~l1_pre_topc(A_243) | ~v2_pre_topc(A_243) | v2_struct_0(A_243))), inference(cnfTransformation, [status(thm)], [f_119])).
% 4.88/1.89  tff(c_700, plain, (![A_213]: (~v3_tex_2(A_213, '#skF_4') | ~v1_xboole_0(A_213) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~r1_tarski(A_213, u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_422, c_694])).
% 4.88/1.89  tff(c_715, plain, (![A_213]: (~v3_tex_2(A_213, '#skF_4') | ~v1_xboole_0(A_213) | v2_struct_0('#skF_4') | ~r1_tarski(A_213, u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_74, c_700])).
% 4.88/1.89  tff(c_720, plain, (![A_244]: (~v3_tex_2(A_244, '#skF_4') | ~v1_xboole_0(A_244) | ~r1_tarski(A_244, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_80, c_715])).
% 4.88/1.89  tff(c_740, plain, (~v3_tex_2(u1_struct_0('#skF_5'), '#skF_4') | ~v1_xboole_0(u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_132, c_720])).
% 4.88/1.89  tff(c_754, plain, (~v3_tex_2(u1_struct_0('#skF_5'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_189, c_740])).
% 4.88/1.89  tff(c_1013, plain, (~v4_tex_2('#skF_5', '#skF_4') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_999, c_754])).
% 4.88/1.89  tff(c_1022, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_68, c_70, c_1013])).
% 4.88/1.89  tff(c_1024, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_1022])).
% 4.88/1.89  tff(c_1026, plain, (~v1_xboole_0(u1_struct_0('#skF_5'))), inference(splitRight, [status(thm)], [c_187])).
% 4.88/1.89  tff(c_1138, plain, (~m1_pre_topc('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_1133, c_1026])).
% 4.88/1.89  tff(c_1143, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_68, c_1138])).
% 4.88/1.89  tff(c_1144, plain, (k6_domain_1(u1_struct_0('#skF_4'), '#skF_8')=k1_tarski('#skF_8')), inference(splitRight, [status(thm)], [c_188])).
% 4.88/1.89  tff(c_1025, plain, (k6_domain_1(u1_struct_0('#skF_5'), '#skF_8')=k1_tarski('#skF_8')), inference(splitRight, [status(thm)], [c_187])).
% 4.88/1.89  tff(c_50, plain, (k8_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6', k6_domain_1(u1_struct_0('#skF_5'), '#skF_7'))!=k2_pre_topc('#skF_4', k6_domain_1(u1_struct_0('#skF_4'), '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_196])).
% 4.88/1.89  tff(c_82, plain, (k8_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6', k6_domain_1(u1_struct_0('#skF_5'), '#skF_8'))!=k2_pre_topc('#skF_4', k6_domain_1(u1_struct_0('#skF_4'), '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50])).
% 4.88/1.89  tff(c_1027, plain, (k8_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6', k1_tarski('#skF_8'))!=k2_pre_topc('#skF_4', k6_domain_1(u1_struct_0('#skF_4'), '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_1025, c_82])).
% 4.88/1.89  tff(c_1258, plain, (k8_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6', k1_tarski('#skF_8'))!=k2_pre_topc('#skF_4', k1_tarski('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_1144, c_1027])).
% 4.88/1.89  tff(c_66, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_196])).
% 4.88/1.89  tff(c_64, plain, (v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_196])).
% 4.88/1.89  tff(c_62, plain, (v5_pre_topc('#skF_6', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_196])).
% 4.88/1.89  tff(c_58, plain, (v3_borsuk_1('#skF_6', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_196])).
% 4.88/1.89  tff(c_1174, plain, (![A_316, B_317]: (m1_subset_1(k6_domain_1(A_316, B_317), k1_zfmisc_1(A_316)) | ~m1_subset_1(B_317, A_316) | v1_xboole_0(A_316))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.88/1.89  tff(c_1186, plain, (m1_subset_1(k1_tarski('#skF_8'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | v1_xboole_0(u1_struct_0('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_1025, c_1174])).
% 4.88/1.89  tff(c_1193, plain, (m1_subset_1(k1_tarski('#skF_8'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | v1_xboole_0(u1_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_81, c_1186])).
% 4.88/1.89  tff(c_1194, plain, (m1_subset_1(k1_tarski('#skF_8'), k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_1026, c_1193])).
% 4.88/1.89  tff(c_60, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'))))), inference(cnfTransformation, [status(thm)], [f_196])).
% 4.88/1.89  tff(c_76, plain, (v3_tdlat_3('#skF_4')), inference(cnfTransformation, [status(thm)], [f_196])).
% 4.88/1.89  tff(c_1145, plain, (~v1_xboole_0(u1_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_188])).
% 4.88/1.89  tff(c_1183, plain, (m1_subset_1(k1_tarski('#skF_8'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_4')) | v1_xboole_0(u1_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1144, c_1174])).
% 4.88/1.89  tff(c_1190, plain, (m1_subset_1(k1_tarski('#skF_8'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | v1_xboole_0(u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_1183])).
% 4.88/1.89  tff(c_1191, plain, (m1_subset_1(k1_tarski('#skF_8'), k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_1145, c_1190])).
% 4.88/1.89  tff(c_2326, plain, (![A_437, B_438, C_439, E_440]: (k8_relset_1(u1_struct_0(A_437), u1_struct_0(B_438), C_439, E_440)=k2_pre_topc(A_437, E_440) | ~m1_subset_1(E_440, k1_zfmisc_1(u1_struct_0(A_437))) | ~m1_subset_1(E_440, k1_zfmisc_1(u1_struct_0(B_438))) | ~v3_borsuk_1(C_439, A_437, B_438) | ~m1_subset_1(C_439, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_437), u1_struct_0(B_438)))) | ~v5_pre_topc(C_439, A_437, B_438) | ~v1_funct_2(C_439, u1_struct_0(A_437), u1_struct_0(B_438)) | ~v1_funct_1(C_439) | ~m1_pre_topc(B_438, A_437) | ~v4_tex_2(B_438, A_437) | v2_struct_0(B_438) | ~l1_pre_topc(A_437) | ~v3_tdlat_3(A_437) | ~v2_pre_topc(A_437) | v2_struct_0(A_437))), inference(cnfTransformation, [status(thm)], [f_157])).
% 4.88/1.89  tff(c_2340, plain, (![B_438, C_439]: (k8_relset_1(u1_struct_0('#skF_4'), u1_struct_0(B_438), C_439, k1_tarski('#skF_8'))=k2_pre_topc('#skF_4', k1_tarski('#skF_8')) | ~m1_subset_1(k1_tarski('#skF_8'), k1_zfmisc_1(u1_struct_0(B_438))) | ~v3_borsuk_1(C_439, '#skF_4', B_438) | ~m1_subset_1(C_439, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_438)))) | ~v5_pre_topc(C_439, '#skF_4', B_438) | ~v1_funct_2(C_439, u1_struct_0('#skF_4'), u1_struct_0(B_438)) | ~v1_funct_1(C_439) | ~m1_pre_topc(B_438, '#skF_4') | ~v4_tex_2(B_438, '#skF_4') | v2_struct_0(B_438) | ~l1_pre_topc('#skF_4') | ~v3_tdlat_3('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_1191, c_2326])).
% 4.88/1.89  tff(c_2361, plain, (![B_438, C_439]: (k8_relset_1(u1_struct_0('#skF_4'), u1_struct_0(B_438), C_439, k1_tarski('#skF_8'))=k2_pre_topc('#skF_4', k1_tarski('#skF_8')) | ~m1_subset_1(k1_tarski('#skF_8'), k1_zfmisc_1(u1_struct_0(B_438))) | ~v3_borsuk_1(C_439, '#skF_4', B_438) | ~m1_subset_1(C_439, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_438)))) | ~v5_pre_topc(C_439, '#skF_4', B_438) | ~v1_funct_2(C_439, u1_struct_0('#skF_4'), u1_struct_0(B_438)) | ~v1_funct_1(C_439) | ~m1_pre_topc(B_438, '#skF_4') | ~v4_tex_2(B_438, '#skF_4') | v2_struct_0(B_438) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_74, c_2340])).
% 4.88/1.89  tff(c_2414, plain, (![B_446, C_447]: (k8_relset_1(u1_struct_0('#skF_4'), u1_struct_0(B_446), C_447, k1_tarski('#skF_8'))=k2_pre_topc('#skF_4', k1_tarski('#skF_8')) | ~m1_subset_1(k1_tarski('#skF_8'), k1_zfmisc_1(u1_struct_0(B_446))) | ~v3_borsuk_1(C_447, '#skF_4', B_446) | ~m1_subset_1(C_447, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_446)))) | ~v5_pre_topc(C_447, '#skF_4', B_446) | ~v1_funct_2(C_447, u1_struct_0('#skF_4'), u1_struct_0(B_446)) | ~v1_funct_1(C_447) | ~m1_pre_topc(B_446, '#skF_4') | ~v4_tex_2(B_446, '#skF_4') | v2_struct_0(B_446))), inference(negUnitSimplification, [status(thm)], [c_80, c_2361])).
% 4.88/1.89  tff(c_2421, plain, (k8_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6', k1_tarski('#skF_8'))=k2_pre_topc('#skF_4', k1_tarski('#skF_8')) | ~m1_subset_1(k1_tarski('#skF_8'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~v3_borsuk_1('#skF_6', '#skF_4', '#skF_5') | ~v5_pre_topc('#skF_6', '#skF_4', '#skF_5') | ~v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_5')) | ~v1_funct_1('#skF_6') | ~m1_pre_topc('#skF_5', '#skF_4') | ~v4_tex_2('#skF_5', '#skF_4') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_60, c_2414])).
% 4.88/1.89  tff(c_2429, plain, (k8_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6', k1_tarski('#skF_8'))=k2_pre_topc('#skF_4', k1_tarski('#skF_8')) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_64, c_62, c_58, c_1194, c_2421])).
% 4.88/1.89  tff(c_2431, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_1258, c_2429])).
% 4.88/1.89  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.88/1.89  
% 4.88/1.89  Inference rules
% 4.88/1.89  ----------------------
% 4.88/1.89  #Ref     : 0
% 4.88/1.89  #Sup     : 531
% 4.88/1.89  #Fact    : 0
% 4.88/1.89  #Define  : 0
% 4.88/1.89  #Split   : 22
% 4.88/1.89  #Chain   : 0
% 4.88/1.89  #Close   : 0
% 4.88/1.89  
% 4.88/1.89  Ordering : KBO
% 4.88/1.89  
% 4.88/1.89  Simplification rules
% 4.88/1.89  ----------------------
% 4.88/1.89  #Subsume      : 204
% 4.88/1.89  #Demod        : 102
% 4.88/1.89  #Tautology    : 84
% 4.88/1.89  #SimpNegUnit  : 70
% 4.88/1.89  #BackRed      : 16
% 4.88/1.89  
% 4.88/1.89  #Partial instantiations: 0
% 4.88/1.89  #Strategies tried      : 1
% 4.88/1.89  
% 4.88/1.89  Timing (in seconds)
% 4.88/1.89  ----------------------
% 4.88/1.89  Preprocessing        : 0.39
% 4.88/1.89  Parsing              : 0.20
% 4.88/1.89  CNF conversion       : 0.03
% 4.88/1.89  Main loop            : 0.73
% 4.88/1.89  Inferencing          : 0.26
% 4.88/1.89  Reduction            : 0.22
% 4.88/1.89  Demodulation         : 0.15
% 4.88/1.89  BG Simplification    : 0.03
% 4.88/1.89  Subsumption          : 0.16
% 4.88/1.89  Abstraction          : 0.03
% 4.88/1.89  MUC search           : 0.00
% 4.88/1.89  Cooper               : 0.00
% 4.88/1.89  Total                : 1.16
% 4.88/1.89  Index Insertion      : 0.00
% 4.88/1.89  Index Deletion       : 0.00
% 4.88/1.89  Index Matching       : 0.00
% 4.88/1.89  BG Taut test         : 0.00
%------------------------------------------------------------------------------
