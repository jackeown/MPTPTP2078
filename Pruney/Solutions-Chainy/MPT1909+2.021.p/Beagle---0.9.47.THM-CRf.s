%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:40 EST 2020

% Result     : Theorem 4.71s
% Output     : CNFRefutation 4.71s
% Verified   : 
% Statistics : Number of formulae       :  125 ( 237 expanded)
%              Number of leaves         :   47 ( 105 expanded)
%              Depth                    :   12
%              Number of atoms          :  274 (1084 expanded)
%              Number of equality atoms :   25 ( 145 expanded)
%              Maximal formula depth    :   20 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_pre_topc > v3_borsuk_1 > v1_funct_2 > v4_tex_2 > v3_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_pre_topc > k8_relset_1 > k6_domain_1 > k2_zfmisc_1 > k2_tarski > k2_pre_topc > k10_relat_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_8 > #skF_4 > #skF_2

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

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v3_tdlat_3,type,(
    v3_tdlat_3: $i > $o )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

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

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_188,negated_conjecture,(
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

tff(f_48,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_79,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_44,axiom,(
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

tff(f_96,axiom,(
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

tff(f_58,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(B)))
             => m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_pre_topc)).

tff(f_111,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( v1_xboole_0(B)
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
         => ~ v3_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_tex_2)).

tff(f_65,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_149,axiom,(
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

tff(c_62,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_50,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5')))) ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_1188,plain,(
    ! [A_266,B_267,C_268,D_269] :
      ( k8_relset_1(A_266,B_267,C_268,D_269) = k10_relat_1(C_268,D_269)
      | ~ m1_subset_1(C_268,k1_zfmisc_1(k2_zfmisc_1(A_266,B_267))) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_1198,plain,(
    ! [D_269] : k8_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6',D_269) = k10_relat_1('#skF_6',D_269) ),
    inference(resolution,[status(thm)],[c_50,c_1188])).

tff(c_58,plain,(
    m1_pre_topc('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_64,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_44,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_144,plain,(
    ! [A_123,B_124] :
      ( k6_domain_1(A_123,B_124) = k1_tarski(B_124)
      | ~ m1_subset_1(B_124,A_123)
      | v1_xboole_0(A_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_160,plain,
    ( k6_domain_1(u1_struct_0('#skF_4'),'#skF_8') = k1_tarski('#skF_8')
    | v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_44,c_144])).

tff(c_1002,plain,(
    v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_160])).

tff(c_1041,plain,(
    ! [B_245,A_246] :
      ( m1_subset_1(u1_struct_0(B_245),k1_zfmisc_1(u1_struct_0(A_246)))
      | ~ m1_pre_topc(B_245,A_246)
      | ~ l1_pre_topc(A_246) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_14,plain,(
    ! [A_11,B_12] :
      ( r1_tarski(A_11,B_12)
      | ~ m1_subset_1(A_11,k1_zfmisc_1(B_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_1050,plain,(
    ! [B_247,A_248] :
      ( r1_tarski(u1_struct_0(B_247),u1_struct_0(A_248))
      | ~ m1_pre_topc(B_247,A_248)
      | ~ l1_pre_topc(A_248) ) ),
    inference(resolution,[status(thm)],[c_1041,c_14])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_115,plain,(
    ! [C_116,B_117,A_118] :
      ( r2_hidden(C_116,B_117)
      | ~ r2_hidden(C_116,A_118)
      | ~ r1_tarski(A_118,B_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_122,plain,(
    ! [A_119,B_120] :
      ( r2_hidden('#skF_1'(A_119),B_120)
      | ~ r1_tarski(A_119,B_120)
      | v1_xboole_0(A_119) ) ),
    inference(resolution,[status(thm)],[c_4,c_115])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_129,plain,(
    ! [B_120,A_119] :
      ( ~ v1_xboole_0(B_120)
      | ~ r1_tarski(A_119,B_120)
      | v1_xboole_0(A_119) ) ),
    inference(resolution,[status(thm)],[c_122,c_2])).

tff(c_1088,plain,(
    ! [A_255,B_256] :
      ( ~ v1_xboole_0(u1_struct_0(A_255))
      | v1_xboole_0(u1_struct_0(B_256))
      | ~ m1_pre_topc(B_256,A_255)
      | ~ l1_pre_topc(A_255) ) ),
    inference(resolution,[status(thm)],[c_1050,c_129])).

tff(c_1090,plain,(
    ! [B_256] :
      ( v1_xboole_0(u1_struct_0(B_256))
      | ~ m1_pre_topc(B_256,'#skF_4')
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1002,c_1088])).

tff(c_1094,plain,(
    ! [B_257] :
      ( v1_xboole_0(u1_struct_0(B_257))
      | ~ m1_pre_topc(B_257,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_1090])).

tff(c_70,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_60,plain,(
    v4_tex_2('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_26,plain,(
    ! [B_30,A_28] :
      ( m1_subset_1(u1_struct_0(B_30),k1_zfmisc_1(u1_struct_0(A_28)))
      | ~ m1_pre_topc(B_30,A_28)
      | ~ l1_pre_topc(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_947,plain,(
    ! [B_237,A_238] :
      ( v3_tex_2(u1_struct_0(B_237),A_238)
      | ~ m1_subset_1(u1_struct_0(B_237),k1_zfmisc_1(u1_struct_0(A_238)))
      | ~ v4_tex_2(B_237,A_238)
      | ~ m1_pre_topc(B_237,A_238)
      | ~ l1_pre_topc(A_238)
      | v2_struct_0(A_238) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_969,plain,(
    ! [B_239,A_240] :
      ( v3_tex_2(u1_struct_0(B_239),A_240)
      | ~ v4_tex_2(B_239,A_240)
      | v2_struct_0(A_240)
      | ~ m1_pre_topc(B_239,A_240)
      | ~ l1_pre_topc(A_240) ) ),
    inference(resolution,[status(thm)],[c_26,c_947])).

tff(c_42,plain,(
    '#skF_7' = '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_46,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_71,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_46])).

tff(c_159,plain,
    ( k6_domain_1(u1_struct_0('#skF_5'),'#skF_8') = k1_tarski('#skF_8')
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_71,c_144])).

tff(c_161,plain,(
    v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_159])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_2'(A_5,B_6),A_5)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_108,plain,(
    ! [A_113,B_114] :
      ( ~ r2_hidden('#skF_2'(A_113,B_114),B_114)
      | r1_tarski(A_113,B_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_113,plain,(
    ! [A_5] : r1_tarski(A_5,A_5) ),
    inference(resolution,[status(thm)],[c_10,c_108])).

tff(c_68,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_16,plain,(
    ! [A_11,B_12] :
      ( m1_subset_1(A_11,k1_zfmisc_1(B_12))
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_388,plain,(
    ! [C_179,A_180,B_181] :
      ( m1_subset_1(C_179,k1_zfmisc_1(u1_struct_0(A_180)))
      | ~ m1_subset_1(C_179,k1_zfmisc_1(u1_struct_0(B_181)))
      | ~ m1_pre_topc(B_181,A_180)
      | ~ l1_pre_topc(A_180) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_467,plain,(
    ! [A_194,A_195,B_196] :
      ( m1_subset_1(A_194,k1_zfmisc_1(u1_struct_0(A_195)))
      | ~ m1_pre_topc(B_196,A_195)
      | ~ l1_pre_topc(A_195)
      | ~ r1_tarski(A_194,u1_struct_0(B_196)) ) ),
    inference(resolution,[status(thm)],[c_16,c_388])).

tff(c_469,plain,(
    ! [A_194] :
      ( m1_subset_1(A_194,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4')
      | ~ r1_tarski(A_194,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_58,c_467])).

tff(c_472,plain,(
    ! [A_194] :
      ( m1_subset_1(A_194,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r1_tarski(A_194,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_469])).

tff(c_671,plain,(
    ! [B_214,A_215] :
      ( ~ v3_tex_2(B_214,A_215)
      | ~ m1_subset_1(B_214,k1_zfmisc_1(u1_struct_0(A_215)))
      | ~ v1_xboole_0(B_214)
      | ~ l1_pre_topc(A_215)
      | ~ v2_pre_topc(A_215)
      | v2_struct_0(A_215) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_674,plain,(
    ! [A_194] :
      ( ~ v3_tex_2(A_194,'#skF_4')
      | ~ v1_xboole_0(A_194)
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ r1_tarski(A_194,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_472,c_671])).

tff(c_688,plain,(
    ! [A_194] :
      ( ~ v3_tex_2(A_194,'#skF_4')
      | ~ v1_xboole_0(A_194)
      | v2_struct_0('#skF_4')
      | ~ r1_tarski(A_194,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_64,c_674])).

tff(c_721,plain,(
    ! [A_218] :
      ( ~ v3_tex_2(A_218,'#skF_4')
      | ~ v1_xboole_0(A_218)
      | ~ r1_tarski(A_218,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_688])).

tff(c_741,plain,
    ( ~ v3_tex_2(u1_struct_0('#skF_5'),'#skF_4')
    | ~ v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_113,c_721])).

tff(c_755,plain,(
    ~ v3_tex_2(u1_struct_0('#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_161,c_741])).

tff(c_983,plain,
    ( ~ v4_tex_2('#skF_5','#skF_4')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_5','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_969,c_755])).

tff(c_992,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_58,c_60,c_983])).

tff(c_994,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_992])).

tff(c_996,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_159])).

tff(c_1099,plain,(
    ~ m1_pre_topc('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_1094,c_996])).

tff(c_1104,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_1099])).

tff(c_1105,plain,(
    k6_domain_1(u1_struct_0('#skF_4'),'#skF_8') = k1_tarski('#skF_8') ),
    inference(splitRight,[status(thm)],[c_160])).

tff(c_995,plain,(
    k6_domain_1(u1_struct_0('#skF_5'),'#skF_8') = k1_tarski('#skF_8') ),
    inference(splitRight,[status(thm)],[c_159])).

tff(c_40,plain,(
    k8_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6',k6_domain_1(u1_struct_0('#skF_5'),'#skF_7')) != k2_pre_topc('#skF_4',k6_domain_1(u1_struct_0('#skF_4'),'#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_72,plain,(
    k8_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6',k6_domain_1(u1_struct_0('#skF_5'),'#skF_8')) != k2_pre_topc('#skF_4',k6_domain_1(u1_struct_0('#skF_4'),'#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40])).

tff(c_997,plain,(
    k8_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6',k1_tarski('#skF_8')) != k2_pre_topc('#skF_4',k6_domain_1(u1_struct_0('#skF_4'),'#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_995,c_72])).

tff(c_1244,plain,(
    k2_pre_topc('#skF_4',k1_tarski('#skF_8')) != k10_relat_1('#skF_6',k1_tarski('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1198,c_1105,c_997])).

tff(c_56,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_54,plain,(
    v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_52,plain,(
    v5_pre_topc('#skF_6','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_48,plain,(
    v3_borsuk_1('#skF_6','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_1111,plain,(
    ! [A_258,B_259] :
      ( m1_subset_1(k6_domain_1(A_258,B_259),k1_zfmisc_1(A_258))
      | ~ m1_subset_1(B_259,A_258)
      | v1_xboole_0(A_258) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1123,plain,
    ( m1_subset_1(k1_tarski('#skF_8'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_995,c_1111])).

tff(c_1130,plain,
    ( m1_subset_1(k1_tarski('#skF_8'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_1123])).

tff(c_1131,plain,(
    m1_subset_1(k1_tarski('#skF_8'),k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_996,c_1130])).

tff(c_66,plain,(
    v3_tdlat_3('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_1106,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_160])).

tff(c_1120,plain,
    ( m1_subset_1(k1_tarski('#skF_8'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_4'))
    | v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1105,c_1111])).

tff(c_1127,plain,
    ( m1_subset_1(k1_tarski('#skF_8'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_1120])).

tff(c_1128,plain,(
    m1_subset_1(k1_tarski('#skF_8'),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_1106,c_1127])).

tff(c_2021,plain,(
    ! [A_368,B_369,C_370,E_371] :
      ( k8_relset_1(u1_struct_0(A_368),u1_struct_0(B_369),C_370,E_371) = k2_pre_topc(A_368,E_371)
      | ~ m1_subset_1(E_371,k1_zfmisc_1(u1_struct_0(A_368)))
      | ~ m1_subset_1(E_371,k1_zfmisc_1(u1_struct_0(B_369)))
      | ~ v3_borsuk_1(C_370,A_368,B_369)
      | ~ m1_subset_1(C_370,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_368),u1_struct_0(B_369))))
      | ~ v5_pre_topc(C_370,A_368,B_369)
      | ~ v1_funct_2(C_370,u1_struct_0(A_368),u1_struct_0(B_369))
      | ~ v1_funct_1(C_370)
      | ~ m1_pre_topc(B_369,A_368)
      | ~ v4_tex_2(B_369,A_368)
      | v2_struct_0(B_369)
      | ~ l1_pre_topc(A_368)
      | ~ v3_tdlat_3(A_368)
      | ~ v2_pre_topc(A_368)
      | v2_struct_0(A_368) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_2037,plain,(
    ! [B_369,C_370] :
      ( k8_relset_1(u1_struct_0('#skF_4'),u1_struct_0(B_369),C_370,k1_tarski('#skF_8')) = k2_pre_topc('#skF_4',k1_tarski('#skF_8'))
      | ~ m1_subset_1(k1_tarski('#skF_8'),k1_zfmisc_1(u1_struct_0(B_369)))
      | ~ v3_borsuk_1(C_370,'#skF_4',B_369)
      | ~ m1_subset_1(C_370,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_369))))
      | ~ v5_pre_topc(C_370,'#skF_4',B_369)
      | ~ v1_funct_2(C_370,u1_struct_0('#skF_4'),u1_struct_0(B_369))
      | ~ v1_funct_1(C_370)
      | ~ m1_pre_topc(B_369,'#skF_4')
      | ~ v4_tex_2(B_369,'#skF_4')
      | v2_struct_0(B_369)
      | ~ l1_pre_topc('#skF_4')
      | ~ v3_tdlat_3('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1128,c_2021])).

tff(c_2057,plain,(
    ! [B_369,C_370] :
      ( k8_relset_1(u1_struct_0('#skF_4'),u1_struct_0(B_369),C_370,k1_tarski('#skF_8')) = k2_pre_topc('#skF_4',k1_tarski('#skF_8'))
      | ~ m1_subset_1(k1_tarski('#skF_8'),k1_zfmisc_1(u1_struct_0(B_369)))
      | ~ v3_borsuk_1(C_370,'#skF_4',B_369)
      | ~ m1_subset_1(C_370,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_369))))
      | ~ v5_pre_topc(C_370,'#skF_4',B_369)
      | ~ v1_funct_2(C_370,u1_struct_0('#skF_4'),u1_struct_0(B_369))
      | ~ v1_funct_1(C_370)
      | ~ m1_pre_topc(B_369,'#skF_4')
      | ~ v4_tex_2(B_369,'#skF_4')
      | v2_struct_0(B_369)
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_64,c_2037])).

tff(c_2106,plain,(
    ! [B_375,C_376] :
      ( k8_relset_1(u1_struct_0('#skF_4'),u1_struct_0(B_375),C_376,k1_tarski('#skF_8')) = k2_pre_topc('#skF_4',k1_tarski('#skF_8'))
      | ~ m1_subset_1(k1_tarski('#skF_8'),k1_zfmisc_1(u1_struct_0(B_375)))
      | ~ v3_borsuk_1(C_376,'#skF_4',B_375)
      | ~ m1_subset_1(C_376,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_375))))
      | ~ v5_pre_topc(C_376,'#skF_4',B_375)
      | ~ v1_funct_2(C_376,u1_struct_0('#skF_4'),u1_struct_0(B_375))
      | ~ v1_funct_1(C_376)
      | ~ m1_pre_topc(B_375,'#skF_4')
      | ~ v4_tex_2(B_375,'#skF_4')
      | v2_struct_0(B_375) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_2057])).

tff(c_2113,plain,
    ( k8_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6',k1_tarski('#skF_8')) = k2_pre_topc('#skF_4',k1_tarski('#skF_8'))
    | ~ m1_subset_1(k1_tarski('#skF_8'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ v3_borsuk_1('#skF_6','#skF_4','#skF_5')
    | ~ v5_pre_topc('#skF_6','#skF_4','#skF_5')
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_5'))
    | ~ v1_funct_1('#skF_6')
    | ~ m1_pre_topc('#skF_5','#skF_4')
    | ~ v4_tex_2('#skF_5','#skF_4')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_2106])).

tff(c_2121,plain,
    ( k2_pre_topc('#skF_4',k1_tarski('#skF_8')) = k10_relat_1('#skF_6',k1_tarski('#skF_8'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_56,c_54,c_52,c_48,c_1131,c_1198,c_2113])).

tff(c_2123,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_1244,c_2121])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:53:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.71/1.85  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.71/1.86  
% 4.71/1.86  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.71/1.86  %$ v5_pre_topc > v3_borsuk_1 > v1_funct_2 > v4_tex_2 > v3_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_pre_topc > k8_relset_1 > k6_domain_1 > k2_zfmisc_1 > k2_tarski > k2_pre_topc > k10_relat_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_8 > #skF_4 > #skF_2
% 4.71/1.86  
% 4.71/1.86  %Foreground sorts:
% 4.71/1.86  
% 4.71/1.86  
% 4.71/1.86  %Background operators:
% 4.71/1.86  
% 4.71/1.86  
% 4.71/1.86  %Foreground operators:
% 4.71/1.86  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.71/1.86  tff(v3_borsuk_1, type, v3_borsuk_1: ($i * $i * $i) > $o).
% 4.71/1.86  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.71/1.86  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.71/1.86  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.71/1.86  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.71/1.86  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 4.71/1.86  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.71/1.86  tff(v4_tex_2, type, v4_tex_2: ($i * $i) > $o).
% 4.71/1.86  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.71/1.86  tff('#skF_7', type, '#skF_7': $i).
% 4.71/1.86  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.71/1.86  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 4.71/1.86  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.71/1.86  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.71/1.86  tff('#skF_5', type, '#skF_5': $i).
% 4.71/1.86  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 4.71/1.86  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.71/1.86  tff('#skF_6', type, '#skF_6': $i).
% 4.71/1.86  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.71/1.86  tff(v3_tdlat_3, type, v3_tdlat_3: $i > $o).
% 4.71/1.86  tff('#skF_8', type, '#skF_8': $i).
% 4.71/1.86  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.71/1.86  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 4.71/1.86  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.71/1.86  tff('#skF_4', type, '#skF_4': $i).
% 4.71/1.86  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.71/1.86  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.71/1.86  tff(v5_pre_topc, type, v5_pre_topc: ($i * $i * $i) > $o).
% 4.71/1.86  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 4.71/1.86  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.71/1.86  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.71/1.86  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.71/1.86  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 4.71/1.86  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.71/1.86  
% 4.71/1.88  tff(f_188, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v4_tex_2(B, A)) & m1_pre_topc(B, A)) => (![C]: ((((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & v5_pre_topc(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (v3_borsuk_1(C, A, B) => (![D]: (m1_subset_1(D, u1_struct_0(B)) => (![E]: (m1_subset_1(E, u1_struct_0(A)) => ((D = E) => (k8_relset_1(u1_struct_0(A), u1_struct_0(B), C, k6_domain_1(u1_struct_0(B), D)) = k2_pre_topc(A, k6_domain_1(u1_struct_0(A), E))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_tex_2)).
% 4.71/1.88  tff(f_48, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 4.71/1.88  tff(f_72, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 4.71/1.88  tff(f_79, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 4.71/1.88  tff(f_44, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 4.71/1.88  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 4.71/1.88  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 4.71/1.88  tff(f_96, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (v4_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => v3_tex_2(C, A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_tex_2)).
% 4.71/1.88  tff(f_58, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B))) => m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_pre_topc)).
% 4.71/1.88  tff(f_111, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ~v3_tex_2(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_tex_2)).
% 4.71/1.88  tff(f_65, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 4.71/1.88  tff(f_149, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v4_tex_2(B, A)) & m1_pre_topc(B, A)) => (![C]: ((((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & v5_pre_topc(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (v3_borsuk_1(C, A, B) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => (![E]: (m1_subset_1(E, k1_zfmisc_1(u1_struct_0(A))) => ((D = E) => (k8_relset_1(u1_struct_0(A), u1_struct_0(B), C, D) = k2_pre_topc(A, E)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t76_tex_2)).
% 4.71/1.88  tff(c_62, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_188])).
% 4.71/1.88  tff(c_50, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'))))), inference(cnfTransformation, [status(thm)], [f_188])).
% 4.71/1.88  tff(c_1188, plain, (![A_266, B_267, C_268, D_269]: (k8_relset_1(A_266, B_267, C_268, D_269)=k10_relat_1(C_268, D_269) | ~m1_subset_1(C_268, k1_zfmisc_1(k2_zfmisc_1(A_266, B_267))))), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.71/1.88  tff(c_1198, plain, (![D_269]: (k8_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6', D_269)=k10_relat_1('#skF_6', D_269))), inference(resolution, [status(thm)], [c_50, c_1188])).
% 4.71/1.88  tff(c_58, plain, (m1_pre_topc('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_188])).
% 4.71/1.88  tff(c_64, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_188])).
% 4.71/1.88  tff(c_44, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_188])).
% 4.71/1.88  tff(c_144, plain, (![A_123, B_124]: (k6_domain_1(A_123, B_124)=k1_tarski(B_124) | ~m1_subset_1(B_124, A_123) | v1_xboole_0(A_123))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.71/1.88  tff(c_160, plain, (k6_domain_1(u1_struct_0('#skF_4'), '#skF_8')=k1_tarski('#skF_8') | v1_xboole_0(u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_44, c_144])).
% 4.71/1.88  tff(c_1002, plain, (v1_xboole_0(u1_struct_0('#skF_4'))), inference(splitLeft, [status(thm)], [c_160])).
% 4.71/1.88  tff(c_1041, plain, (![B_245, A_246]: (m1_subset_1(u1_struct_0(B_245), k1_zfmisc_1(u1_struct_0(A_246))) | ~m1_pre_topc(B_245, A_246) | ~l1_pre_topc(A_246))), inference(cnfTransformation, [status(thm)], [f_79])).
% 4.71/1.88  tff(c_14, plain, (![A_11, B_12]: (r1_tarski(A_11, B_12) | ~m1_subset_1(A_11, k1_zfmisc_1(B_12)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.71/1.88  tff(c_1050, plain, (![B_247, A_248]: (r1_tarski(u1_struct_0(B_247), u1_struct_0(A_248)) | ~m1_pre_topc(B_247, A_248) | ~l1_pre_topc(A_248))), inference(resolution, [status(thm)], [c_1041, c_14])).
% 4.71/1.88  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.71/1.88  tff(c_115, plain, (![C_116, B_117, A_118]: (r2_hidden(C_116, B_117) | ~r2_hidden(C_116, A_118) | ~r1_tarski(A_118, B_117))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.71/1.88  tff(c_122, plain, (![A_119, B_120]: (r2_hidden('#skF_1'(A_119), B_120) | ~r1_tarski(A_119, B_120) | v1_xboole_0(A_119))), inference(resolution, [status(thm)], [c_4, c_115])).
% 4.71/1.88  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.71/1.88  tff(c_129, plain, (![B_120, A_119]: (~v1_xboole_0(B_120) | ~r1_tarski(A_119, B_120) | v1_xboole_0(A_119))), inference(resolution, [status(thm)], [c_122, c_2])).
% 4.71/1.88  tff(c_1088, plain, (![A_255, B_256]: (~v1_xboole_0(u1_struct_0(A_255)) | v1_xboole_0(u1_struct_0(B_256)) | ~m1_pre_topc(B_256, A_255) | ~l1_pre_topc(A_255))), inference(resolution, [status(thm)], [c_1050, c_129])).
% 4.71/1.88  tff(c_1090, plain, (![B_256]: (v1_xboole_0(u1_struct_0(B_256)) | ~m1_pre_topc(B_256, '#skF_4') | ~l1_pre_topc('#skF_4'))), inference(resolution, [status(thm)], [c_1002, c_1088])).
% 4.71/1.88  tff(c_1094, plain, (![B_257]: (v1_xboole_0(u1_struct_0(B_257)) | ~m1_pre_topc(B_257, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_1090])).
% 4.71/1.88  tff(c_70, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_188])).
% 4.71/1.88  tff(c_60, plain, (v4_tex_2('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_188])).
% 4.71/1.88  tff(c_26, plain, (![B_30, A_28]: (m1_subset_1(u1_struct_0(B_30), k1_zfmisc_1(u1_struct_0(A_28))) | ~m1_pre_topc(B_30, A_28) | ~l1_pre_topc(A_28))), inference(cnfTransformation, [status(thm)], [f_79])).
% 4.71/1.88  tff(c_947, plain, (![B_237, A_238]: (v3_tex_2(u1_struct_0(B_237), A_238) | ~m1_subset_1(u1_struct_0(B_237), k1_zfmisc_1(u1_struct_0(A_238))) | ~v4_tex_2(B_237, A_238) | ~m1_pre_topc(B_237, A_238) | ~l1_pre_topc(A_238) | v2_struct_0(A_238))), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.71/1.88  tff(c_969, plain, (![B_239, A_240]: (v3_tex_2(u1_struct_0(B_239), A_240) | ~v4_tex_2(B_239, A_240) | v2_struct_0(A_240) | ~m1_pre_topc(B_239, A_240) | ~l1_pre_topc(A_240))), inference(resolution, [status(thm)], [c_26, c_947])).
% 4.71/1.88  tff(c_42, plain, ('#skF_7'='#skF_8'), inference(cnfTransformation, [status(thm)], [f_188])).
% 4.71/1.88  tff(c_46, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_188])).
% 4.71/1.88  tff(c_71, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_46])).
% 4.71/1.88  tff(c_159, plain, (k6_domain_1(u1_struct_0('#skF_5'), '#skF_8')=k1_tarski('#skF_8') | v1_xboole_0(u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_71, c_144])).
% 4.71/1.88  tff(c_161, plain, (v1_xboole_0(u1_struct_0('#skF_5'))), inference(splitLeft, [status(thm)], [c_159])).
% 4.71/1.88  tff(c_10, plain, (![A_5, B_6]: (r2_hidden('#skF_2'(A_5, B_6), A_5) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.71/1.88  tff(c_108, plain, (![A_113, B_114]: (~r2_hidden('#skF_2'(A_113, B_114), B_114) | r1_tarski(A_113, B_114))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.71/1.88  tff(c_113, plain, (![A_5]: (r1_tarski(A_5, A_5))), inference(resolution, [status(thm)], [c_10, c_108])).
% 4.71/1.88  tff(c_68, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_188])).
% 4.71/1.88  tff(c_16, plain, (![A_11, B_12]: (m1_subset_1(A_11, k1_zfmisc_1(B_12)) | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.71/1.88  tff(c_388, plain, (![C_179, A_180, B_181]: (m1_subset_1(C_179, k1_zfmisc_1(u1_struct_0(A_180))) | ~m1_subset_1(C_179, k1_zfmisc_1(u1_struct_0(B_181))) | ~m1_pre_topc(B_181, A_180) | ~l1_pre_topc(A_180))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.71/1.88  tff(c_467, plain, (![A_194, A_195, B_196]: (m1_subset_1(A_194, k1_zfmisc_1(u1_struct_0(A_195))) | ~m1_pre_topc(B_196, A_195) | ~l1_pre_topc(A_195) | ~r1_tarski(A_194, u1_struct_0(B_196)))), inference(resolution, [status(thm)], [c_16, c_388])).
% 4.71/1.88  tff(c_469, plain, (![A_194]: (m1_subset_1(A_194, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4') | ~r1_tarski(A_194, u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_58, c_467])).
% 4.71/1.88  tff(c_472, plain, (![A_194]: (m1_subset_1(A_194, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r1_tarski(A_194, u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_469])).
% 4.71/1.88  tff(c_671, plain, (![B_214, A_215]: (~v3_tex_2(B_214, A_215) | ~m1_subset_1(B_214, k1_zfmisc_1(u1_struct_0(A_215))) | ~v1_xboole_0(B_214) | ~l1_pre_topc(A_215) | ~v2_pre_topc(A_215) | v2_struct_0(A_215))), inference(cnfTransformation, [status(thm)], [f_111])).
% 4.71/1.88  tff(c_674, plain, (![A_194]: (~v3_tex_2(A_194, '#skF_4') | ~v1_xboole_0(A_194) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~r1_tarski(A_194, u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_472, c_671])).
% 4.71/1.88  tff(c_688, plain, (![A_194]: (~v3_tex_2(A_194, '#skF_4') | ~v1_xboole_0(A_194) | v2_struct_0('#skF_4') | ~r1_tarski(A_194, u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_64, c_674])).
% 4.71/1.88  tff(c_721, plain, (![A_218]: (~v3_tex_2(A_218, '#skF_4') | ~v1_xboole_0(A_218) | ~r1_tarski(A_218, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_70, c_688])).
% 4.71/1.88  tff(c_741, plain, (~v3_tex_2(u1_struct_0('#skF_5'), '#skF_4') | ~v1_xboole_0(u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_113, c_721])).
% 4.71/1.88  tff(c_755, plain, (~v3_tex_2(u1_struct_0('#skF_5'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_161, c_741])).
% 4.71/1.88  tff(c_983, plain, (~v4_tex_2('#skF_5', '#skF_4') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_969, c_755])).
% 4.71/1.88  tff(c_992, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_58, c_60, c_983])).
% 4.71/1.88  tff(c_994, plain, $false, inference(negUnitSimplification, [status(thm)], [c_70, c_992])).
% 4.71/1.88  tff(c_996, plain, (~v1_xboole_0(u1_struct_0('#skF_5'))), inference(splitRight, [status(thm)], [c_159])).
% 4.71/1.88  tff(c_1099, plain, (~m1_pre_topc('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_1094, c_996])).
% 4.71/1.88  tff(c_1104, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_1099])).
% 4.71/1.88  tff(c_1105, plain, (k6_domain_1(u1_struct_0('#skF_4'), '#skF_8')=k1_tarski('#skF_8')), inference(splitRight, [status(thm)], [c_160])).
% 4.71/1.88  tff(c_995, plain, (k6_domain_1(u1_struct_0('#skF_5'), '#skF_8')=k1_tarski('#skF_8')), inference(splitRight, [status(thm)], [c_159])).
% 4.71/1.88  tff(c_40, plain, (k8_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6', k6_domain_1(u1_struct_0('#skF_5'), '#skF_7'))!=k2_pre_topc('#skF_4', k6_domain_1(u1_struct_0('#skF_4'), '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_188])).
% 4.71/1.88  tff(c_72, plain, (k8_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6', k6_domain_1(u1_struct_0('#skF_5'), '#skF_8'))!=k2_pre_topc('#skF_4', k6_domain_1(u1_struct_0('#skF_4'), '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40])).
% 4.71/1.88  tff(c_997, plain, (k8_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6', k1_tarski('#skF_8'))!=k2_pre_topc('#skF_4', k6_domain_1(u1_struct_0('#skF_4'), '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_995, c_72])).
% 4.71/1.88  tff(c_1244, plain, (k2_pre_topc('#skF_4', k1_tarski('#skF_8'))!=k10_relat_1('#skF_6', k1_tarski('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_1198, c_1105, c_997])).
% 4.71/1.88  tff(c_56, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_188])).
% 4.71/1.88  tff(c_54, plain, (v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_188])).
% 4.71/1.88  tff(c_52, plain, (v5_pre_topc('#skF_6', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_188])).
% 4.71/1.88  tff(c_48, plain, (v3_borsuk_1('#skF_6', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_188])).
% 4.71/1.88  tff(c_1111, plain, (![A_258, B_259]: (m1_subset_1(k6_domain_1(A_258, B_259), k1_zfmisc_1(A_258)) | ~m1_subset_1(B_259, A_258) | v1_xboole_0(A_258))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.71/1.88  tff(c_1123, plain, (m1_subset_1(k1_tarski('#skF_8'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | v1_xboole_0(u1_struct_0('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_995, c_1111])).
% 4.71/1.88  tff(c_1130, plain, (m1_subset_1(k1_tarski('#skF_8'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | v1_xboole_0(u1_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_71, c_1123])).
% 4.71/1.88  tff(c_1131, plain, (m1_subset_1(k1_tarski('#skF_8'), k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_996, c_1130])).
% 4.71/1.88  tff(c_66, plain, (v3_tdlat_3('#skF_4')), inference(cnfTransformation, [status(thm)], [f_188])).
% 4.71/1.88  tff(c_1106, plain, (~v1_xboole_0(u1_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_160])).
% 4.71/1.88  tff(c_1120, plain, (m1_subset_1(k1_tarski('#skF_8'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_4')) | v1_xboole_0(u1_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1105, c_1111])).
% 4.71/1.88  tff(c_1127, plain, (m1_subset_1(k1_tarski('#skF_8'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | v1_xboole_0(u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_1120])).
% 4.71/1.88  tff(c_1128, plain, (m1_subset_1(k1_tarski('#skF_8'), k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_1106, c_1127])).
% 4.71/1.88  tff(c_2021, plain, (![A_368, B_369, C_370, E_371]: (k8_relset_1(u1_struct_0(A_368), u1_struct_0(B_369), C_370, E_371)=k2_pre_topc(A_368, E_371) | ~m1_subset_1(E_371, k1_zfmisc_1(u1_struct_0(A_368))) | ~m1_subset_1(E_371, k1_zfmisc_1(u1_struct_0(B_369))) | ~v3_borsuk_1(C_370, A_368, B_369) | ~m1_subset_1(C_370, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_368), u1_struct_0(B_369)))) | ~v5_pre_topc(C_370, A_368, B_369) | ~v1_funct_2(C_370, u1_struct_0(A_368), u1_struct_0(B_369)) | ~v1_funct_1(C_370) | ~m1_pre_topc(B_369, A_368) | ~v4_tex_2(B_369, A_368) | v2_struct_0(B_369) | ~l1_pre_topc(A_368) | ~v3_tdlat_3(A_368) | ~v2_pre_topc(A_368) | v2_struct_0(A_368))), inference(cnfTransformation, [status(thm)], [f_149])).
% 4.71/1.88  tff(c_2037, plain, (![B_369, C_370]: (k8_relset_1(u1_struct_0('#skF_4'), u1_struct_0(B_369), C_370, k1_tarski('#skF_8'))=k2_pre_topc('#skF_4', k1_tarski('#skF_8')) | ~m1_subset_1(k1_tarski('#skF_8'), k1_zfmisc_1(u1_struct_0(B_369))) | ~v3_borsuk_1(C_370, '#skF_4', B_369) | ~m1_subset_1(C_370, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_369)))) | ~v5_pre_topc(C_370, '#skF_4', B_369) | ~v1_funct_2(C_370, u1_struct_0('#skF_4'), u1_struct_0(B_369)) | ~v1_funct_1(C_370) | ~m1_pre_topc(B_369, '#skF_4') | ~v4_tex_2(B_369, '#skF_4') | v2_struct_0(B_369) | ~l1_pre_topc('#skF_4') | ~v3_tdlat_3('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_1128, c_2021])).
% 4.71/1.88  tff(c_2057, plain, (![B_369, C_370]: (k8_relset_1(u1_struct_0('#skF_4'), u1_struct_0(B_369), C_370, k1_tarski('#skF_8'))=k2_pre_topc('#skF_4', k1_tarski('#skF_8')) | ~m1_subset_1(k1_tarski('#skF_8'), k1_zfmisc_1(u1_struct_0(B_369))) | ~v3_borsuk_1(C_370, '#skF_4', B_369) | ~m1_subset_1(C_370, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_369)))) | ~v5_pre_topc(C_370, '#skF_4', B_369) | ~v1_funct_2(C_370, u1_struct_0('#skF_4'), u1_struct_0(B_369)) | ~v1_funct_1(C_370) | ~m1_pre_topc(B_369, '#skF_4') | ~v4_tex_2(B_369, '#skF_4') | v2_struct_0(B_369) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_64, c_2037])).
% 4.71/1.88  tff(c_2106, plain, (![B_375, C_376]: (k8_relset_1(u1_struct_0('#skF_4'), u1_struct_0(B_375), C_376, k1_tarski('#skF_8'))=k2_pre_topc('#skF_4', k1_tarski('#skF_8')) | ~m1_subset_1(k1_tarski('#skF_8'), k1_zfmisc_1(u1_struct_0(B_375))) | ~v3_borsuk_1(C_376, '#skF_4', B_375) | ~m1_subset_1(C_376, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_375)))) | ~v5_pre_topc(C_376, '#skF_4', B_375) | ~v1_funct_2(C_376, u1_struct_0('#skF_4'), u1_struct_0(B_375)) | ~v1_funct_1(C_376) | ~m1_pre_topc(B_375, '#skF_4') | ~v4_tex_2(B_375, '#skF_4') | v2_struct_0(B_375))), inference(negUnitSimplification, [status(thm)], [c_70, c_2057])).
% 4.71/1.88  tff(c_2113, plain, (k8_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6', k1_tarski('#skF_8'))=k2_pre_topc('#skF_4', k1_tarski('#skF_8')) | ~m1_subset_1(k1_tarski('#skF_8'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~v3_borsuk_1('#skF_6', '#skF_4', '#skF_5') | ~v5_pre_topc('#skF_6', '#skF_4', '#skF_5') | ~v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_5')) | ~v1_funct_1('#skF_6') | ~m1_pre_topc('#skF_5', '#skF_4') | ~v4_tex_2('#skF_5', '#skF_4') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_50, c_2106])).
% 4.71/1.88  tff(c_2121, plain, (k2_pre_topc('#skF_4', k1_tarski('#skF_8'))=k10_relat_1('#skF_6', k1_tarski('#skF_8')) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_56, c_54, c_52, c_48, c_1131, c_1198, c_2113])).
% 4.71/1.88  tff(c_2123, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_1244, c_2121])).
% 4.71/1.88  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.71/1.88  
% 4.71/1.88  Inference rules
% 4.71/1.88  ----------------------
% 4.71/1.88  #Ref     : 0
% 4.71/1.88  #Sup     : 456
% 4.71/1.88  #Fact    : 0
% 4.71/1.88  #Define  : 0
% 4.71/1.88  #Split   : 18
% 4.71/1.88  #Chain   : 0
% 4.71/1.88  #Close   : 0
% 4.71/1.88  
% 4.71/1.88  Ordering : KBO
% 4.71/1.88  
% 4.71/1.88  Simplification rules
% 4.71/1.88  ----------------------
% 4.71/1.88  #Subsume      : 135
% 4.71/1.88  #Demod        : 94
% 4.71/1.88  #Tautology    : 103
% 4.71/1.88  #SimpNegUnit  : 42
% 4.71/1.88  #BackRed      : 18
% 4.71/1.88  
% 4.71/1.88  #Partial instantiations: 0
% 4.71/1.88  #Strategies tried      : 1
% 4.71/1.88  
% 4.71/1.88  Timing (in seconds)
% 4.71/1.88  ----------------------
% 4.71/1.89  Preprocessing        : 0.40
% 4.71/1.89  Parsing              : 0.21
% 4.71/1.89  CNF conversion       : 0.03
% 4.71/1.89  Main loop            : 0.66
% 4.71/1.89  Inferencing          : 0.24
% 4.71/1.89  Reduction            : 0.20
% 4.71/1.89  Demodulation         : 0.13
% 4.71/1.89  BG Simplification    : 0.03
% 4.71/1.89  Subsumption          : 0.14
% 4.71/1.89  Abstraction          : 0.03
% 4.71/1.89  MUC search           : 0.00
% 4.71/1.89  Cooper               : 0.00
% 4.71/1.89  Total                : 1.11
% 4.71/1.89  Index Insertion      : 0.00
% 4.71/1.89  Index Deletion       : 0.00
% 4.71/1.89  Index Matching       : 0.00
% 4.71/1.89  BG Taut test         : 0.00
%------------------------------------------------------------------------------
