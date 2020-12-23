%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:42 EST 2020

% Result     : Theorem 3.27s
% Output     : CNFRefutation 3.44s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 237 expanded)
%              Number of leaves         :   40 ( 102 expanded)
%              Depth                    :   12
%              Number of atoms          :  280 (1166 expanded)
%              Number of equality atoms :   22 ( 151 expanded)
%              Maximal formula depth    :   20 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_pre_topc > v3_borsuk_1 > v1_funct_2 > v4_tex_2 > v3_tex_2 > r2_hidden > m1_subset_1 > m1_pre_topc > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_pre_topc > k8_relset_1 > k6_domain_1 > k2_zfmisc_1 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(v4_tex_2,type,(
    v4_tex_2: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

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

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v3_tdlat_3,type,(
    v3_tdlat_3: $i > $o )).

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

tff(f_170,negated_conjecture,(
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

tff(f_54,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_61,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_78,axiom,(
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

tff(f_93,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( v1_xboole_0(B)
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
         => ~ v3_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_tex_2)).

tff(f_33,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_47,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_131,axiom,(
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

tff(c_48,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_56,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_50,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_44,plain,(
    m1_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_54,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_46,plain,(
    v4_tex_2('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_28,plain,(
    '#skF_5' = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_32,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_57,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_32])).

tff(c_78,plain,(
    ! [A_90,B_91] :
      ( k6_domain_1(A_90,B_91) = k1_tarski(B_91)
      | ~ m1_subset_1(B_91,A_90)
      | v1_xboole_0(A_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_90,plain,
    ( k6_domain_1(u1_struct_0('#skF_3'),'#skF_6') = k1_tarski('#skF_6')
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_57,c_78])).

tff(c_316,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_90])).

tff(c_12,plain,(
    ! [B_13,A_11] :
      ( m1_subset_1(u1_struct_0(B_13),k1_zfmisc_1(u1_struct_0(A_11)))
      | ~ m1_pre_topc(B_13,A_11)
      | ~ l1_pre_topc(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_430,plain,(
    ! [B_168,A_169] :
      ( v3_tex_2(u1_struct_0(B_168),A_169)
      | ~ m1_subset_1(u1_struct_0(B_168),k1_zfmisc_1(u1_struct_0(A_169)))
      | ~ v4_tex_2(B_168,A_169)
      | ~ m1_pre_topc(B_168,A_169)
      | ~ l1_pre_topc(A_169)
      | v2_struct_0(A_169) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_452,plain,(
    ! [B_174,A_175] :
      ( v3_tex_2(u1_struct_0(B_174),A_175)
      | ~ v4_tex_2(B_174,A_175)
      | v2_struct_0(A_175)
      | ~ m1_pre_topc(B_174,A_175)
      | ~ l1_pre_topc(A_175) ) ),
    inference(resolution,[status(thm)],[c_12,c_430])).

tff(c_354,plain,(
    ! [B_155,A_156] :
      ( ~ v3_tex_2(B_155,A_156)
      | ~ m1_subset_1(B_155,k1_zfmisc_1(u1_struct_0(A_156)))
      | ~ v1_xboole_0(B_155)
      | ~ l1_pre_topc(A_156)
      | ~ v2_pre_topc(A_156)
      | v2_struct_0(A_156) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_370,plain,(
    ! [B_13,A_11] :
      ( ~ v3_tex_2(u1_struct_0(B_13),A_11)
      | ~ v1_xboole_0(u1_struct_0(B_13))
      | ~ v2_pre_topc(A_11)
      | v2_struct_0(A_11)
      | ~ m1_pre_topc(B_13,A_11)
      | ~ l1_pre_topc(A_11) ) ),
    inference(resolution,[status(thm)],[c_12,c_354])).

tff(c_457,plain,(
    ! [B_176,A_177] :
      ( ~ v1_xboole_0(u1_struct_0(B_176))
      | ~ v2_pre_topc(A_177)
      | ~ v4_tex_2(B_176,A_177)
      | v2_struct_0(A_177)
      | ~ m1_pre_topc(B_176,A_177)
      | ~ l1_pre_topc(A_177) ) ),
    inference(resolution,[status(thm)],[c_452,c_370])).

tff(c_461,plain,(
    ! [A_178] :
      ( ~ v2_pre_topc(A_178)
      | ~ v4_tex_2('#skF_3',A_178)
      | v2_struct_0(A_178)
      | ~ m1_pre_topc('#skF_3',A_178)
      | ~ l1_pre_topc(A_178) ) ),
    inference(resolution,[status(thm)],[c_316,c_457])).

tff(c_468,plain,
    ( ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_46,c_461])).

tff(c_472,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_44,c_54,c_468])).

tff(c_474,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_472])).

tff(c_475,plain,(
    k6_domain_1(u1_struct_0('#skF_3'),'#skF_6') = k1_tarski('#skF_6') ),
    inference(splitRight,[status(thm)],[c_90])).

tff(c_92,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_90])).

tff(c_202,plain,(
    ! [B_120,A_121] :
      ( v3_tex_2(u1_struct_0(B_120),A_121)
      | ~ m1_subset_1(u1_struct_0(B_120),k1_zfmisc_1(u1_struct_0(A_121)))
      | ~ v4_tex_2(B_120,A_121)
      | ~ m1_pre_topc(B_120,A_121)
      | ~ l1_pre_topc(A_121)
      | v2_struct_0(A_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_207,plain,(
    ! [B_122,A_123] :
      ( v3_tex_2(u1_struct_0(B_122),A_123)
      | ~ v4_tex_2(B_122,A_123)
      | v2_struct_0(A_123)
      | ~ m1_pre_topc(B_122,A_123)
      | ~ l1_pre_topc(A_123) ) ),
    inference(resolution,[status(thm)],[c_12,c_202])).

tff(c_140,plain,(
    ! [B_107,A_108] :
      ( ~ v3_tex_2(B_107,A_108)
      | ~ m1_subset_1(B_107,k1_zfmisc_1(u1_struct_0(A_108)))
      | ~ v1_xboole_0(B_107)
      | ~ l1_pre_topc(A_108)
      | ~ v2_pre_topc(A_108)
      | v2_struct_0(A_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_149,plain,(
    ! [B_13,A_11] :
      ( ~ v3_tex_2(u1_struct_0(B_13),A_11)
      | ~ v1_xboole_0(u1_struct_0(B_13))
      | ~ v2_pre_topc(A_11)
      | v2_struct_0(A_11)
      | ~ m1_pre_topc(B_13,A_11)
      | ~ l1_pre_topc(A_11) ) ),
    inference(resolution,[status(thm)],[c_12,c_140])).

tff(c_223,plain,(
    ! [B_128,A_129] :
      ( ~ v1_xboole_0(u1_struct_0(B_128))
      | ~ v2_pre_topc(A_129)
      | ~ v4_tex_2(B_128,A_129)
      | v2_struct_0(A_129)
      | ~ m1_pre_topc(B_128,A_129)
      | ~ l1_pre_topc(A_129) ) ),
    inference(resolution,[status(thm)],[c_207,c_149])).

tff(c_230,plain,(
    ! [A_130] :
      ( ~ v2_pre_topc(A_130)
      | ~ v4_tex_2('#skF_3',A_130)
      | v2_struct_0(A_130)
      | ~ m1_pre_topc('#skF_3',A_130)
      | ~ l1_pre_topc(A_130) ) ),
    inference(resolution,[status(thm)],[c_92,c_223])).

tff(c_237,plain,
    ( ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_46,c_230])).

tff(c_241,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_44,c_54,c_237])).

tff(c_243,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_241])).

tff(c_245,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_90])).

tff(c_4,plain,(
    ! [A_2,B_3] :
      ( r2_hidden(A_2,B_3)
      | v1_xboole_0(B_3)
      | ~ m1_subset_1(A_2,B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_30,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_89,plain,
    ( k6_domain_1(u1_struct_0('#skF_2'),'#skF_6') = k1_tarski('#skF_6')
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_30,c_78])).

tff(c_91,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_89])).

tff(c_273,plain,(
    ! [B_133,A_134] :
      ( m1_subset_1(u1_struct_0(B_133),k1_zfmisc_1(u1_struct_0(A_134)))
      | ~ m1_pre_topc(B_133,A_134)
      | ~ l1_pre_topc(A_134) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_6,plain,(
    ! [C_6,B_5,A_4] :
      ( ~ v1_xboole_0(C_6)
      | ~ m1_subset_1(B_5,k1_zfmisc_1(C_6))
      | ~ r2_hidden(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_282,plain,(
    ! [A_137,A_138,B_139] :
      ( ~ v1_xboole_0(u1_struct_0(A_137))
      | ~ r2_hidden(A_138,u1_struct_0(B_139))
      | ~ m1_pre_topc(B_139,A_137)
      | ~ l1_pre_topc(A_137) ) ),
    inference(resolution,[status(thm)],[c_273,c_6])).

tff(c_284,plain,(
    ! [A_138,B_139] :
      ( ~ r2_hidden(A_138,u1_struct_0(B_139))
      | ~ m1_pre_topc(B_139,'#skF_2')
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_91,c_282])).

tff(c_288,plain,(
    ! [A_140,B_141] :
      ( ~ r2_hidden(A_140,u1_struct_0(B_141))
      | ~ m1_pre_topc(B_141,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_284])).

tff(c_294,plain,(
    ! [B_142,A_143] :
      ( ~ m1_pre_topc(B_142,'#skF_2')
      | v1_xboole_0(u1_struct_0(B_142))
      | ~ m1_subset_1(A_143,u1_struct_0(B_142)) ) ),
    inference(resolution,[status(thm)],[c_4,c_288])).

tff(c_300,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_2')
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_57,c_294])).

tff(c_305,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_300])).

tff(c_307,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_245,c_305])).

tff(c_308,plain,(
    k6_domain_1(u1_struct_0('#skF_2'),'#skF_6') = k1_tarski('#skF_6') ),
    inference(splitRight,[status(thm)],[c_89])).

tff(c_26,plain,(
    k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4',k6_domain_1(u1_struct_0('#skF_3'),'#skF_5')) != k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_58,plain,(
    k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4',k6_domain_1(u1_struct_0('#skF_3'),'#skF_6')) != k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26])).

tff(c_311,plain,(
    k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4',k6_domain_1(u1_struct_0('#skF_3'),'#skF_6')) != k2_pre_topc('#skF_2',k1_tarski('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_308,c_58])).

tff(c_477,plain,(
    k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4',k1_tarski('#skF_6')) != k2_pre_topc('#skF_2',k1_tarski('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_475,c_311])).

tff(c_42,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_40,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_38,plain,(
    v5_pre_topc('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_34,plain,(
    v3_borsuk_1('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_476,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_90])).

tff(c_482,plain,(
    ! [A_179,B_180] :
      ( m1_subset_1(k6_domain_1(A_179,B_180),k1_zfmisc_1(A_179))
      | ~ m1_subset_1(B_180,A_179)
      | v1_xboole_0(A_179) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_490,plain,
    ( m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3'))
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_475,c_482])).

tff(c_497,plain,
    ( m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_490])).

tff(c_498,plain,(
    m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_476,c_497])).

tff(c_36,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_52,plain,(
    v3_tdlat_3('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_309,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_89])).

tff(c_493,plain,
    ( m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_2'))
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_308,c_482])).

tff(c_500,plain,
    ( m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_493])).

tff(c_501,plain,(
    m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_309,c_500])).

tff(c_622,plain,(
    ! [A_206,B_207,C_208,E_209] :
      ( k8_relset_1(u1_struct_0(A_206),u1_struct_0(B_207),C_208,E_209) = k2_pre_topc(A_206,E_209)
      | ~ m1_subset_1(E_209,k1_zfmisc_1(u1_struct_0(A_206)))
      | ~ m1_subset_1(E_209,k1_zfmisc_1(u1_struct_0(B_207)))
      | ~ v3_borsuk_1(C_208,A_206,B_207)
      | ~ m1_subset_1(C_208,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_206),u1_struct_0(B_207))))
      | ~ v5_pre_topc(C_208,A_206,B_207)
      | ~ v1_funct_2(C_208,u1_struct_0(A_206),u1_struct_0(B_207))
      | ~ v1_funct_1(C_208)
      | ~ m1_pre_topc(B_207,A_206)
      | ~ v4_tex_2(B_207,A_206)
      | v2_struct_0(B_207)
      | ~ l1_pre_topc(A_206)
      | ~ v3_tdlat_3(A_206)
      | ~ v2_pre_topc(A_206)
      | v2_struct_0(A_206) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_628,plain,(
    ! [B_207,C_208] :
      ( k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0(B_207),C_208,k1_tarski('#skF_6')) = k2_pre_topc('#skF_2',k1_tarski('#skF_6'))
      | ~ m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0(B_207)))
      | ~ v3_borsuk_1(C_208,'#skF_2',B_207)
      | ~ m1_subset_1(C_208,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0(B_207))))
      | ~ v5_pre_topc(C_208,'#skF_2',B_207)
      | ~ v1_funct_2(C_208,u1_struct_0('#skF_2'),u1_struct_0(B_207))
      | ~ v1_funct_1(C_208)
      | ~ m1_pre_topc(B_207,'#skF_2')
      | ~ v4_tex_2(B_207,'#skF_2')
      | v2_struct_0(B_207)
      | ~ l1_pre_topc('#skF_2')
      | ~ v3_tdlat_3('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_501,c_622])).

tff(c_638,plain,(
    ! [B_207,C_208] :
      ( k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0(B_207),C_208,k1_tarski('#skF_6')) = k2_pre_topc('#skF_2',k1_tarski('#skF_6'))
      | ~ m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0(B_207)))
      | ~ v3_borsuk_1(C_208,'#skF_2',B_207)
      | ~ m1_subset_1(C_208,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0(B_207))))
      | ~ v5_pre_topc(C_208,'#skF_2',B_207)
      | ~ v1_funct_2(C_208,u1_struct_0('#skF_2'),u1_struct_0(B_207))
      | ~ v1_funct_1(C_208)
      | ~ m1_pre_topc(B_207,'#skF_2')
      | ~ v4_tex_2(B_207,'#skF_2')
      | v2_struct_0(B_207)
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_628])).

tff(c_664,plain,(
    ! [B_218,C_219] :
      ( k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0(B_218),C_219,k1_tarski('#skF_6')) = k2_pre_topc('#skF_2',k1_tarski('#skF_6'))
      | ~ m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0(B_218)))
      | ~ v3_borsuk_1(C_219,'#skF_2',B_218)
      | ~ m1_subset_1(C_219,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0(B_218))))
      | ~ v5_pre_topc(C_219,'#skF_2',B_218)
      | ~ v1_funct_2(C_219,u1_struct_0('#skF_2'),u1_struct_0(B_218))
      | ~ v1_funct_1(C_219)
      | ~ m1_pre_topc(B_218,'#skF_2')
      | ~ v4_tex_2(B_218,'#skF_2')
      | v2_struct_0(B_218) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_638])).

tff(c_671,plain,
    ( k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4',k1_tarski('#skF_6')) = k2_pre_topc('#skF_2',k1_tarski('#skF_6'))
    | ~ m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ v3_borsuk_1('#skF_4','#skF_2','#skF_3')
    | ~ v5_pre_topc('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ v4_tex_2('#skF_3','#skF_2')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_664])).

tff(c_675,plain,
    ( k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4',k1_tarski('#skF_6')) = k2_pre_topc('#skF_2',k1_tarski('#skF_6'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_40,c_38,c_34,c_498,c_671])).

tff(c_677,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_477,c_675])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 10:01:57 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.27/1.55  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.27/1.56  
% 3.27/1.56  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.27/1.56  %$ v5_pre_topc > v3_borsuk_1 > v1_funct_2 > v4_tex_2 > v3_tex_2 > r2_hidden > m1_subset_1 > m1_pre_topc > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_pre_topc > k8_relset_1 > k6_domain_1 > k2_zfmisc_1 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 3.27/1.56  
% 3.27/1.56  %Foreground sorts:
% 3.27/1.56  
% 3.27/1.56  
% 3.27/1.56  %Background operators:
% 3.27/1.56  
% 3.27/1.56  
% 3.27/1.56  %Foreground operators:
% 3.27/1.56  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.27/1.56  tff(v3_borsuk_1, type, v3_borsuk_1: ($i * $i * $i) > $o).
% 3.27/1.56  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.27/1.56  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.27/1.56  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.27/1.56  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.27/1.56  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 3.27/1.56  tff(v4_tex_2, type, v4_tex_2: ($i * $i) > $o).
% 3.27/1.56  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.27/1.56  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 3.27/1.56  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.27/1.56  tff('#skF_5', type, '#skF_5': $i).
% 3.27/1.56  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 3.27/1.56  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.27/1.56  tff('#skF_6', type, '#skF_6': $i).
% 3.27/1.56  tff('#skF_2', type, '#skF_2': $i).
% 3.27/1.56  tff('#skF_3', type, '#skF_3': $i).
% 3.27/1.56  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.27/1.56  tff(v3_tdlat_3, type, v3_tdlat_3: $i > $o).
% 3.27/1.56  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.27/1.56  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.27/1.56  tff('#skF_4', type, '#skF_4': $i).
% 3.27/1.56  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.27/1.56  tff(v5_pre_topc, type, v5_pre_topc: ($i * $i * $i) > $o).
% 3.27/1.56  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.27/1.56  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.27/1.56  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.27/1.56  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.27/1.56  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.27/1.56  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 3.27/1.56  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.27/1.56  
% 3.44/1.58  tff(f_170, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v4_tex_2(B, A)) & m1_pre_topc(B, A)) => (![C]: ((((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & v5_pre_topc(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (v3_borsuk_1(C, A, B) => (![D]: (m1_subset_1(D, u1_struct_0(B)) => (![E]: (m1_subset_1(E, u1_struct_0(A)) => ((D = E) => (k8_relset_1(u1_struct_0(A), u1_struct_0(B), C, k6_domain_1(u1_struct_0(B), D)) = k2_pre_topc(A, k6_domain_1(u1_struct_0(A), E))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_tex_2)).
% 3.44/1.58  tff(f_54, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 3.44/1.58  tff(f_61, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 3.44/1.58  tff(f_78, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (v4_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => v3_tex_2(C, A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_tex_2)).
% 3.44/1.58  tff(f_93, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ~v3_tex_2(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_tex_2)).
% 3.44/1.58  tff(f_33, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 3.44/1.58  tff(f_40, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 3.44/1.58  tff(f_47, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 3.44/1.58  tff(f_131, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v4_tex_2(B, A)) & m1_pre_topc(B, A)) => (![C]: ((((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & v5_pre_topc(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (v3_borsuk_1(C, A, B) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => (![E]: (m1_subset_1(E, k1_zfmisc_1(u1_struct_0(A))) => ((D = E) => (k8_relset_1(u1_struct_0(A), u1_struct_0(B), C, D) = k2_pre_topc(A, E)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t76_tex_2)).
% 3.44/1.58  tff(c_48, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_170])).
% 3.44/1.58  tff(c_56, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_170])).
% 3.44/1.58  tff(c_50, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_170])).
% 3.44/1.58  tff(c_44, plain, (m1_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_170])).
% 3.44/1.58  tff(c_54, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_170])).
% 3.44/1.58  tff(c_46, plain, (v4_tex_2('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_170])).
% 3.44/1.58  tff(c_28, plain, ('#skF_5'='#skF_6'), inference(cnfTransformation, [status(thm)], [f_170])).
% 3.44/1.58  tff(c_32, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_170])).
% 3.44/1.58  tff(c_57, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_32])).
% 3.44/1.58  tff(c_78, plain, (![A_90, B_91]: (k6_domain_1(A_90, B_91)=k1_tarski(B_91) | ~m1_subset_1(B_91, A_90) | v1_xboole_0(A_90))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.44/1.58  tff(c_90, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_6')=k1_tarski('#skF_6') | v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_57, c_78])).
% 3.44/1.58  tff(c_316, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_90])).
% 3.44/1.58  tff(c_12, plain, (![B_13, A_11]: (m1_subset_1(u1_struct_0(B_13), k1_zfmisc_1(u1_struct_0(A_11))) | ~m1_pre_topc(B_13, A_11) | ~l1_pre_topc(A_11))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.44/1.58  tff(c_430, plain, (![B_168, A_169]: (v3_tex_2(u1_struct_0(B_168), A_169) | ~m1_subset_1(u1_struct_0(B_168), k1_zfmisc_1(u1_struct_0(A_169))) | ~v4_tex_2(B_168, A_169) | ~m1_pre_topc(B_168, A_169) | ~l1_pre_topc(A_169) | v2_struct_0(A_169))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.44/1.58  tff(c_452, plain, (![B_174, A_175]: (v3_tex_2(u1_struct_0(B_174), A_175) | ~v4_tex_2(B_174, A_175) | v2_struct_0(A_175) | ~m1_pre_topc(B_174, A_175) | ~l1_pre_topc(A_175))), inference(resolution, [status(thm)], [c_12, c_430])).
% 3.44/1.58  tff(c_354, plain, (![B_155, A_156]: (~v3_tex_2(B_155, A_156) | ~m1_subset_1(B_155, k1_zfmisc_1(u1_struct_0(A_156))) | ~v1_xboole_0(B_155) | ~l1_pre_topc(A_156) | ~v2_pre_topc(A_156) | v2_struct_0(A_156))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.44/1.58  tff(c_370, plain, (![B_13, A_11]: (~v3_tex_2(u1_struct_0(B_13), A_11) | ~v1_xboole_0(u1_struct_0(B_13)) | ~v2_pre_topc(A_11) | v2_struct_0(A_11) | ~m1_pre_topc(B_13, A_11) | ~l1_pre_topc(A_11))), inference(resolution, [status(thm)], [c_12, c_354])).
% 3.44/1.58  tff(c_457, plain, (![B_176, A_177]: (~v1_xboole_0(u1_struct_0(B_176)) | ~v2_pre_topc(A_177) | ~v4_tex_2(B_176, A_177) | v2_struct_0(A_177) | ~m1_pre_topc(B_176, A_177) | ~l1_pre_topc(A_177))), inference(resolution, [status(thm)], [c_452, c_370])).
% 3.44/1.58  tff(c_461, plain, (![A_178]: (~v2_pre_topc(A_178) | ~v4_tex_2('#skF_3', A_178) | v2_struct_0(A_178) | ~m1_pre_topc('#skF_3', A_178) | ~l1_pre_topc(A_178))), inference(resolution, [status(thm)], [c_316, c_457])).
% 3.44/1.58  tff(c_468, plain, (~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_46, c_461])).
% 3.44/1.58  tff(c_472, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_44, c_54, c_468])).
% 3.44/1.58  tff(c_474, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_472])).
% 3.44/1.58  tff(c_475, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_6')=k1_tarski('#skF_6')), inference(splitRight, [status(thm)], [c_90])).
% 3.44/1.58  tff(c_92, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_90])).
% 3.44/1.58  tff(c_202, plain, (![B_120, A_121]: (v3_tex_2(u1_struct_0(B_120), A_121) | ~m1_subset_1(u1_struct_0(B_120), k1_zfmisc_1(u1_struct_0(A_121))) | ~v4_tex_2(B_120, A_121) | ~m1_pre_topc(B_120, A_121) | ~l1_pre_topc(A_121) | v2_struct_0(A_121))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.44/1.58  tff(c_207, plain, (![B_122, A_123]: (v3_tex_2(u1_struct_0(B_122), A_123) | ~v4_tex_2(B_122, A_123) | v2_struct_0(A_123) | ~m1_pre_topc(B_122, A_123) | ~l1_pre_topc(A_123))), inference(resolution, [status(thm)], [c_12, c_202])).
% 3.44/1.58  tff(c_140, plain, (![B_107, A_108]: (~v3_tex_2(B_107, A_108) | ~m1_subset_1(B_107, k1_zfmisc_1(u1_struct_0(A_108))) | ~v1_xboole_0(B_107) | ~l1_pre_topc(A_108) | ~v2_pre_topc(A_108) | v2_struct_0(A_108))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.44/1.58  tff(c_149, plain, (![B_13, A_11]: (~v3_tex_2(u1_struct_0(B_13), A_11) | ~v1_xboole_0(u1_struct_0(B_13)) | ~v2_pre_topc(A_11) | v2_struct_0(A_11) | ~m1_pre_topc(B_13, A_11) | ~l1_pre_topc(A_11))), inference(resolution, [status(thm)], [c_12, c_140])).
% 3.44/1.58  tff(c_223, plain, (![B_128, A_129]: (~v1_xboole_0(u1_struct_0(B_128)) | ~v2_pre_topc(A_129) | ~v4_tex_2(B_128, A_129) | v2_struct_0(A_129) | ~m1_pre_topc(B_128, A_129) | ~l1_pre_topc(A_129))), inference(resolution, [status(thm)], [c_207, c_149])).
% 3.44/1.58  tff(c_230, plain, (![A_130]: (~v2_pre_topc(A_130) | ~v4_tex_2('#skF_3', A_130) | v2_struct_0(A_130) | ~m1_pre_topc('#skF_3', A_130) | ~l1_pre_topc(A_130))), inference(resolution, [status(thm)], [c_92, c_223])).
% 3.44/1.58  tff(c_237, plain, (~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_46, c_230])).
% 3.44/1.58  tff(c_241, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_44, c_54, c_237])).
% 3.44/1.58  tff(c_243, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_241])).
% 3.44/1.58  tff(c_245, plain, (~v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_90])).
% 3.44/1.58  tff(c_4, plain, (![A_2, B_3]: (r2_hidden(A_2, B_3) | v1_xboole_0(B_3) | ~m1_subset_1(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.44/1.58  tff(c_30, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_170])).
% 3.44/1.58  tff(c_89, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_6')=k1_tarski('#skF_6') | v1_xboole_0(u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_30, c_78])).
% 3.44/1.58  tff(c_91, plain, (v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_89])).
% 3.44/1.58  tff(c_273, plain, (![B_133, A_134]: (m1_subset_1(u1_struct_0(B_133), k1_zfmisc_1(u1_struct_0(A_134))) | ~m1_pre_topc(B_133, A_134) | ~l1_pre_topc(A_134))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.44/1.58  tff(c_6, plain, (![C_6, B_5, A_4]: (~v1_xboole_0(C_6) | ~m1_subset_1(B_5, k1_zfmisc_1(C_6)) | ~r2_hidden(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.44/1.58  tff(c_282, plain, (![A_137, A_138, B_139]: (~v1_xboole_0(u1_struct_0(A_137)) | ~r2_hidden(A_138, u1_struct_0(B_139)) | ~m1_pre_topc(B_139, A_137) | ~l1_pre_topc(A_137))), inference(resolution, [status(thm)], [c_273, c_6])).
% 3.44/1.58  tff(c_284, plain, (![A_138, B_139]: (~r2_hidden(A_138, u1_struct_0(B_139)) | ~m1_pre_topc(B_139, '#skF_2') | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_91, c_282])).
% 3.44/1.58  tff(c_288, plain, (![A_140, B_141]: (~r2_hidden(A_140, u1_struct_0(B_141)) | ~m1_pre_topc(B_141, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_284])).
% 3.44/1.58  tff(c_294, plain, (![B_142, A_143]: (~m1_pre_topc(B_142, '#skF_2') | v1_xboole_0(u1_struct_0(B_142)) | ~m1_subset_1(A_143, u1_struct_0(B_142)))), inference(resolution, [status(thm)], [c_4, c_288])).
% 3.44/1.58  tff(c_300, plain, (~m1_pre_topc('#skF_3', '#skF_2') | v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_57, c_294])).
% 3.44/1.58  tff(c_305, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_300])).
% 3.44/1.58  tff(c_307, plain, $false, inference(negUnitSimplification, [status(thm)], [c_245, c_305])).
% 3.44/1.58  tff(c_308, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_6')=k1_tarski('#skF_6')), inference(splitRight, [status(thm)], [c_89])).
% 3.44/1.58  tff(c_26, plain, (k8_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4', k6_domain_1(u1_struct_0('#skF_3'), '#skF_5'))!=k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_170])).
% 3.44/1.58  tff(c_58, plain, (k8_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4', k6_domain_1(u1_struct_0('#skF_3'), '#skF_6'))!=k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26])).
% 3.44/1.58  tff(c_311, plain, (k8_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4', k6_domain_1(u1_struct_0('#skF_3'), '#skF_6'))!=k2_pre_topc('#skF_2', k1_tarski('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_308, c_58])).
% 3.44/1.58  tff(c_477, plain, (k8_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4', k1_tarski('#skF_6'))!=k2_pre_topc('#skF_2', k1_tarski('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_475, c_311])).
% 3.44/1.58  tff(c_42, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_170])).
% 3.44/1.58  tff(c_40, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_170])).
% 3.44/1.58  tff(c_38, plain, (v5_pre_topc('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_170])).
% 3.44/1.58  tff(c_34, plain, (v3_borsuk_1('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_170])).
% 3.44/1.58  tff(c_476, plain, (~v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_90])).
% 3.44/1.58  tff(c_482, plain, (![A_179, B_180]: (m1_subset_1(k6_domain_1(A_179, B_180), k1_zfmisc_1(A_179)) | ~m1_subset_1(B_180, A_179) | v1_xboole_0(A_179))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.44/1.58  tff(c_490, plain, (m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_3')) | v1_xboole_0(u1_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_475, c_482])).
% 3.44/1.58  tff(c_497, plain, (m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | v1_xboole_0(u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_57, c_490])).
% 3.44/1.58  tff(c_498, plain, (m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_476, c_497])).
% 3.44/1.58  tff(c_36, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_170])).
% 3.44/1.58  tff(c_52, plain, (v3_tdlat_3('#skF_2')), inference(cnfTransformation, [status(thm)], [f_170])).
% 3.44/1.58  tff(c_309, plain, (~v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_89])).
% 3.44/1.58  tff(c_493, plain, (m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_2')) | v1_xboole_0(u1_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_308, c_482])).
% 3.44/1.58  tff(c_500, plain, (m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | v1_xboole_0(u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_493])).
% 3.44/1.58  tff(c_501, plain, (m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_309, c_500])).
% 3.44/1.58  tff(c_622, plain, (![A_206, B_207, C_208, E_209]: (k8_relset_1(u1_struct_0(A_206), u1_struct_0(B_207), C_208, E_209)=k2_pre_topc(A_206, E_209) | ~m1_subset_1(E_209, k1_zfmisc_1(u1_struct_0(A_206))) | ~m1_subset_1(E_209, k1_zfmisc_1(u1_struct_0(B_207))) | ~v3_borsuk_1(C_208, A_206, B_207) | ~m1_subset_1(C_208, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_206), u1_struct_0(B_207)))) | ~v5_pre_topc(C_208, A_206, B_207) | ~v1_funct_2(C_208, u1_struct_0(A_206), u1_struct_0(B_207)) | ~v1_funct_1(C_208) | ~m1_pre_topc(B_207, A_206) | ~v4_tex_2(B_207, A_206) | v2_struct_0(B_207) | ~l1_pre_topc(A_206) | ~v3_tdlat_3(A_206) | ~v2_pre_topc(A_206) | v2_struct_0(A_206))), inference(cnfTransformation, [status(thm)], [f_131])).
% 3.44/1.58  tff(c_628, plain, (![B_207, C_208]: (k8_relset_1(u1_struct_0('#skF_2'), u1_struct_0(B_207), C_208, k1_tarski('#skF_6'))=k2_pre_topc('#skF_2', k1_tarski('#skF_6')) | ~m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0(B_207))) | ~v3_borsuk_1(C_208, '#skF_2', B_207) | ~m1_subset_1(C_208, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0(B_207)))) | ~v5_pre_topc(C_208, '#skF_2', B_207) | ~v1_funct_2(C_208, u1_struct_0('#skF_2'), u1_struct_0(B_207)) | ~v1_funct_1(C_208) | ~m1_pre_topc(B_207, '#skF_2') | ~v4_tex_2(B_207, '#skF_2') | v2_struct_0(B_207) | ~l1_pre_topc('#skF_2') | ~v3_tdlat_3('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_501, c_622])).
% 3.44/1.58  tff(c_638, plain, (![B_207, C_208]: (k8_relset_1(u1_struct_0('#skF_2'), u1_struct_0(B_207), C_208, k1_tarski('#skF_6'))=k2_pre_topc('#skF_2', k1_tarski('#skF_6')) | ~m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0(B_207))) | ~v3_borsuk_1(C_208, '#skF_2', B_207) | ~m1_subset_1(C_208, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0(B_207)))) | ~v5_pre_topc(C_208, '#skF_2', B_207) | ~v1_funct_2(C_208, u1_struct_0('#skF_2'), u1_struct_0(B_207)) | ~v1_funct_1(C_208) | ~m1_pre_topc(B_207, '#skF_2') | ~v4_tex_2(B_207, '#skF_2') | v2_struct_0(B_207) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_628])).
% 3.44/1.58  tff(c_664, plain, (![B_218, C_219]: (k8_relset_1(u1_struct_0('#skF_2'), u1_struct_0(B_218), C_219, k1_tarski('#skF_6'))=k2_pre_topc('#skF_2', k1_tarski('#skF_6')) | ~m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0(B_218))) | ~v3_borsuk_1(C_219, '#skF_2', B_218) | ~m1_subset_1(C_219, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0(B_218)))) | ~v5_pre_topc(C_219, '#skF_2', B_218) | ~v1_funct_2(C_219, u1_struct_0('#skF_2'), u1_struct_0(B_218)) | ~v1_funct_1(C_219) | ~m1_pre_topc(B_218, '#skF_2') | ~v4_tex_2(B_218, '#skF_2') | v2_struct_0(B_218))), inference(negUnitSimplification, [status(thm)], [c_56, c_638])).
% 3.44/1.58  tff(c_671, plain, (k8_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4', k1_tarski('#skF_6'))=k2_pre_topc('#skF_2', k1_tarski('#skF_6')) | ~m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~v3_borsuk_1('#skF_4', '#skF_2', '#skF_3') | ~v5_pre_topc('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_2') | ~v4_tex_2('#skF_3', '#skF_2') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_36, c_664])).
% 3.44/1.58  tff(c_675, plain, (k8_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4', k1_tarski('#skF_6'))=k2_pre_topc('#skF_2', k1_tarski('#skF_6')) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_40, c_38, c_34, c_498, c_671])).
% 3.44/1.58  tff(c_677, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_477, c_675])).
% 3.44/1.58  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.44/1.58  
% 3.44/1.58  Inference rules
% 3.44/1.58  ----------------------
% 3.44/1.58  #Ref     : 0
% 3.44/1.58  #Sup     : 132
% 3.44/1.58  #Fact    : 0
% 3.44/1.58  #Define  : 0
% 3.44/1.58  #Split   : 14
% 3.44/1.58  #Chain   : 0
% 3.44/1.58  #Close   : 0
% 3.44/1.58  
% 3.44/1.58  Ordering : KBO
% 3.44/1.58  
% 3.44/1.58  Simplification rules
% 3.44/1.58  ----------------------
% 3.44/1.58  #Subsume      : 13
% 3.44/1.58  #Demod        : 54
% 3.44/1.58  #Tautology    : 32
% 3.44/1.58  #SimpNegUnit  : 19
% 3.44/1.58  #BackRed      : 3
% 3.44/1.58  
% 3.44/1.58  #Partial instantiations: 0
% 3.44/1.58  #Strategies tried      : 1
% 3.44/1.58  
% 3.44/1.58  Timing (in seconds)
% 3.44/1.58  ----------------------
% 3.44/1.58  Preprocessing        : 0.38
% 3.44/1.58  Parsing              : 0.18
% 3.44/1.58  CNF conversion       : 0.03
% 3.44/1.58  Main loop            : 0.42
% 3.44/1.58  Inferencing          : 0.16
% 3.44/1.58  Reduction            : 0.13
% 3.44/1.58  Demodulation         : 0.09
% 3.44/1.58  BG Simplification    : 0.03
% 3.44/1.58  Subsumption          : 0.06
% 3.44/1.58  Abstraction          : 0.03
% 3.44/1.58  MUC search           : 0.00
% 3.44/1.58  Cooper               : 0.00
% 3.44/1.58  Total                : 0.84
% 3.44/1.58  Index Insertion      : 0.00
% 3.44/1.58  Index Deletion       : 0.00
% 3.44/1.58  Index Matching       : 0.00
% 3.44/1.58  BG Taut test         : 0.00
%------------------------------------------------------------------------------
