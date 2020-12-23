%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:38 EST 2020

% Result     : Theorem 3.12s
% Output     : CNFRefutation 3.22s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 232 expanded)
%              Number of leaves         :   41 ( 102 expanded)
%              Depth                    :   13
%              Number of atoms          :  241 (1127 expanded)
%              Number of equality atoms :   21 ( 140 expanded)
%              Maximal formula depth    :   20 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_pre_topc > v3_borsuk_1 > v1_funct_2 > v4_tex_2 > v4_pre_topc > r2_hidden > m1_subset_1 > m1_pre_topc > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_pre_topc > k8_relset_1 > k6_domain_1 > k2_zfmisc_1 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v3_borsuk_1,type,(
    v3_borsuk_1: ( $i * $i * $i ) > $o )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

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

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v3_tdlat_3,type,(
    v3_tdlat_3: $i > $o )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_172,negated_conjecture,(
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

tff(f_95,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_71,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ? [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
          & ~ v1_xboole_0(B)
          & v4_pre_topc(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc7_pre_topc)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_49,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_56,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_88,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_133,axiom,(
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

tff(c_50,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_58,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_56,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_52,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_30,plain,(
    '#skF_7' = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_32,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_59,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_32])).

tff(c_101,plain,(
    ! [A_98,B_99] :
      ( k6_domain_1(A_98,B_99) = k1_tarski(B_99)
      | ~ m1_subset_1(B_99,A_98)
      | v1_xboole_0(A_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_113,plain,
    ( k6_domain_1(u1_struct_0('#skF_3'),'#skF_6') = k1_tarski('#skF_6')
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_59,c_101])).

tff(c_235,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_113])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_250,plain,(
    ! [A_117] :
      ( m1_subset_1('#skF_2'(A_117),k1_zfmisc_1(u1_struct_0(A_117)))
      | ~ l1_pre_topc(A_117)
      | ~ v2_pre_topc(A_117)
      | v2_struct_0(A_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_8,plain,(
    ! [C_8,B_7,A_6] :
      ( ~ v1_xboole_0(C_8)
      | ~ m1_subset_1(B_7,k1_zfmisc_1(C_8))
      | ~ r2_hidden(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_265,plain,(
    ! [A_118,A_119] :
      ( ~ v1_xboole_0(u1_struct_0(A_118))
      | ~ r2_hidden(A_119,'#skF_2'(A_118))
      | ~ l1_pre_topc(A_118)
      | ~ v2_pre_topc(A_118)
      | v2_struct_0(A_118) ) ),
    inference(resolution,[status(thm)],[c_250,c_8])).

tff(c_271,plain,(
    ! [A_120] :
      ( ~ v1_xboole_0(u1_struct_0(A_120))
      | ~ l1_pre_topc(A_120)
      | ~ v2_pre_topc(A_120)
      | v2_struct_0(A_120)
      | v1_xboole_0('#skF_2'(A_120)) ) ),
    inference(resolution,[status(thm)],[c_4,c_265])).

tff(c_274,plain,
    ( ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3')
    | v1_xboole_0('#skF_2'('#skF_3')) ),
    inference(resolution,[status(thm)],[c_235,c_271])).

tff(c_277,plain,
    ( v2_struct_0('#skF_3')
    | v1_xboole_0('#skF_2'('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_274])).

tff(c_278,plain,(
    v1_xboole_0('#skF_2'('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_277])).

tff(c_16,plain,(
    ! [A_15] :
      ( ~ v1_xboole_0('#skF_2'(A_15))
      | ~ l1_pre_topc(A_15)
      | ~ v2_pre_topc(A_15)
      | v2_struct_0(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_281,plain,
    ( ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_278,c_16])).

tff(c_284,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_281])).

tff(c_286,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_284])).

tff(c_287,plain,(
    k6_domain_1(u1_struct_0('#skF_3'),'#skF_6') = k1_tarski('#skF_6') ),
    inference(splitRight,[status(thm)],[c_113])).

tff(c_46,plain,(
    m1_pre_topc('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_92,plain,(
    ! [B_95,A_96] :
      ( v2_pre_topc(B_95)
      | ~ m1_pre_topc(B_95,A_96)
      | ~ l1_pre_topc(A_96)
      | ~ v2_pre_topc(A_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_95,plain,
    ( v2_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_92])).

tff(c_98,plain,(
    v2_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_95])).

tff(c_80,plain,(
    ! [B_89,A_90] :
      ( l1_pre_topc(B_89)
      | ~ m1_pre_topc(B_89,A_90)
      | ~ l1_pre_topc(A_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_83,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_80])).

tff(c_86,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_83])).

tff(c_34,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_112,plain,
    ( k6_domain_1(u1_struct_0('#skF_4'),'#skF_6') = k1_tarski('#skF_6')
    | v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_34,c_101])).

tff(c_114,plain,(
    v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_112])).

tff(c_198,plain,(
    ! [A_111] :
      ( m1_subset_1('#skF_2'(A_111),k1_zfmisc_1(u1_struct_0(A_111)))
      | ~ l1_pre_topc(A_111)
      | ~ v2_pre_topc(A_111)
      | v2_struct_0(A_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_206,plain,(
    ! [A_112,A_113] :
      ( ~ v1_xboole_0(u1_struct_0(A_112))
      | ~ r2_hidden(A_113,'#skF_2'(A_112))
      | ~ l1_pre_topc(A_112)
      | ~ v2_pre_topc(A_112)
      | v2_struct_0(A_112) ) ),
    inference(resolution,[status(thm)],[c_198,c_8])).

tff(c_212,plain,(
    ! [A_114] :
      ( ~ v1_xboole_0(u1_struct_0(A_114))
      | ~ l1_pre_topc(A_114)
      | ~ v2_pre_topc(A_114)
      | v2_struct_0(A_114)
      | v1_xboole_0('#skF_2'(A_114)) ) ),
    inference(resolution,[status(thm)],[c_4,c_206])).

tff(c_215,plain,
    ( ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4')
    | v1_xboole_0('#skF_2'('#skF_4')) ),
    inference(resolution,[status(thm)],[c_114,c_212])).

tff(c_218,plain,
    ( v2_struct_0('#skF_4')
    | v1_xboole_0('#skF_2'('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_86,c_215])).

tff(c_219,plain,(
    v1_xboole_0('#skF_2'('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_218])).

tff(c_222,plain,
    ( ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_219,c_16])).

tff(c_225,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_86,c_222])).

tff(c_227,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_225])).

tff(c_228,plain,(
    k6_domain_1(u1_struct_0('#skF_4'),'#skF_6') = k1_tarski('#skF_6') ),
    inference(splitRight,[status(thm)],[c_112])).

tff(c_28,plain,(
    k8_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5',k6_domain_1(u1_struct_0('#skF_4'),'#skF_6')) != k2_pre_topc('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),'#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_60,plain,(
    k8_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5',k6_domain_1(u1_struct_0('#skF_4'),'#skF_6')) != k2_pre_topc('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),'#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28])).

tff(c_230,plain,(
    k8_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5',k1_tarski('#skF_6')) != k2_pre_topc('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),'#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_228,c_60])).

tff(c_345,plain,(
    k8_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5',k1_tarski('#skF_6')) != k2_pre_topc('#skF_3',k1_tarski('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_287,c_230])).

tff(c_48,plain,(
    v4_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_44,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_42,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_40,plain,(
    v5_pre_topc('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_36,plain,(
    v3_borsuk_1('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_229,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_112])).

tff(c_293,plain,(
    ! [A_121,B_122] :
      ( m1_subset_1(k6_domain_1(A_121,B_122),k1_zfmisc_1(A_121))
      | ~ m1_subset_1(B_122,A_121)
      | v1_xboole_0(A_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_304,plain,
    ( m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4'))
    | v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_228,c_293])).

tff(c_311,plain,
    ( m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_304])).

tff(c_312,plain,(
    m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_229,c_311])).

tff(c_38,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_54,plain,(
    v3_tdlat_3('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_288,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_113])).

tff(c_301,plain,
    ( m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3'))
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_287,c_293])).

tff(c_308,plain,
    ( m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_301])).

tff(c_309,plain,(
    m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_288,c_308])).

tff(c_409,plain,(
    ! [A_140,B_141,C_142,E_143] :
      ( k8_relset_1(u1_struct_0(A_140),u1_struct_0(B_141),C_142,E_143) = k2_pre_topc(A_140,E_143)
      | ~ m1_subset_1(E_143,k1_zfmisc_1(u1_struct_0(A_140)))
      | ~ m1_subset_1(E_143,k1_zfmisc_1(u1_struct_0(B_141)))
      | ~ v3_borsuk_1(C_142,A_140,B_141)
      | ~ m1_subset_1(C_142,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_140),u1_struct_0(B_141))))
      | ~ v5_pre_topc(C_142,A_140,B_141)
      | ~ v1_funct_2(C_142,u1_struct_0(A_140),u1_struct_0(B_141))
      | ~ v1_funct_1(C_142)
      | ~ m1_pre_topc(B_141,A_140)
      | ~ v4_tex_2(B_141,A_140)
      | v2_struct_0(B_141)
      | ~ l1_pre_topc(A_140)
      | ~ v3_tdlat_3(A_140)
      | ~ v2_pre_topc(A_140)
      | v2_struct_0(A_140) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_421,plain,(
    ! [B_141,C_142] :
      ( k8_relset_1(u1_struct_0('#skF_3'),u1_struct_0(B_141),C_142,k1_tarski('#skF_6')) = k2_pre_topc('#skF_3',k1_tarski('#skF_6'))
      | ~ m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0(B_141)))
      | ~ v3_borsuk_1(C_142,'#skF_3',B_141)
      | ~ m1_subset_1(C_142,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_141))))
      | ~ v5_pre_topc(C_142,'#skF_3',B_141)
      | ~ v1_funct_2(C_142,u1_struct_0('#skF_3'),u1_struct_0(B_141))
      | ~ v1_funct_1(C_142)
      | ~ m1_pre_topc(B_141,'#skF_3')
      | ~ v4_tex_2(B_141,'#skF_3')
      | v2_struct_0(B_141)
      | ~ l1_pre_topc('#skF_3')
      | ~ v3_tdlat_3('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_309,c_409])).

tff(c_435,plain,(
    ! [B_141,C_142] :
      ( k8_relset_1(u1_struct_0('#skF_3'),u1_struct_0(B_141),C_142,k1_tarski('#skF_6')) = k2_pre_topc('#skF_3',k1_tarski('#skF_6'))
      | ~ m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0(B_141)))
      | ~ v3_borsuk_1(C_142,'#skF_3',B_141)
      | ~ m1_subset_1(C_142,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_141))))
      | ~ v5_pre_topc(C_142,'#skF_3',B_141)
      | ~ v1_funct_2(C_142,u1_struct_0('#skF_3'),u1_struct_0(B_141))
      | ~ v1_funct_1(C_142)
      | ~ m1_pre_topc(B_141,'#skF_3')
      | ~ v4_tex_2(B_141,'#skF_3')
      | v2_struct_0(B_141)
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_421])).

tff(c_484,plain,(
    ! [B_150,C_151] :
      ( k8_relset_1(u1_struct_0('#skF_3'),u1_struct_0(B_150),C_151,k1_tarski('#skF_6')) = k2_pre_topc('#skF_3',k1_tarski('#skF_6'))
      | ~ m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0(B_150)))
      | ~ v3_borsuk_1(C_151,'#skF_3',B_150)
      | ~ m1_subset_1(C_151,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_150))))
      | ~ v5_pre_topc(C_151,'#skF_3',B_150)
      | ~ v1_funct_2(C_151,u1_struct_0('#skF_3'),u1_struct_0(B_150))
      | ~ v1_funct_1(C_151)
      | ~ m1_pre_topc(B_150,'#skF_3')
      | ~ v4_tex_2(B_150,'#skF_3')
      | v2_struct_0(B_150) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_435])).

tff(c_491,plain,
    ( k8_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5',k1_tarski('#skF_6')) = k2_pre_topc('#skF_3',k1_tarski('#skF_6'))
    | ~ m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ v3_borsuk_1('#skF_5','#skF_3','#skF_4')
    | ~ v5_pre_topc('#skF_5','#skF_3','#skF_4')
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ v4_tex_2('#skF_4','#skF_3')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_484])).

tff(c_495,plain,
    ( k8_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5',k1_tarski('#skF_6')) = k2_pre_topc('#skF_3',k1_tarski('#skF_6'))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_40,c_36,c_312,c_491])).

tff(c_497,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_345,c_495])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:07:38 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.12/1.48  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.12/1.48  
% 3.12/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.22/1.49  %$ v5_pre_topc > v3_borsuk_1 > v1_funct_2 > v4_tex_2 > v4_pre_topc > r2_hidden > m1_subset_1 > m1_pre_topc > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_pre_topc > k8_relset_1 > k6_domain_1 > k2_zfmisc_1 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_4
% 3.22/1.49  
% 3.22/1.49  %Foreground sorts:
% 3.22/1.49  
% 3.22/1.49  
% 3.22/1.49  %Background operators:
% 3.22/1.49  
% 3.22/1.49  
% 3.22/1.49  %Foreground operators:
% 3.22/1.49  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.22/1.49  tff(v3_borsuk_1, type, v3_borsuk_1: ($i * $i * $i) > $o).
% 3.22/1.49  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.22/1.49  tff('#skF_2', type, '#skF_2': $i > $i).
% 3.22/1.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.22/1.49  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.22/1.49  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.22/1.49  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 3.22/1.49  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.22/1.49  tff(v4_tex_2, type, v4_tex_2: ($i * $i) > $o).
% 3.22/1.49  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.22/1.49  tff('#skF_7', type, '#skF_7': $i).
% 3.22/1.49  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 3.22/1.49  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.22/1.49  tff('#skF_5', type, '#skF_5': $i).
% 3.22/1.49  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.22/1.49  tff('#skF_6', type, '#skF_6': $i).
% 3.22/1.49  tff('#skF_3', type, '#skF_3': $i).
% 3.22/1.49  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.22/1.49  tff(v3_tdlat_3, type, v3_tdlat_3: $i > $o).
% 3.22/1.49  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 3.22/1.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.22/1.49  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.22/1.49  tff('#skF_4', type, '#skF_4': $i).
% 3.22/1.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.22/1.49  tff(v5_pre_topc, type, v5_pre_topc: ($i * $i * $i) > $o).
% 3.22/1.49  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.22/1.49  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.22/1.49  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.22/1.49  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.22/1.49  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 3.22/1.49  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.22/1.49  
% 3.22/1.50  tff(f_172, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v4_tex_2(B, A)) & m1_pre_topc(B, A)) => (![C]: ((((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & v5_pre_topc(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (v3_borsuk_1(C, A, B) => (![D]: (m1_subset_1(D, u1_struct_0(B)) => (![E]: (m1_subset_1(E, u1_struct_0(A)) => ((D = E) => (k8_relset_1(u1_struct_0(A), u1_struct_0(B), C, k6_domain_1(u1_struct_0(B), D)) = k2_pre_topc(A, k6_domain_1(u1_struct_0(A), E))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_tex_2)).
% 3.22/1.50  tff(f_95, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 3.22/1.50  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.22/1.50  tff(f_71, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (?[B]: ((m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) & ~v1_xboole_0(B)) & v4_pre_topc(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc7_pre_topc)).
% 3.22/1.50  tff(f_40, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 3.22/1.50  tff(f_49, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_pre_topc)).
% 3.22/1.50  tff(f_56, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 3.22/1.50  tff(f_88, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 3.22/1.50  tff(f_133, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v4_tex_2(B, A)) & m1_pre_topc(B, A)) => (![C]: ((((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & v5_pre_topc(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (v3_borsuk_1(C, A, B) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => (![E]: (m1_subset_1(E, k1_zfmisc_1(u1_struct_0(A))) => ((D = E) => (k8_relset_1(u1_struct_0(A), u1_struct_0(B), C, D) = k2_pre_topc(A, E)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t76_tex_2)).
% 3.22/1.50  tff(c_50, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_172])).
% 3.22/1.50  tff(c_58, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_172])).
% 3.22/1.50  tff(c_56, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_172])).
% 3.22/1.50  tff(c_52, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_172])).
% 3.22/1.50  tff(c_30, plain, ('#skF_7'='#skF_6'), inference(cnfTransformation, [status(thm)], [f_172])).
% 3.22/1.50  tff(c_32, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_172])).
% 3.22/1.50  tff(c_59, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_32])).
% 3.22/1.50  tff(c_101, plain, (![A_98, B_99]: (k6_domain_1(A_98, B_99)=k1_tarski(B_99) | ~m1_subset_1(B_99, A_98) | v1_xboole_0(A_98))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.22/1.50  tff(c_113, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_6')=k1_tarski('#skF_6') | v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_59, c_101])).
% 3.22/1.50  tff(c_235, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_113])).
% 3.22/1.50  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.22/1.50  tff(c_250, plain, (![A_117]: (m1_subset_1('#skF_2'(A_117), k1_zfmisc_1(u1_struct_0(A_117))) | ~l1_pre_topc(A_117) | ~v2_pre_topc(A_117) | v2_struct_0(A_117))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.22/1.50  tff(c_8, plain, (![C_8, B_7, A_6]: (~v1_xboole_0(C_8) | ~m1_subset_1(B_7, k1_zfmisc_1(C_8)) | ~r2_hidden(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.22/1.50  tff(c_265, plain, (![A_118, A_119]: (~v1_xboole_0(u1_struct_0(A_118)) | ~r2_hidden(A_119, '#skF_2'(A_118)) | ~l1_pre_topc(A_118) | ~v2_pre_topc(A_118) | v2_struct_0(A_118))), inference(resolution, [status(thm)], [c_250, c_8])).
% 3.22/1.50  tff(c_271, plain, (![A_120]: (~v1_xboole_0(u1_struct_0(A_120)) | ~l1_pre_topc(A_120) | ~v2_pre_topc(A_120) | v2_struct_0(A_120) | v1_xboole_0('#skF_2'(A_120)))), inference(resolution, [status(thm)], [c_4, c_265])).
% 3.22/1.50  tff(c_274, plain, (~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | v1_xboole_0('#skF_2'('#skF_3'))), inference(resolution, [status(thm)], [c_235, c_271])).
% 3.22/1.50  tff(c_277, plain, (v2_struct_0('#skF_3') | v1_xboole_0('#skF_2'('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_52, c_274])).
% 3.22/1.50  tff(c_278, plain, (v1_xboole_0('#skF_2'('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_58, c_277])).
% 3.22/1.50  tff(c_16, plain, (![A_15]: (~v1_xboole_0('#skF_2'(A_15)) | ~l1_pre_topc(A_15) | ~v2_pre_topc(A_15) | v2_struct_0(A_15))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.22/1.50  tff(c_281, plain, (~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_278, c_16])).
% 3.22/1.50  tff(c_284, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_52, c_281])).
% 3.22/1.50  tff(c_286, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_284])).
% 3.22/1.50  tff(c_287, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_6')=k1_tarski('#skF_6')), inference(splitRight, [status(thm)], [c_113])).
% 3.22/1.50  tff(c_46, plain, (m1_pre_topc('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_172])).
% 3.22/1.50  tff(c_92, plain, (![B_95, A_96]: (v2_pre_topc(B_95) | ~m1_pre_topc(B_95, A_96) | ~l1_pre_topc(A_96) | ~v2_pre_topc(A_96))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.22/1.50  tff(c_95, plain, (v2_pre_topc('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_46, c_92])).
% 3.22/1.50  tff(c_98, plain, (v2_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_52, c_95])).
% 3.22/1.50  tff(c_80, plain, (![B_89, A_90]: (l1_pre_topc(B_89) | ~m1_pre_topc(B_89, A_90) | ~l1_pre_topc(A_90))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.22/1.50  tff(c_83, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_46, c_80])).
% 3.22/1.50  tff(c_86, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_83])).
% 3.22/1.50  tff(c_34, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_172])).
% 3.22/1.50  tff(c_112, plain, (k6_domain_1(u1_struct_0('#skF_4'), '#skF_6')=k1_tarski('#skF_6') | v1_xboole_0(u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_34, c_101])).
% 3.22/1.50  tff(c_114, plain, (v1_xboole_0(u1_struct_0('#skF_4'))), inference(splitLeft, [status(thm)], [c_112])).
% 3.22/1.50  tff(c_198, plain, (![A_111]: (m1_subset_1('#skF_2'(A_111), k1_zfmisc_1(u1_struct_0(A_111))) | ~l1_pre_topc(A_111) | ~v2_pre_topc(A_111) | v2_struct_0(A_111))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.22/1.50  tff(c_206, plain, (![A_112, A_113]: (~v1_xboole_0(u1_struct_0(A_112)) | ~r2_hidden(A_113, '#skF_2'(A_112)) | ~l1_pre_topc(A_112) | ~v2_pre_topc(A_112) | v2_struct_0(A_112))), inference(resolution, [status(thm)], [c_198, c_8])).
% 3.22/1.50  tff(c_212, plain, (![A_114]: (~v1_xboole_0(u1_struct_0(A_114)) | ~l1_pre_topc(A_114) | ~v2_pre_topc(A_114) | v2_struct_0(A_114) | v1_xboole_0('#skF_2'(A_114)))), inference(resolution, [status(thm)], [c_4, c_206])).
% 3.22/1.50  tff(c_215, plain, (~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | v1_xboole_0('#skF_2'('#skF_4'))), inference(resolution, [status(thm)], [c_114, c_212])).
% 3.22/1.50  tff(c_218, plain, (v2_struct_0('#skF_4') | v1_xboole_0('#skF_2'('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_86, c_215])).
% 3.22/1.50  tff(c_219, plain, (v1_xboole_0('#skF_2'('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_50, c_218])).
% 3.22/1.50  tff(c_222, plain, (~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_219, c_16])).
% 3.22/1.50  tff(c_225, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_98, c_86, c_222])).
% 3.22/1.50  tff(c_227, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_225])).
% 3.22/1.50  tff(c_228, plain, (k6_domain_1(u1_struct_0('#skF_4'), '#skF_6')=k1_tarski('#skF_6')), inference(splitRight, [status(thm)], [c_112])).
% 3.22/1.50  tff(c_28, plain, (k8_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5', k6_domain_1(u1_struct_0('#skF_4'), '#skF_6'))!=k2_pre_topc('#skF_3', k6_domain_1(u1_struct_0('#skF_3'), '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_172])).
% 3.22/1.50  tff(c_60, plain, (k8_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5', k6_domain_1(u1_struct_0('#skF_4'), '#skF_6'))!=k2_pre_topc('#skF_3', k6_domain_1(u1_struct_0('#skF_3'), '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28])).
% 3.22/1.50  tff(c_230, plain, (k8_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5', k1_tarski('#skF_6'))!=k2_pre_topc('#skF_3', k6_domain_1(u1_struct_0('#skF_3'), '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_228, c_60])).
% 3.22/1.50  tff(c_345, plain, (k8_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5', k1_tarski('#skF_6'))!=k2_pre_topc('#skF_3', k1_tarski('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_287, c_230])).
% 3.22/1.50  tff(c_48, plain, (v4_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_172])).
% 3.22/1.50  tff(c_44, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_172])).
% 3.22/1.50  tff(c_42, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_172])).
% 3.22/1.50  tff(c_40, plain, (v5_pre_topc('#skF_5', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_172])).
% 3.22/1.50  tff(c_36, plain, (v3_borsuk_1('#skF_5', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_172])).
% 3.22/1.50  tff(c_229, plain, (~v1_xboole_0(u1_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_112])).
% 3.22/1.50  tff(c_293, plain, (![A_121, B_122]: (m1_subset_1(k6_domain_1(A_121, B_122), k1_zfmisc_1(A_121)) | ~m1_subset_1(B_122, A_121) | v1_xboole_0(A_121))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.22/1.50  tff(c_304, plain, (m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_4')) | v1_xboole_0(u1_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_228, c_293])).
% 3.22/1.50  tff(c_311, plain, (m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | v1_xboole_0(u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_304])).
% 3.22/1.50  tff(c_312, plain, (m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_229, c_311])).
% 3.22/1.50  tff(c_38, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_172])).
% 3.22/1.50  tff(c_54, plain, (v3_tdlat_3('#skF_3')), inference(cnfTransformation, [status(thm)], [f_172])).
% 3.22/1.50  tff(c_288, plain, (~v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_113])).
% 3.22/1.50  tff(c_301, plain, (m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_3')) | v1_xboole_0(u1_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_287, c_293])).
% 3.22/1.50  tff(c_308, plain, (m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | v1_xboole_0(u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_59, c_301])).
% 3.22/1.50  tff(c_309, plain, (m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_288, c_308])).
% 3.22/1.50  tff(c_409, plain, (![A_140, B_141, C_142, E_143]: (k8_relset_1(u1_struct_0(A_140), u1_struct_0(B_141), C_142, E_143)=k2_pre_topc(A_140, E_143) | ~m1_subset_1(E_143, k1_zfmisc_1(u1_struct_0(A_140))) | ~m1_subset_1(E_143, k1_zfmisc_1(u1_struct_0(B_141))) | ~v3_borsuk_1(C_142, A_140, B_141) | ~m1_subset_1(C_142, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_140), u1_struct_0(B_141)))) | ~v5_pre_topc(C_142, A_140, B_141) | ~v1_funct_2(C_142, u1_struct_0(A_140), u1_struct_0(B_141)) | ~v1_funct_1(C_142) | ~m1_pre_topc(B_141, A_140) | ~v4_tex_2(B_141, A_140) | v2_struct_0(B_141) | ~l1_pre_topc(A_140) | ~v3_tdlat_3(A_140) | ~v2_pre_topc(A_140) | v2_struct_0(A_140))), inference(cnfTransformation, [status(thm)], [f_133])).
% 3.22/1.50  tff(c_421, plain, (![B_141, C_142]: (k8_relset_1(u1_struct_0('#skF_3'), u1_struct_0(B_141), C_142, k1_tarski('#skF_6'))=k2_pre_topc('#skF_3', k1_tarski('#skF_6')) | ~m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0(B_141))) | ~v3_borsuk_1(C_142, '#skF_3', B_141) | ~m1_subset_1(C_142, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_141)))) | ~v5_pre_topc(C_142, '#skF_3', B_141) | ~v1_funct_2(C_142, u1_struct_0('#skF_3'), u1_struct_0(B_141)) | ~v1_funct_1(C_142) | ~m1_pre_topc(B_141, '#skF_3') | ~v4_tex_2(B_141, '#skF_3') | v2_struct_0(B_141) | ~l1_pre_topc('#skF_3') | ~v3_tdlat_3('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_309, c_409])).
% 3.22/1.50  tff(c_435, plain, (![B_141, C_142]: (k8_relset_1(u1_struct_0('#skF_3'), u1_struct_0(B_141), C_142, k1_tarski('#skF_6'))=k2_pre_topc('#skF_3', k1_tarski('#skF_6')) | ~m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0(B_141))) | ~v3_borsuk_1(C_142, '#skF_3', B_141) | ~m1_subset_1(C_142, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_141)))) | ~v5_pre_topc(C_142, '#skF_3', B_141) | ~v1_funct_2(C_142, u1_struct_0('#skF_3'), u1_struct_0(B_141)) | ~v1_funct_1(C_142) | ~m1_pre_topc(B_141, '#skF_3') | ~v4_tex_2(B_141, '#skF_3') | v2_struct_0(B_141) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_421])).
% 3.22/1.50  tff(c_484, plain, (![B_150, C_151]: (k8_relset_1(u1_struct_0('#skF_3'), u1_struct_0(B_150), C_151, k1_tarski('#skF_6'))=k2_pre_topc('#skF_3', k1_tarski('#skF_6')) | ~m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0(B_150))) | ~v3_borsuk_1(C_151, '#skF_3', B_150) | ~m1_subset_1(C_151, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_150)))) | ~v5_pre_topc(C_151, '#skF_3', B_150) | ~v1_funct_2(C_151, u1_struct_0('#skF_3'), u1_struct_0(B_150)) | ~v1_funct_1(C_151) | ~m1_pre_topc(B_150, '#skF_3') | ~v4_tex_2(B_150, '#skF_3') | v2_struct_0(B_150))), inference(negUnitSimplification, [status(thm)], [c_58, c_435])).
% 3.22/1.50  tff(c_491, plain, (k8_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5', k1_tarski('#skF_6'))=k2_pre_topc('#skF_3', k1_tarski('#skF_6')) | ~m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~v3_borsuk_1('#skF_5', '#skF_3', '#skF_4') | ~v5_pre_topc('#skF_5', '#skF_3', '#skF_4') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_4')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_3') | ~v4_tex_2('#skF_4', '#skF_3') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_38, c_484])).
% 3.22/1.50  tff(c_495, plain, (k8_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5', k1_tarski('#skF_6'))=k2_pre_topc('#skF_3', k1_tarski('#skF_6')) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_40, c_36, c_312, c_491])).
% 3.22/1.50  tff(c_497, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_345, c_495])).
% 3.22/1.50  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.22/1.50  
% 3.22/1.50  Inference rules
% 3.22/1.50  ----------------------
% 3.22/1.50  #Ref     : 0
% 3.22/1.50  #Sup     : 93
% 3.22/1.50  #Fact    : 0
% 3.22/1.50  #Define  : 0
% 3.22/1.50  #Split   : 10
% 3.22/1.50  #Chain   : 0
% 3.22/1.50  #Close   : 0
% 3.22/1.50  
% 3.22/1.50  Ordering : KBO
% 3.22/1.51  
% 3.22/1.51  Simplification rules
% 3.22/1.51  ----------------------
% 3.22/1.51  #Subsume      : 4
% 3.22/1.51  #Demod        : 50
% 3.22/1.51  #Tautology    : 23
% 3.22/1.51  #SimpNegUnit  : 16
% 3.22/1.51  #BackRed      : 2
% 3.22/1.51  
% 3.22/1.51  #Partial instantiations: 0
% 3.22/1.51  #Strategies tried      : 1
% 3.22/1.51  
% 3.22/1.51  Timing (in seconds)
% 3.22/1.51  ----------------------
% 3.22/1.51  Preprocessing        : 0.38
% 3.22/1.51  Parsing              : 0.20
% 3.22/1.51  CNF conversion       : 0.03
% 3.22/1.51  Main loop            : 0.34
% 3.22/1.51  Inferencing          : 0.12
% 3.22/1.51  Reduction            : 0.11
% 3.22/1.51  Demodulation         : 0.08
% 3.22/1.51  BG Simplification    : 0.02
% 3.22/1.51  Subsumption          : 0.07
% 3.22/1.51  Abstraction          : 0.01
% 3.22/1.51  MUC search           : 0.00
% 3.22/1.51  Cooper               : 0.00
% 3.22/1.51  Total                : 0.76
% 3.22/1.51  Index Insertion      : 0.00
% 3.22/1.51  Index Deletion       : 0.00
% 3.22/1.51  Index Matching       : 0.00
% 3.22/1.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
