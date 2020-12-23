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
% DateTime   : Thu Dec  3 10:30:41 EST 2020

% Result     : Theorem 3.50s
% Output     : CNFRefutation 3.50s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 226 expanded)
%              Number of leaves         :   41 (  99 expanded)
%              Depth                    :   13
%              Number of atoms          :  275 (1090 expanded)
%              Number of equality atoms :   22 ( 140 expanded)
%              Maximal formula depth    :   20 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_pre_topc > v3_borsuk_1 > v1_funct_2 > v4_tex_2 > v3_tex_2 > r2_hidden > m1_subset_1 > m1_pre_topc > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_pre_topc > k8_relset_1 > k6_domain_1 > k2_zfmisc_1 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2

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

tff(f_180,negated_conjecture,(
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

tff(f_64,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_71,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_88,axiom,(
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

tff(f_103,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( v1_xboole_0(B)
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
         => ~ v3_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_tex_2)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_57,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_141,axiom,(
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

tff(c_52,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_60,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_54,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_48,plain,(
    m1_pre_topc('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_58,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_50,plain,(
    v4_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_36,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_87,plain,(
    ! [A_100,B_101] :
      ( k6_domain_1(A_100,B_101) = k1_tarski(B_101)
      | ~ m1_subset_1(B_101,A_100)
      | v1_xboole_0(A_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_99,plain,
    ( k6_domain_1(u1_struct_0('#skF_4'),'#skF_6') = k1_tarski('#skF_6')
    | v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_36,c_87])).

tff(c_314,plain,(
    v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_99])).

tff(c_16,plain,(
    ! [B_22,A_20] :
      ( m1_subset_1(u1_struct_0(B_22),k1_zfmisc_1(u1_struct_0(A_20)))
      | ~ m1_pre_topc(B_22,A_20)
      | ~ l1_pre_topc(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_497,plain,(
    ! [B_191,A_192] :
      ( v3_tex_2(u1_struct_0(B_191),A_192)
      | ~ m1_subset_1(u1_struct_0(B_191),k1_zfmisc_1(u1_struct_0(A_192)))
      | ~ v4_tex_2(B_191,A_192)
      | ~ m1_pre_topc(B_191,A_192)
      | ~ l1_pre_topc(A_192)
      | v2_struct_0(A_192) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_502,plain,(
    ! [B_193,A_194] :
      ( v3_tex_2(u1_struct_0(B_193),A_194)
      | ~ v4_tex_2(B_193,A_194)
      | v2_struct_0(A_194)
      | ~ m1_pre_topc(B_193,A_194)
      | ~ l1_pre_topc(A_194) ) ),
    inference(resolution,[status(thm)],[c_16,c_497])).

tff(c_382,plain,(
    ! [B_170,A_171] :
      ( ~ v3_tex_2(B_170,A_171)
      | ~ m1_subset_1(B_170,k1_zfmisc_1(u1_struct_0(A_171)))
      | ~ v1_xboole_0(B_170)
      | ~ l1_pre_topc(A_171)
      | ~ v2_pre_topc(A_171)
      | v2_struct_0(A_171) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_397,plain,(
    ! [B_22,A_20] :
      ( ~ v3_tex_2(u1_struct_0(B_22),A_20)
      | ~ v1_xboole_0(u1_struct_0(B_22))
      | ~ v2_pre_topc(A_20)
      | v2_struct_0(A_20)
      | ~ m1_pre_topc(B_22,A_20)
      | ~ l1_pre_topc(A_20) ) ),
    inference(resolution,[status(thm)],[c_16,c_382])).

tff(c_507,plain,(
    ! [B_195,A_196] :
      ( ~ v1_xboole_0(u1_struct_0(B_195))
      | ~ v2_pre_topc(A_196)
      | ~ v4_tex_2(B_195,A_196)
      | v2_struct_0(A_196)
      | ~ m1_pre_topc(B_195,A_196)
      | ~ l1_pre_topc(A_196) ) ),
    inference(resolution,[status(thm)],[c_502,c_397])).

tff(c_511,plain,(
    ! [A_197] :
      ( ~ v2_pre_topc(A_197)
      | ~ v4_tex_2('#skF_4',A_197)
      | v2_struct_0(A_197)
      | ~ m1_pre_topc('#skF_4',A_197)
      | ~ l1_pre_topc(A_197) ) ),
    inference(resolution,[status(thm)],[c_314,c_507])).

tff(c_518,plain,
    ( ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_511])).

tff(c_522,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_48,c_58,c_518])).

tff(c_524,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_522])).

tff(c_525,plain,(
    k6_domain_1(u1_struct_0('#skF_4'),'#skF_6') = k1_tarski('#skF_6') ),
    inference(splitRight,[status(thm)],[c_99])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_32,plain,(
    '#skF_7' = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_34,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_61,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_34])).

tff(c_98,plain,
    ( k6_domain_1(u1_struct_0('#skF_3'),'#skF_6') = k1_tarski('#skF_6')
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_61,c_87])).

tff(c_100,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_98])).

tff(c_254,plain,(
    ! [B_142,A_143] :
      ( m1_subset_1(u1_struct_0(B_142),k1_zfmisc_1(u1_struct_0(A_143)))
      | ~ m1_pre_topc(B_142,A_143)
      | ~ l1_pre_topc(A_143) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_8,plain,(
    ! [C_8,B_7,A_6] :
      ( ~ v1_xboole_0(C_8)
      | ~ m1_subset_1(B_7,k1_zfmisc_1(C_8))
      | ~ r2_hidden(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_284,plain,(
    ! [A_148,A_149,B_150] :
      ( ~ v1_xboole_0(u1_struct_0(A_148))
      | ~ r2_hidden(A_149,u1_struct_0(B_150))
      | ~ m1_pre_topc(B_150,A_148)
      | ~ l1_pre_topc(A_148) ) ),
    inference(resolution,[status(thm)],[c_254,c_8])).

tff(c_286,plain,(
    ! [A_149,B_150] :
      ( ~ r2_hidden(A_149,u1_struct_0(B_150))
      | ~ m1_pre_topc(B_150,'#skF_3')
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_100,c_284])).

tff(c_290,plain,(
    ! [A_151,B_152] :
      ( ~ r2_hidden(A_151,u1_struct_0(B_152))
      | ~ m1_pre_topc(B_152,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_286])).

tff(c_297,plain,(
    ! [B_153] :
      ( ~ m1_pre_topc(B_153,'#skF_3')
      | v1_xboole_0(u1_struct_0(B_153)) ) ),
    inference(resolution,[status(thm)],[c_4,c_290])).

tff(c_101,plain,(
    v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_99])).

tff(c_192,plain,(
    ! [B_133,A_134] :
      ( v3_tex_2(u1_struct_0(B_133),A_134)
      | ~ m1_subset_1(u1_struct_0(B_133),k1_zfmisc_1(u1_struct_0(A_134)))
      | ~ v4_tex_2(B_133,A_134)
      | ~ m1_pre_topc(B_133,A_134)
      | ~ l1_pre_topc(A_134)
      | v2_struct_0(A_134) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_197,plain,(
    ! [B_135,A_136] :
      ( v3_tex_2(u1_struct_0(B_135),A_136)
      | ~ v4_tex_2(B_135,A_136)
      | v2_struct_0(A_136)
      | ~ m1_pre_topc(B_135,A_136)
      | ~ l1_pre_topc(A_136) ) ),
    inference(resolution,[status(thm)],[c_16,c_192])).

tff(c_160,plain,(
    ! [B_124,A_125] :
      ( ~ v3_tex_2(B_124,A_125)
      | ~ m1_subset_1(B_124,k1_zfmisc_1(u1_struct_0(A_125)))
      | ~ v1_xboole_0(B_124)
      | ~ l1_pre_topc(A_125)
      | ~ v2_pre_topc(A_125)
      | v2_struct_0(A_125) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_168,plain,(
    ! [B_22,A_20] :
      ( ~ v3_tex_2(u1_struct_0(B_22),A_20)
      | ~ v1_xboole_0(u1_struct_0(B_22))
      | ~ v2_pre_topc(A_20)
      | v2_struct_0(A_20)
      | ~ m1_pre_topc(B_22,A_20)
      | ~ l1_pre_topc(A_20) ) ),
    inference(resolution,[status(thm)],[c_16,c_160])).

tff(c_202,plain,(
    ! [B_137,A_138] :
      ( ~ v1_xboole_0(u1_struct_0(B_137))
      | ~ v2_pre_topc(A_138)
      | ~ v4_tex_2(B_137,A_138)
      | v2_struct_0(A_138)
      | ~ m1_pre_topc(B_137,A_138)
      | ~ l1_pre_topc(A_138) ) ),
    inference(resolution,[status(thm)],[c_197,c_168])).

tff(c_212,plain,(
    ! [A_139] :
      ( ~ v2_pre_topc(A_139)
      | ~ v4_tex_2('#skF_4',A_139)
      | v2_struct_0(A_139)
      | ~ m1_pre_topc('#skF_4',A_139)
      | ~ l1_pre_topc(A_139) ) ),
    inference(resolution,[status(thm)],[c_101,c_202])).

tff(c_219,plain,
    ( ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_212])).

tff(c_223,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_48,c_58,c_219])).

tff(c_225,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_223])).

tff(c_227,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_99])).

tff(c_302,plain,(
    ~ m1_pre_topc('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_297,c_227])).

tff(c_307,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_302])).

tff(c_308,plain,(
    k6_domain_1(u1_struct_0('#skF_3'),'#skF_6') = k1_tarski('#skF_6') ),
    inference(splitRight,[status(thm)],[c_98])).

tff(c_30,plain,(
    k8_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5',k6_domain_1(u1_struct_0('#skF_4'),'#skF_6')) != k2_pre_topc('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),'#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_62,plain,(
    k8_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5',k6_domain_1(u1_struct_0('#skF_4'),'#skF_6')) != k2_pre_topc('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),'#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30])).

tff(c_527,plain,(
    k8_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5',k6_domain_1(u1_struct_0('#skF_4'),'#skF_6')) != k2_pre_topc('#skF_3',k1_tarski('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_308,c_62])).

tff(c_528,plain,(
    k8_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5',k1_tarski('#skF_6')) != k2_pre_topc('#skF_3',k1_tarski('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_525,c_527])).

tff(c_46,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_44,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_42,plain,(
    v5_pre_topc('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_38,plain,(
    v3_borsuk_1('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_526,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_99])).

tff(c_533,plain,(
    ! [A_198,B_199] :
      ( m1_subset_1(k6_domain_1(A_198,B_199),k1_zfmisc_1(A_198))
      | ~ m1_subset_1(B_199,A_198)
      | v1_xboole_0(A_198) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_541,plain,
    ( m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4'))
    | v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_525,c_533])).

tff(c_548,plain,
    ( m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_541])).

tff(c_549,plain,(
    m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_526,c_548])).

tff(c_40,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_56,plain,(
    v3_tdlat_3('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_309,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_98])).

tff(c_544,plain,
    ( m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3'))
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_308,c_533])).

tff(c_551,plain,
    ( m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_544])).

tff(c_552,plain,(
    m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_309,c_551])).

tff(c_789,plain,(
    ! [A_246,B_247,C_248,E_249] :
      ( k8_relset_1(u1_struct_0(A_246),u1_struct_0(B_247),C_248,E_249) = k2_pre_topc(A_246,E_249)
      | ~ m1_subset_1(E_249,k1_zfmisc_1(u1_struct_0(A_246)))
      | ~ m1_subset_1(E_249,k1_zfmisc_1(u1_struct_0(B_247)))
      | ~ v3_borsuk_1(C_248,A_246,B_247)
      | ~ m1_subset_1(C_248,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_246),u1_struct_0(B_247))))
      | ~ v5_pre_topc(C_248,A_246,B_247)
      | ~ v1_funct_2(C_248,u1_struct_0(A_246),u1_struct_0(B_247))
      | ~ v1_funct_1(C_248)
      | ~ m1_pre_topc(B_247,A_246)
      | ~ v4_tex_2(B_247,A_246)
      | v2_struct_0(B_247)
      | ~ l1_pre_topc(A_246)
      | ~ v3_tdlat_3(A_246)
      | ~ v2_pre_topc(A_246)
      | v2_struct_0(A_246) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_799,plain,(
    ! [B_247,C_248] :
      ( k8_relset_1(u1_struct_0('#skF_3'),u1_struct_0(B_247),C_248,k1_tarski('#skF_6')) = k2_pre_topc('#skF_3',k1_tarski('#skF_6'))
      | ~ m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0(B_247)))
      | ~ v3_borsuk_1(C_248,'#skF_3',B_247)
      | ~ m1_subset_1(C_248,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_247))))
      | ~ v5_pre_topc(C_248,'#skF_3',B_247)
      | ~ v1_funct_2(C_248,u1_struct_0('#skF_3'),u1_struct_0(B_247))
      | ~ v1_funct_1(C_248)
      | ~ m1_pre_topc(B_247,'#skF_3')
      | ~ v4_tex_2(B_247,'#skF_3')
      | v2_struct_0(B_247)
      | ~ l1_pre_topc('#skF_3')
      | ~ v3_tdlat_3('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_552,c_789])).

tff(c_811,plain,(
    ! [B_247,C_248] :
      ( k8_relset_1(u1_struct_0('#skF_3'),u1_struct_0(B_247),C_248,k1_tarski('#skF_6')) = k2_pre_topc('#skF_3',k1_tarski('#skF_6'))
      | ~ m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0(B_247)))
      | ~ v3_borsuk_1(C_248,'#skF_3',B_247)
      | ~ m1_subset_1(C_248,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_247))))
      | ~ v5_pre_topc(C_248,'#skF_3',B_247)
      | ~ v1_funct_2(C_248,u1_struct_0('#skF_3'),u1_struct_0(B_247))
      | ~ v1_funct_1(C_248)
      | ~ m1_pre_topc(B_247,'#skF_3')
      | ~ v4_tex_2(B_247,'#skF_3')
      | v2_struct_0(B_247)
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_799])).

tff(c_865,plain,(
    ! [B_260,C_261] :
      ( k8_relset_1(u1_struct_0('#skF_3'),u1_struct_0(B_260),C_261,k1_tarski('#skF_6')) = k2_pre_topc('#skF_3',k1_tarski('#skF_6'))
      | ~ m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0(B_260)))
      | ~ v3_borsuk_1(C_261,'#skF_3',B_260)
      | ~ m1_subset_1(C_261,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_260))))
      | ~ v5_pre_topc(C_261,'#skF_3',B_260)
      | ~ v1_funct_2(C_261,u1_struct_0('#skF_3'),u1_struct_0(B_260))
      | ~ v1_funct_1(C_261)
      | ~ m1_pre_topc(B_260,'#skF_3')
      | ~ v4_tex_2(B_260,'#skF_3')
      | v2_struct_0(B_260) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_811])).

tff(c_872,plain,
    ( k8_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5',k1_tarski('#skF_6')) = k2_pre_topc('#skF_3',k1_tarski('#skF_6'))
    | ~ m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ v3_borsuk_1('#skF_5','#skF_3','#skF_4')
    | ~ v5_pre_topc('#skF_5','#skF_3','#skF_4')
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ v4_tex_2('#skF_4','#skF_3')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_865])).

tff(c_876,plain,
    ( k8_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5',k1_tarski('#skF_6')) = k2_pre_topc('#skF_3',k1_tarski('#skF_6'))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_42,c_38,c_549,c_872])).

tff(c_878,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_528,c_876])).
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
% 0.13/0.34  % DateTime   : Tue Dec  1 13:09:26 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.50/1.57  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.50/1.57  
% 3.50/1.57  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.50/1.58  %$ v5_pre_topc > v3_borsuk_1 > v1_funct_2 > v4_tex_2 > v3_tex_2 > r2_hidden > m1_subset_1 > m1_pre_topc > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_pre_topc > k8_relset_1 > k6_domain_1 > k2_zfmisc_1 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2
% 3.50/1.58  
% 3.50/1.58  %Foreground sorts:
% 3.50/1.58  
% 3.50/1.58  
% 3.50/1.58  %Background operators:
% 3.50/1.58  
% 3.50/1.58  
% 3.50/1.58  %Foreground operators:
% 3.50/1.58  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.50/1.58  tff(v3_borsuk_1, type, v3_borsuk_1: ($i * $i * $i) > $o).
% 3.50/1.58  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.50/1.58  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.50/1.58  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.50/1.58  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.50/1.58  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 3.50/1.58  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.50/1.58  tff(v4_tex_2, type, v4_tex_2: ($i * $i) > $o).
% 3.50/1.58  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.50/1.58  tff('#skF_7', type, '#skF_7': $i).
% 3.50/1.58  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 3.50/1.58  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.50/1.58  tff('#skF_5', type, '#skF_5': $i).
% 3.50/1.58  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 3.50/1.58  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.50/1.58  tff('#skF_6', type, '#skF_6': $i).
% 3.50/1.58  tff('#skF_3', type, '#skF_3': $i).
% 3.50/1.58  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.50/1.58  tff(v3_tdlat_3, type, v3_tdlat_3: $i > $o).
% 3.50/1.58  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.50/1.58  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.50/1.58  tff('#skF_4', type, '#skF_4': $i).
% 3.50/1.58  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.50/1.58  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.50/1.58  tff(v5_pre_topc, type, v5_pre_topc: ($i * $i * $i) > $o).
% 3.50/1.58  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.50/1.58  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.50/1.58  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.50/1.58  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.50/1.58  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 3.50/1.58  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.50/1.58  
% 3.50/1.60  tff(f_180, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v4_tex_2(B, A)) & m1_pre_topc(B, A)) => (![C]: ((((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & v5_pre_topc(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (v3_borsuk_1(C, A, B) => (![D]: (m1_subset_1(D, u1_struct_0(B)) => (![E]: (m1_subset_1(E, u1_struct_0(A)) => ((D = E) => (k8_relset_1(u1_struct_0(A), u1_struct_0(B), C, k6_domain_1(u1_struct_0(B), D)) = k2_pre_topc(A, k6_domain_1(u1_struct_0(A), E))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_tex_2)).
% 3.50/1.60  tff(f_64, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 3.50/1.60  tff(f_71, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 3.50/1.60  tff(f_88, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (v4_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => v3_tex_2(C, A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_tex_2)).
% 3.50/1.60  tff(f_103, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ~v3_tex_2(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_tex_2)).
% 3.50/1.60  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.50/1.60  tff(f_40, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 3.50/1.60  tff(f_57, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 3.50/1.60  tff(f_141, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v4_tex_2(B, A)) & m1_pre_topc(B, A)) => (![C]: ((((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & v5_pre_topc(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (v3_borsuk_1(C, A, B) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => (![E]: (m1_subset_1(E, k1_zfmisc_1(u1_struct_0(A))) => ((D = E) => (k8_relset_1(u1_struct_0(A), u1_struct_0(B), C, D) = k2_pre_topc(A, E)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t76_tex_2)).
% 3.50/1.60  tff(c_52, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_180])).
% 3.50/1.60  tff(c_60, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_180])).
% 3.50/1.60  tff(c_54, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_180])).
% 3.50/1.60  tff(c_48, plain, (m1_pre_topc('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_180])).
% 3.50/1.60  tff(c_58, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_180])).
% 3.50/1.60  tff(c_50, plain, (v4_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_180])).
% 3.50/1.60  tff(c_36, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_180])).
% 3.50/1.60  tff(c_87, plain, (![A_100, B_101]: (k6_domain_1(A_100, B_101)=k1_tarski(B_101) | ~m1_subset_1(B_101, A_100) | v1_xboole_0(A_100))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.50/1.60  tff(c_99, plain, (k6_domain_1(u1_struct_0('#skF_4'), '#skF_6')=k1_tarski('#skF_6') | v1_xboole_0(u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_36, c_87])).
% 3.50/1.60  tff(c_314, plain, (v1_xboole_0(u1_struct_0('#skF_4'))), inference(splitLeft, [status(thm)], [c_99])).
% 3.50/1.60  tff(c_16, plain, (![B_22, A_20]: (m1_subset_1(u1_struct_0(B_22), k1_zfmisc_1(u1_struct_0(A_20))) | ~m1_pre_topc(B_22, A_20) | ~l1_pre_topc(A_20))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.50/1.60  tff(c_497, plain, (![B_191, A_192]: (v3_tex_2(u1_struct_0(B_191), A_192) | ~m1_subset_1(u1_struct_0(B_191), k1_zfmisc_1(u1_struct_0(A_192))) | ~v4_tex_2(B_191, A_192) | ~m1_pre_topc(B_191, A_192) | ~l1_pre_topc(A_192) | v2_struct_0(A_192))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.50/1.60  tff(c_502, plain, (![B_193, A_194]: (v3_tex_2(u1_struct_0(B_193), A_194) | ~v4_tex_2(B_193, A_194) | v2_struct_0(A_194) | ~m1_pre_topc(B_193, A_194) | ~l1_pre_topc(A_194))), inference(resolution, [status(thm)], [c_16, c_497])).
% 3.50/1.60  tff(c_382, plain, (![B_170, A_171]: (~v3_tex_2(B_170, A_171) | ~m1_subset_1(B_170, k1_zfmisc_1(u1_struct_0(A_171))) | ~v1_xboole_0(B_170) | ~l1_pre_topc(A_171) | ~v2_pre_topc(A_171) | v2_struct_0(A_171))), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.50/1.60  tff(c_397, plain, (![B_22, A_20]: (~v3_tex_2(u1_struct_0(B_22), A_20) | ~v1_xboole_0(u1_struct_0(B_22)) | ~v2_pre_topc(A_20) | v2_struct_0(A_20) | ~m1_pre_topc(B_22, A_20) | ~l1_pre_topc(A_20))), inference(resolution, [status(thm)], [c_16, c_382])).
% 3.50/1.60  tff(c_507, plain, (![B_195, A_196]: (~v1_xboole_0(u1_struct_0(B_195)) | ~v2_pre_topc(A_196) | ~v4_tex_2(B_195, A_196) | v2_struct_0(A_196) | ~m1_pre_topc(B_195, A_196) | ~l1_pre_topc(A_196))), inference(resolution, [status(thm)], [c_502, c_397])).
% 3.50/1.60  tff(c_511, plain, (![A_197]: (~v2_pre_topc(A_197) | ~v4_tex_2('#skF_4', A_197) | v2_struct_0(A_197) | ~m1_pre_topc('#skF_4', A_197) | ~l1_pre_topc(A_197))), inference(resolution, [status(thm)], [c_314, c_507])).
% 3.50/1.60  tff(c_518, plain, (~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_50, c_511])).
% 3.50/1.60  tff(c_522, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_48, c_58, c_518])).
% 3.50/1.60  tff(c_524, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_522])).
% 3.50/1.60  tff(c_525, plain, (k6_domain_1(u1_struct_0('#skF_4'), '#skF_6')=k1_tarski('#skF_6')), inference(splitRight, [status(thm)], [c_99])).
% 3.50/1.60  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.50/1.60  tff(c_32, plain, ('#skF_7'='#skF_6'), inference(cnfTransformation, [status(thm)], [f_180])).
% 3.50/1.60  tff(c_34, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_180])).
% 3.50/1.60  tff(c_61, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_34])).
% 3.50/1.60  tff(c_98, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_6')=k1_tarski('#skF_6') | v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_61, c_87])).
% 3.50/1.60  tff(c_100, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_98])).
% 3.50/1.60  tff(c_254, plain, (![B_142, A_143]: (m1_subset_1(u1_struct_0(B_142), k1_zfmisc_1(u1_struct_0(A_143))) | ~m1_pre_topc(B_142, A_143) | ~l1_pre_topc(A_143))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.50/1.60  tff(c_8, plain, (![C_8, B_7, A_6]: (~v1_xboole_0(C_8) | ~m1_subset_1(B_7, k1_zfmisc_1(C_8)) | ~r2_hidden(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.50/1.60  tff(c_284, plain, (![A_148, A_149, B_150]: (~v1_xboole_0(u1_struct_0(A_148)) | ~r2_hidden(A_149, u1_struct_0(B_150)) | ~m1_pre_topc(B_150, A_148) | ~l1_pre_topc(A_148))), inference(resolution, [status(thm)], [c_254, c_8])).
% 3.50/1.60  tff(c_286, plain, (![A_149, B_150]: (~r2_hidden(A_149, u1_struct_0(B_150)) | ~m1_pre_topc(B_150, '#skF_3') | ~l1_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_100, c_284])).
% 3.50/1.60  tff(c_290, plain, (![A_151, B_152]: (~r2_hidden(A_151, u1_struct_0(B_152)) | ~m1_pre_topc(B_152, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_286])).
% 3.50/1.60  tff(c_297, plain, (![B_153]: (~m1_pre_topc(B_153, '#skF_3') | v1_xboole_0(u1_struct_0(B_153)))), inference(resolution, [status(thm)], [c_4, c_290])).
% 3.50/1.60  tff(c_101, plain, (v1_xboole_0(u1_struct_0('#skF_4'))), inference(splitLeft, [status(thm)], [c_99])).
% 3.50/1.60  tff(c_192, plain, (![B_133, A_134]: (v3_tex_2(u1_struct_0(B_133), A_134) | ~m1_subset_1(u1_struct_0(B_133), k1_zfmisc_1(u1_struct_0(A_134))) | ~v4_tex_2(B_133, A_134) | ~m1_pre_topc(B_133, A_134) | ~l1_pre_topc(A_134) | v2_struct_0(A_134))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.50/1.60  tff(c_197, plain, (![B_135, A_136]: (v3_tex_2(u1_struct_0(B_135), A_136) | ~v4_tex_2(B_135, A_136) | v2_struct_0(A_136) | ~m1_pre_topc(B_135, A_136) | ~l1_pre_topc(A_136))), inference(resolution, [status(thm)], [c_16, c_192])).
% 3.50/1.60  tff(c_160, plain, (![B_124, A_125]: (~v3_tex_2(B_124, A_125) | ~m1_subset_1(B_124, k1_zfmisc_1(u1_struct_0(A_125))) | ~v1_xboole_0(B_124) | ~l1_pre_topc(A_125) | ~v2_pre_topc(A_125) | v2_struct_0(A_125))), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.50/1.60  tff(c_168, plain, (![B_22, A_20]: (~v3_tex_2(u1_struct_0(B_22), A_20) | ~v1_xboole_0(u1_struct_0(B_22)) | ~v2_pre_topc(A_20) | v2_struct_0(A_20) | ~m1_pre_topc(B_22, A_20) | ~l1_pre_topc(A_20))), inference(resolution, [status(thm)], [c_16, c_160])).
% 3.50/1.60  tff(c_202, plain, (![B_137, A_138]: (~v1_xboole_0(u1_struct_0(B_137)) | ~v2_pre_topc(A_138) | ~v4_tex_2(B_137, A_138) | v2_struct_0(A_138) | ~m1_pre_topc(B_137, A_138) | ~l1_pre_topc(A_138))), inference(resolution, [status(thm)], [c_197, c_168])).
% 3.50/1.60  tff(c_212, plain, (![A_139]: (~v2_pre_topc(A_139) | ~v4_tex_2('#skF_4', A_139) | v2_struct_0(A_139) | ~m1_pre_topc('#skF_4', A_139) | ~l1_pre_topc(A_139))), inference(resolution, [status(thm)], [c_101, c_202])).
% 3.50/1.60  tff(c_219, plain, (~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_50, c_212])).
% 3.50/1.60  tff(c_223, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_48, c_58, c_219])).
% 3.50/1.60  tff(c_225, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_223])).
% 3.50/1.60  tff(c_227, plain, (~v1_xboole_0(u1_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_99])).
% 3.50/1.60  tff(c_302, plain, (~m1_pre_topc('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_297, c_227])).
% 3.50/1.60  tff(c_307, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_302])).
% 3.50/1.60  tff(c_308, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_6')=k1_tarski('#skF_6')), inference(splitRight, [status(thm)], [c_98])).
% 3.50/1.60  tff(c_30, plain, (k8_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5', k6_domain_1(u1_struct_0('#skF_4'), '#skF_6'))!=k2_pre_topc('#skF_3', k6_domain_1(u1_struct_0('#skF_3'), '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_180])).
% 3.50/1.60  tff(c_62, plain, (k8_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5', k6_domain_1(u1_struct_0('#skF_4'), '#skF_6'))!=k2_pre_topc('#skF_3', k6_domain_1(u1_struct_0('#skF_3'), '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30])).
% 3.50/1.60  tff(c_527, plain, (k8_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5', k6_domain_1(u1_struct_0('#skF_4'), '#skF_6'))!=k2_pre_topc('#skF_3', k1_tarski('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_308, c_62])).
% 3.50/1.60  tff(c_528, plain, (k8_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5', k1_tarski('#skF_6'))!=k2_pre_topc('#skF_3', k1_tarski('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_525, c_527])).
% 3.50/1.60  tff(c_46, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_180])).
% 3.50/1.60  tff(c_44, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_180])).
% 3.50/1.60  tff(c_42, plain, (v5_pre_topc('#skF_5', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_180])).
% 3.50/1.60  tff(c_38, plain, (v3_borsuk_1('#skF_5', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_180])).
% 3.50/1.60  tff(c_526, plain, (~v1_xboole_0(u1_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_99])).
% 3.50/1.60  tff(c_533, plain, (![A_198, B_199]: (m1_subset_1(k6_domain_1(A_198, B_199), k1_zfmisc_1(A_198)) | ~m1_subset_1(B_199, A_198) | v1_xboole_0(A_198))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.50/1.60  tff(c_541, plain, (m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_4')) | v1_xboole_0(u1_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_525, c_533])).
% 3.50/1.60  tff(c_548, plain, (m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | v1_xboole_0(u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_541])).
% 3.50/1.60  tff(c_549, plain, (m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_526, c_548])).
% 3.50/1.60  tff(c_40, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_180])).
% 3.50/1.60  tff(c_56, plain, (v3_tdlat_3('#skF_3')), inference(cnfTransformation, [status(thm)], [f_180])).
% 3.50/1.60  tff(c_309, plain, (~v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_98])).
% 3.50/1.60  tff(c_544, plain, (m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_3')) | v1_xboole_0(u1_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_308, c_533])).
% 3.50/1.60  tff(c_551, plain, (m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | v1_xboole_0(u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_61, c_544])).
% 3.50/1.60  tff(c_552, plain, (m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_309, c_551])).
% 3.50/1.60  tff(c_789, plain, (![A_246, B_247, C_248, E_249]: (k8_relset_1(u1_struct_0(A_246), u1_struct_0(B_247), C_248, E_249)=k2_pre_topc(A_246, E_249) | ~m1_subset_1(E_249, k1_zfmisc_1(u1_struct_0(A_246))) | ~m1_subset_1(E_249, k1_zfmisc_1(u1_struct_0(B_247))) | ~v3_borsuk_1(C_248, A_246, B_247) | ~m1_subset_1(C_248, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_246), u1_struct_0(B_247)))) | ~v5_pre_topc(C_248, A_246, B_247) | ~v1_funct_2(C_248, u1_struct_0(A_246), u1_struct_0(B_247)) | ~v1_funct_1(C_248) | ~m1_pre_topc(B_247, A_246) | ~v4_tex_2(B_247, A_246) | v2_struct_0(B_247) | ~l1_pre_topc(A_246) | ~v3_tdlat_3(A_246) | ~v2_pre_topc(A_246) | v2_struct_0(A_246))), inference(cnfTransformation, [status(thm)], [f_141])).
% 3.50/1.60  tff(c_799, plain, (![B_247, C_248]: (k8_relset_1(u1_struct_0('#skF_3'), u1_struct_0(B_247), C_248, k1_tarski('#skF_6'))=k2_pre_topc('#skF_3', k1_tarski('#skF_6')) | ~m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0(B_247))) | ~v3_borsuk_1(C_248, '#skF_3', B_247) | ~m1_subset_1(C_248, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_247)))) | ~v5_pre_topc(C_248, '#skF_3', B_247) | ~v1_funct_2(C_248, u1_struct_0('#skF_3'), u1_struct_0(B_247)) | ~v1_funct_1(C_248) | ~m1_pre_topc(B_247, '#skF_3') | ~v4_tex_2(B_247, '#skF_3') | v2_struct_0(B_247) | ~l1_pre_topc('#skF_3') | ~v3_tdlat_3('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_552, c_789])).
% 3.50/1.60  tff(c_811, plain, (![B_247, C_248]: (k8_relset_1(u1_struct_0('#skF_3'), u1_struct_0(B_247), C_248, k1_tarski('#skF_6'))=k2_pre_topc('#skF_3', k1_tarski('#skF_6')) | ~m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0(B_247))) | ~v3_borsuk_1(C_248, '#skF_3', B_247) | ~m1_subset_1(C_248, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_247)))) | ~v5_pre_topc(C_248, '#skF_3', B_247) | ~v1_funct_2(C_248, u1_struct_0('#skF_3'), u1_struct_0(B_247)) | ~v1_funct_1(C_248) | ~m1_pre_topc(B_247, '#skF_3') | ~v4_tex_2(B_247, '#skF_3') | v2_struct_0(B_247) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_799])).
% 3.50/1.60  tff(c_865, plain, (![B_260, C_261]: (k8_relset_1(u1_struct_0('#skF_3'), u1_struct_0(B_260), C_261, k1_tarski('#skF_6'))=k2_pre_topc('#skF_3', k1_tarski('#skF_6')) | ~m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0(B_260))) | ~v3_borsuk_1(C_261, '#skF_3', B_260) | ~m1_subset_1(C_261, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_260)))) | ~v5_pre_topc(C_261, '#skF_3', B_260) | ~v1_funct_2(C_261, u1_struct_0('#skF_3'), u1_struct_0(B_260)) | ~v1_funct_1(C_261) | ~m1_pre_topc(B_260, '#skF_3') | ~v4_tex_2(B_260, '#skF_3') | v2_struct_0(B_260))), inference(negUnitSimplification, [status(thm)], [c_60, c_811])).
% 3.50/1.60  tff(c_872, plain, (k8_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5', k1_tarski('#skF_6'))=k2_pre_topc('#skF_3', k1_tarski('#skF_6')) | ~m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~v3_borsuk_1('#skF_5', '#skF_3', '#skF_4') | ~v5_pre_topc('#skF_5', '#skF_3', '#skF_4') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_4')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_3') | ~v4_tex_2('#skF_4', '#skF_3') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_40, c_865])).
% 3.50/1.60  tff(c_876, plain, (k8_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5', k1_tarski('#skF_6'))=k2_pre_topc('#skF_3', k1_tarski('#skF_6')) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_44, c_42, c_38, c_549, c_872])).
% 3.50/1.60  tff(c_878, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_528, c_876])).
% 3.50/1.60  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.50/1.60  
% 3.50/1.60  Inference rules
% 3.50/1.60  ----------------------
% 3.50/1.60  #Ref     : 0
% 3.50/1.60  #Sup     : 182
% 3.50/1.60  #Fact    : 0
% 3.50/1.60  #Define  : 0
% 3.50/1.60  #Split   : 19
% 3.50/1.60  #Chain   : 0
% 3.50/1.60  #Close   : 0
% 3.50/1.60  
% 3.50/1.60  Ordering : KBO
% 3.50/1.60  
% 3.50/1.60  Simplification rules
% 3.50/1.60  ----------------------
% 3.50/1.60  #Subsume      : 24
% 3.50/1.60  #Demod        : 55
% 3.50/1.60  #Tautology    : 35
% 3.50/1.60  #SimpNegUnit  : 18
% 3.50/1.60  #BackRed      : 2
% 3.50/1.60  
% 3.50/1.60  #Partial instantiations: 0
% 3.50/1.60  #Strategies tried      : 1
% 3.50/1.60  
% 3.50/1.60  Timing (in seconds)
% 3.50/1.60  ----------------------
% 3.50/1.60  Preprocessing        : 0.37
% 3.50/1.60  Parsing              : 0.20
% 3.50/1.60  CNF conversion       : 0.03
% 3.50/1.60  Main loop            : 0.44
% 3.50/1.60  Inferencing          : 0.16
% 3.50/1.60  Reduction            : 0.13
% 3.50/1.60  Demodulation         : 0.09
% 3.50/1.60  BG Simplification    : 0.02
% 3.50/1.60  Subsumption          : 0.09
% 3.50/1.60  Abstraction          : 0.02
% 3.50/1.60  MUC search           : 0.00
% 3.50/1.60  Cooper               : 0.00
% 3.50/1.60  Total                : 0.85
% 3.50/1.60  Index Insertion      : 0.00
% 3.50/1.60  Index Deletion       : 0.00
% 3.50/1.60  Index Matching       : 0.00
% 3.50/1.60  BG Taut test         : 0.00
%------------------------------------------------------------------------------
