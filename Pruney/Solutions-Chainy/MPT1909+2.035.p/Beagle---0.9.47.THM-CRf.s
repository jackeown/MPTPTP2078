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
% DateTime   : Thu Dec  3 10:30:42 EST 2020

% Result     : Theorem 3.03s
% Output     : CNFRefutation 3.27s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 172 expanded)
%              Number of leaves         :   43 (  81 expanded)
%              Depth                    :   15
%              Number of atoms          :  251 ( 823 expanded)
%              Number of equality atoms :   24 ( 103 expanded)
%              Maximal formula depth    :   20 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_pre_topc > v3_borsuk_1 > v1_funct_2 > v4_tex_2 > v3_tex_2 > r2_hidden > m1_subset_1 > m1_pre_topc > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k8_relset_1 > k6_domain_1 > k2_zfmisc_1 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

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

tff(f_182,negated_conjecture,(
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

tff(f_66,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_73,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_90,axiom,(
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

tff(f_105,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( v1_xboole_0(B)
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
         => ~ v3_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_tex_2)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(k1_tarski(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).

tff(f_59,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(B)))
             => m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_pre_topc)).

tff(f_143,axiom,(
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

tff(f_41,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_49,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(c_60,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_54,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_48,plain,(
    m1_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_58,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_50,plain,(
    v4_tex_2('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_32,plain,(
    '#skF_5' = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_36,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_61,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_36])).

tff(c_80,plain,(
    ! [A_97,B_98] :
      ( k6_domain_1(A_97,B_98) = k1_tarski(B_98)
      | ~ m1_subset_1(B_98,A_97)
      | v1_xboole_0(A_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_95,plain,
    ( k6_domain_1(u1_struct_0('#skF_3'),'#skF_6') = k1_tarski('#skF_6')
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_61,c_80])).

tff(c_97,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_95])).

tff(c_16,plain,(
    ! [B_19,A_17] :
      ( m1_subset_1(u1_struct_0(B_19),k1_zfmisc_1(u1_struct_0(A_17)))
      | ~ m1_pre_topc(B_19,A_17)
      | ~ l1_pre_topc(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_228,plain,(
    ! [B_130,A_131] :
      ( v3_tex_2(u1_struct_0(B_130),A_131)
      | ~ m1_subset_1(u1_struct_0(B_130),k1_zfmisc_1(u1_struct_0(A_131)))
      | ~ v4_tex_2(B_130,A_131)
      | ~ m1_pre_topc(B_130,A_131)
      | ~ l1_pre_topc(A_131)
      | v2_struct_0(A_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_233,plain,(
    ! [B_132,A_133] :
      ( v3_tex_2(u1_struct_0(B_132),A_133)
      | ~ v4_tex_2(B_132,A_133)
      | v2_struct_0(A_133)
      | ~ m1_pre_topc(B_132,A_133)
      | ~ l1_pre_topc(A_133) ) ),
    inference(resolution,[status(thm)],[c_16,c_228])).

tff(c_176,plain,(
    ! [B_116,A_117] :
      ( ~ v3_tex_2(B_116,A_117)
      | ~ m1_subset_1(B_116,k1_zfmisc_1(u1_struct_0(A_117)))
      | ~ v1_xboole_0(B_116)
      | ~ l1_pre_topc(A_117)
      | ~ v2_pre_topc(A_117)
      | v2_struct_0(A_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_195,plain,(
    ! [B_19,A_17] :
      ( ~ v3_tex_2(u1_struct_0(B_19),A_17)
      | ~ v1_xboole_0(u1_struct_0(B_19))
      | ~ v2_pre_topc(A_17)
      | v2_struct_0(A_17)
      | ~ m1_pre_topc(B_19,A_17)
      | ~ l1_pre_topc(A_17) ) ),
    inference(resolution,[status(thm)],[c_16,c_176])).

tff(c_238,plain,(
    ! [B_134,A_135] :
      ( ~ v1_xboole_0(u1_struct_0(B_134))
      | ~ v2_pre_topc(A_135)
      | ~ v4_tex_2(B_134,A_135)
      | v2_struct_0(A_135)
      | ~ m1_pre_topc(B_134,A_135)
      | ~ l1_pre_topc(A_135) ) ),
    inference(resolution,[status(thm)],[c_233,c_195])).

tff(c_242,plain,(
    ! [A_136] :
      ( ~ v2_pre_topc(A_136)
      | ~ v4_tex_2('#skF_3',A_136)
      | v2_struct_0(A_136)
      | ~ m1_pre_topc('#skF_3',A_136)
      | ~ l1_pre_topc(A_136) ) ),
    inference(resolution,[status(thm)],[c_97,c_238])).

tff(c_249,plain,
    ( ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_242])).

tff(c_253,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_48,c_58,c_249])).

tff(c_255,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_253])).

tff(c_257,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_95])).

tff(c_6,plain,(
    ! [A_4,B_5] :
      ( r2_hidden(A_4,B_5)
      | v1_xboole_0(B_5)
      | ~ m1_subset_1(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_52,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_46,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_44,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_42,plain,(
    v5_pre_topc('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_38,plain,(
    v3_borsuk_1('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_40,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_4,plain,(
    ! [A_2,B_3] :
      ( m1_subset_1(k1_tarski(A_2),k1_zfmisc_1(B_3))
      | ~ r2_hidden(A_2,B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_56,plain,(
    v3_tdlat_3('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_301,plain,(
    ! [C_145,A_146,B_147] :
      ( m1_subset_1(C_145,k1_zfmisc_1(u1_struct_0(A_146)))
      | ~ m1_subset_1(C_145,k1_zfmisc_1(u1_struct_0(B_147)))
      | ~ m1_pre_topc(B_147,A_146)
      | ~ l1_pre_topc(A_146) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_310,plain,(
    ! [A_148,A_149,B_150] :
      ( m1_subset_1(k1_tarski(A_148),k1_zfmisc_1(u1_struct_0(A_149)))
      | ~ m1_pre_topc(B_150,A_149)
      | ~ l1_pre_topc(A_149)
      | ~ r2_hidden(A_148,u1_struct_0(B_150)) ) ),
    inference(resolution,[status(thm)],[c_4,c_301])).

tff(c_312,plain,(
    ! [A_148] :
      ( m1_subset_1(k1_tarski(A_148),k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ r2_hidden(A_148,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_48,c_310])).

tff(c_315,plain,(
    ! [A_148] :
      ( m1_subset_1(k1_tarski(A_148),k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ r2_hidden(A_148,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_312])).

tff(c_449,plain,(
    ! [A_193,B_194,C_195,E_196] :
      ( k8_relset_1(u1_struct_0(A_193),u1_struct_0(B_194),C_195,E_196) = k2_pre_topc(A_193,E_196)
      | ~ m1_subset_1(E_196,k1_zfmisc_1(u1_struct_0(A_193)))
      | ~ m1_subset_1(E_196,k1_zfmisc_1(u1_struct_0(B_194)))
      | ~ v3_borsuk_1(C_195,A_193,B_194)
      | ~ m1_subset_1(C_195,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_193),u1_struct_0(B_194))))
      | ~ v5_pre_topc(C_195,A_193,B_194)
      | ~ v1_funct_2(C_195,u1_struct_0(A_193),u1_struct_0(B_194))
      | ~ v1_funct_1(C_195)
      | ~ m1_pre_topc(B_194,A_193)
      | ~ v4_tex_2(B_194,A_193)
      | v2_struct_0(B_194)
      | ~ l1_pre_topc(A_193)
      | ~ v3_tdlat_3(A_193)
      | ~ v2_pre_topc(A_193)
      | v2_struct_0(A_193) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_457,plain,(
    ! [B_194,C_195,A_148] :
      ( k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0(B_194),C_195,k1_tarski(A_148)) = k2_pre_topc('#skF_2',k1_tarski(A_148))
      | ~ m1_subset_1(k1_tarski(A_148),k1_zfmisc_1(u1_struct_0(B_194)))
      | ~ v3_borsuk_1(C_195,'#skF_2',B_194)
      | ~ m1_subset_1(C_195,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0(B_194))))
      | ~ v5_pre_topc(C_195,'#skF_2',B_194)
      | ~ v1_funct_2(C_195,u1_struct_0('#skF_2'),u1_struct_0(B_194))
      | ~ v1_funct_1(C_195)
      | ~ m1_pre_topc(B_194,'#skF_2')
      | ~ v4_tex_2(B_194,'#skF_2')
      | v2_struct_0(B_194)
      | ~ l1_pre_topc('#skF_2')
      | ~ v3_tdlat_3('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ r2_hidden(A_148,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_315,c_449])).

tff(c_468,plain,(
    ! [B_194,C_195,A_148] :
      ( k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0(B_194),C_195,k1_tarski(A_148)) = k2_pre_topc('#skF_2',k1_tarski(A_148))
      | ~ m1_subset_1(k1_tarski(A_148),k1_zfmisc_1(u1_struct_0(B_194)))
      | ~ v3_borsuk_1(C_195,'#skF_2',B_194)
      | ~ m1_subset_1(C_195,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0(B_194))))
      | ~ v5_pre_topc(C_195,'#skF_2',B_194)
      | ~ v1_funct_2(C_195,u1_struct_0('#skF_2'),u1_struct_0(B_194))
      | ~ v1_funct_1(C_195)
      | ~ m1_pre_topc(B_194,'#skF_2')
      | ~ v4_tex_2(B_194,'#skF_2')
      | v2_struct_0(B_194)
      | v2_struct_0('#skF_2')
      | ~ r2_hidden(A_148,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_457])).

tff(c_490,plain,(
    ! [B_200,C_201,A_202] :
      ( k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0(B_200),C_201,k1_tarski(A_202)) = k2_pre_topc('#skF_2',k1_tarski(A_202))
      | ~ m1_subset_1(k1_tarski(A_202),k1_zfmisc_1(u1_struct_0(B_200)))
      | ~ v3_borsuk_1(C_201,'#skF_2',B_200)
      | ~ m1_subset_1(C_201,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0(B_200))))
      | ~ v5_pre_topc(C_201,'#skF_2',B_200)
      | ~ v1_funct_2(C_201,u1_struct_0('#skF_2'),u1_struct_0(B_200))
      | ~ v1_funct_1(C_201)
      | ~ m1_pre_topc(B_200,'#skF_2')
      | ~ v4_tex_2(B_200,'#skF_2')
      | v2_struct_0(B_200)
      | ~ r2_hidden(A_202,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_468])).

tff(c_512,plain,(
    ! [B_203,C_204,A_205] :
      ( k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0(B_203),C_204,k1_tarski(A_205)) = k2_pre_topc('#skF_2',k1_tarski(A_205))
      | ~ v3_borsuk_1(C_204,'#skF_2',B_203)
      | ~ m1_subset_1(C_204,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0(B_203))))
      | ~ v5_pre_topc(C_204,'#skF_2',B_203)
      | ~ v1_funct_2(C_204,u1_struct_0('#skF_2'),u1_struct_0(B_203))
      | ~ v1_funct_1(C_204)
      | ~ m1_pre_topc(B_203,'#skF_2')
      | ~ v4_tex_2(B_203,'#skF_2')
      | v2_struct_0(B_203)
      | ~ r2_hidden(A_205,u1_struct_0('#skF_3'))
      | ~ r2_hidden(A_205,u1_struct_0(B_203)) ) ),
    inference(resolution,[status(thm)],[c_4,c_490])).

tff(c_517,plain,(
    ! [A_205] :
      ( k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4',k1_tarski(A_205)) = k2_pre_topc('#skF_2',k1_tarski(A_205))
      | ~ v3_borsuk_1('#skF_4','#skF_2','#skF_3')
      | ~ v5_pre_topc('#skF_4','#skF_2','#skF_3')
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_4')
      | ~ m1_pre_topc('#skF_3','#skF_2')
      | ~ v4_tex_2('#skF_3','#skF_2')
      | v2_struct_0('#skF_3')
      | ~ r2_hidden(A_205,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_40,c_512])).

tff(c_521,plain,(
    ! [A_205] :
      ( k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4',k1_tarski(A_205)) = k2_pre_topc('#skF_2',k1_tarski(A_205))
      | v2_struct_0('#skF_3')
      | ~ r2_hidden(A_205,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_42,c_38,c_517])).

tff(c_523,plain,(
    ! [A_206] :
      ( k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4',k1_tarski(A_206)) = k2_pre_topc('#skF_2',k1_tarski(A_206))
      | ~ r2_hidden(A_206,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_521])).

tff(c_8,plain,(
    ! [A_6] :
      ( l1_struct_0(A_6)
      | ~ l1_pre_topc(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_34,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_96,plain,
    ( k6_domain_1(u1_struct_0('#skF_2'),'#skF_6') = k1_tarski('#skF_6')
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_34,c_80])).

tff(c_268,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_96])).

tff(c_10,plain,(
    ! [A_7] :
      ( ~ v1_xboole_0(u1_struct_0(A_7))
      | ~ l1_struct_0(A_7)
      | v2_struct_0(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_272,plain,
    ( ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_268,c_10])).

tff(c_275,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_272])).

tff(c_278,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_8,c_275])).

tff(c_282,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_278])).

tff(c_283,plain,(
    k6_domain_1(u1_struct_0('#skF_2'),'#skF_6') = k1_tarski('#skF_6') ),
    inference(splitRight,[status(thm)],[c_96])).

tff(c_256,plain,(
    k6_domain_1(u1_struct_0('#skF_3'),'#skF_6') = k1_tarski('#skF_6') ),
    inference(splitRight,[status(thm)],[c_95])).

tff(c_30,plain,(
    k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4',k6_domain_1(u1_struct_0('#skF_3'),'#skF_5')) != k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_62,plain,(
    k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4',k6_domain_1(u1_struct_0('#skF_3'),'#skF_6')) != k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30])).

tff(c_263,plain,(
    k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4',k1_tarski('#skF_6')) != k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_256,c_62])).

tff(c_289,plain,(
    k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4',k1_tarski('#skF_6')) != k2_pre_topc('#skF_2',k1_tarski('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_283,c_263])).

tff(c_534,plain,(
    ~ r2_hidden('#skF_6',u1_struct_0('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_523,c_289])).

tff(c_538,plain,
    ( v1_xboole_0(u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_6,c_534])).

tff(c_541,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_538])).

tff(c_543,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_257,c_541])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n018.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 12:22:56 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.03/1.51  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.03/1.52  
% 3.03/1.52  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.27/1.52  %$ v5_pre_topc > v3_borsuk_1 > v1_funct_2 > v4_tex_2 > v3_tex_2 > r2_hidden > m1_subset_1 > m1_pre_topc > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k8_relset_1 > k6_domain_1 > k2_zfmisc_1 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 3.27/1.52  
% 3.27/1.52  %Foreground sorts:
% 3.27/1.52  
% 3.27/1.52  
% 3.27/1.52  %Background operators:
% 3.27/1.52  
% 3.27/1.52  
% 3.27/1.52  %Foreground operators:
% 3.27/1.52  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.27/1.52  tff(v3_borsuk_1, type, v3_borsuk_1: ($i * $i * $i) > $o).
% 3.27/1.52  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.27/1.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.27/1.52  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.27/1.52  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.27/1.52  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 3.27/1.52  tff(v4_tex_2, type, v4_tex_2: ($i * $i) > $o).
% 3.27/1.52  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.27/1.52  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 3.27/1.52  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.27/1.52  tff('#skF_5', type, '#skF_5': $i).
% 3.27/1.52  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 3.27/1.52  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.27/1.52  tff('#skF_6', type, '#skF_6': $i).
% 3.27/1.52  tff('#skF_2', type, '#skF_2': $i).
% 3.27/1.52  tff('#skF_3', type, '#skF_3': $i).
% 3.27/1.52  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.27/1.52  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.27/1.52  tff(v3_tdlat_3, type, v3_tdlat_3: $i > $o).
% 3.27/1.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.27/1.52  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.27/1.52  tff('#skF_4', type, '#skF_4': $i).
% 3.27/1.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.27/1.52  tff(v5_pre_topc, type, v5_pre_topc: ($i * $i * $i) > $o).
% 3.27/1.52  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.27/1.52  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.27/1.52  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.27/1.52  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.27/1.52  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.27/1.52  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 3.27/1.52  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.27/1.52  
% 3.27/1.54  tff(f_182, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v4_tex_2(B, A)) & m1_pre_topc(B, A)) => (![C]: ((((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & v5_pre_topc(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (v3_borsuk_1(C, A, B) => (![D]: (m1_subset_1(D, u1_struct_0(B)) => (![E]: (m1_subset_1(E, u1_struct_0(A)) => ((D = E) => (k8_relset_1(u1_struct_0(A), u1_struct_0(B), C, k6_domain_1(u1_struct_0(B), D)) = k2_pre_topc(A, k6_domain_1(u1_struct_0(A), E))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_tex_2)).
% 3.27/1.54  tff(f_66, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 3.27/1.54  tff(f_73, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 3.27/1.54  tff(f_90, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (v4_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => v3_tex_2(C, A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_tex_2)).
% 3.27/1.54  tff(f_105, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ~v3_tex_2(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_tex_2)).
% 3.27/1.54  tff(f_37, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 3.27/1.54  tff(f_31, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(k1_tarski(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_subset_1)).
% 3.27/1.54  tff(f_59, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B))) => m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_pre_topc)).
% 3.27/1.54  tff(f_143, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v4_tex_2(B, A)) & m1_pre_topc(B, A)) => (![C]: ((((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & v5_pre_topc(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (v3_borsuk_1(C, A, B) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => (![E]: (m1_subset_1(E, k1_zfmisc_1(u1_struct_0(A))) => ((D = E) => (k8_relset_1(u1_struct_0(A), u1_struct_0(B), C, D) = k2_pre_topc(A, E)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t76_tex_2)).
% 3.27/1.54  tff(f_41, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.27/1.54  tff(f_49, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 3.27/1.54  tff(c_60, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_182])).
% 3.27/1.54  tff(c_54, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_182])).
% 3.27/1.54  tff(c_48, plain, (m1_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_182])).
% 3.27/1.54  tff(c_58, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_182])).
% 3.27/1.54  tff(c_50, plain, (v4_tex_2('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_182])).
% 3.27/1.54  tff(c_32, plain, ('#skF_5'='#skF_6'), inference(cnfTransformation, [status(thm)], [f_182])).
% 3.27/1.54  tff(c_36, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_182])).
% 3.27/1.54  tff(c_61, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_36])).
% 3.27/1.54  tff(c_80, plain, (![A_97, B_98]: (k6_domain_1(A_97, B_98)=k1_tarski(B_98) | ~m1_subset_1(B_98, A_97) | v1_xboole_0(A_97))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.27/1.54  tff(c_95, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_6')=k1_tarski('#skF_6') | v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_61, c_80])).
% 3.27/1.54  tff(c_97, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_95])).
% 3.27/1.54  tff(c_16, plain, (![B_19, A_17]: (m1_subset_1(u1_struct_0(B_19), k1_zfmisc_1(u1_struct_0(A_17))) | ~m1_pre_topc(B_19, A_17) | ~l1_pre_topc(A_17))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.27/1.54  tff(c_228, plain, (![B_130, A_131]: (v3_tex_2(u1_struct_0(B_130), A_131) | ~m1_subset_1(u1_struct_0(B_130), k1_zfmisc_1(u1_struct_0(A_131))) | ~v4_tex_2(B_130, A_131) | ~m1_pre_topc(B_130, A_131) | ~l1_pre_topc(A_131) | v2_struct_0(A_131))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.27/1.54  tff(c_233, plain, (![B_132, A_133]: (v3_tex_2(u1_struct_0(B_132), A_133) | ~v4_tex_2(B_132, A_133) | v2_struct_0(A_133) | ~m1_pre_topc(B_132, A_133) | ~l1_pre_topc(A_133))), inference(resolution, [status(thm)], [c_16, c_228])).
% 3.27/1.54  tff(c_176, plain, (![B_116, A_117]: (~v3_tex_2(B_116, A_117) | ~m1_subset_1(B_116, k1_zfmisc_1(u1_struct_0(A_117))) | ~v1_xboole_0(B_116) | ~l1_pre_topc(A_117) | ~v2_pre_topc(A_117) | v2_struct_0(A_117))), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.27/1.54  tff(c_195, plain, (![B_19, A_17]: (~v3_tex_2(u1_struct_0(B_19), A_17) | ~v1_xboole_0(u1_struct_0(B_19)) | ~v2_pre_topc(A_17) | v2_struct_0(A_17) | ~m1_pre_topc(B_19, A_17) | ~l1_pre_topc(A_17))), inference(resolution, [status(thm)], [c_16, c_176])).
% 3.27/1.54  tff(c_238, plain, (![B_134, A_135]: (~v1_xboole_0(u1_struct_0(B_134)) | ~v2_pre_topc(A_135) | ~v4_tex_2(B_134, A_135) | v2_struct_0(A_135) | ~m1_pre_topc(B_134, A_135) | ~l1_pre_topc(A_135))), inference(resolution, [status(thm)], [c_233, c_195])).
% 3.27/1.54  tff(c_242, plain, (![A_136]: (~v2_pre_topc(A_136) | ~v4_tex_2('#skF_3', A_136) | v2_struct_0(A_136) | ~m1_pre_topc('#skF_3', A_136) | ~l1_pre_topc(A_136))), inference(resolution, [status(thm)], [c_97, c_238])).
% 3.27/1.54  tff(c_249, plain, (~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_50, c_242])).
% 3.27/1.54  tff(c_253, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_48, c_58, c_249])).
% 3.27/1.54  tff(c_255, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_253])).
% 3.27/1.54  tff(c_257, plain, (~v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_95])).
% 3.27/1.54  tff(c_6, plain, (![A_4, B_5]: (r2_hidden(A_4, B_5) | v1_xboole_0(B_5) | ~m1_subset_1(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.27/1.54  tff(c_52, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_182])).
% 3.27/1.54  tff(c_46, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_182])).
% 3.27/1.54  tff(c_44, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_182])).
% 3.27/1.54  tff(c_42, plain, (v5_pre_topc('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_182])).
% 3.27/1.54  tff(c_38, plain, (v3_borsuk_1('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_182])).
% 3.27/1.54  tff(c_40, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_182])).
% 3.27/1.54  tff(c_4, plain, (![A_2, B_3]: (m1_subset_1(k1_tarski(A_2), k1_zfmisc_1(B_3)) | ~r2_hidden(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.27/1.54  tff(c_56, plain, (v3_tdlat_3('#skF_2')), inference(cnfTransformation, [status(thm)], [f_182])).
% 3.27/1.54  tff(c_301, plain, (![C_145, A_146, B_147]: (m1_subset_1(C_145, k1_zfmisc_1(u1_struct_0(A_146))) | ~m1_subset_1(C_145, k1_zfmisc_1(u1_struct_0(B_147))) | ~m1_pre_topc(B_147, A_146) | ~l1_pre_topc(A_146))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.27/1.54  tff(c_310, plain, (![A_148, A_149, B_150]: (m1_subset_1(k1_tarski(A_148), k1_zfmisc_1(u1_struct_0(A_149))) | ~m1_pre_topc(B_150, A_149) | ~l1_pre_topc(A_149) | ~r2_hidden(A_148, u1_struct_0(B_150)))), inference(resolution, [status(thm)], [c_4, c_301])).
% 3.27/1.54  tff(c_312, plain, (![A_148]: (m1_subset_1(k1_tarski(A_148), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~r2_hidden(A_148, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_48, c_310])).
% 3.27/1.54  tff(c_315, plain, (![A_148]: (m1_subset_1(k1_tarski(A_148), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~r2_hidden(A_148, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_312])).
% 3.27/1.54  tff(c_449, plain, (![A_193, B_194, C_195, E_196]: (k8_relset_1(u1_struct_0(A_193), u1_struct_0(B_194), C_195, E_196)=k2_pre_topc(A_193, E_196) | ~m1_subset_1(E_196, k1_zfmisc_1(u1_struct_0(A_193))) | ~m1_subset_1(E_196, k1_zfmisc_1(u1_struct_0(B_194))) | ~v3_borsuk_1(C_195, A_193, B_194) | ~m1_subset_1(C_195, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_193), u1_struct_0(B_194)))) | ~v5_pre_topc(C_195, A_193, B_194) | ~v1_funct_2(C_195, u1_struct_0(A_193), u1_struct_0(B_194)) | ~v1_funct_1(C_195) | ~m1_pre_topc(B_194, A_193) | ~v4_tex_2(B_194, A_193) | v2_struct_0(B_194) | ~l1_pre_topc(A_193) | ~v3_tdlat_3(A_193) | ~v2_pre_topc(A_193) | v2_struct_0(A_193))), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.27/1.54  tff(c_457, plain, (![B_194, C_195, A_148]: (k8_relset_1(u1_struct_0('#skF_2'), u1_struct_0(B_194), C_195, k1_tarski(A_148))=k2_pre_topc('#skF_2', k1_tarski(A_148)) | ~m1_subset_1(k1_tarski(A_148), k1_zfmisc_1(u1_struct_0(B_194))) | ~v3_borsuk_1(C_195, '#skF_2', B_194) | ~m1_subset_1(C_195, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0(B_194)))) | ~v5_pre_topc(C_195, '#skF_2', B_194) | ~v1_funct_2(C_195, u1_struct_0('#skF_2'), u1_struct_0(B_194)) | ~v1_funct_1(C_195) | ~m1_pre_topc(B_194, '#skF_2') | ~v4_tex_2(B_194, '#skF_2') | v2_struct_0(B_194) | ~l1_pre_topc('#skF_2') | ~v3_tdlat_3('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~r2_hidden(A_148, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_315, c_449])).
% 3.27/1.54  tff(c_468, plain, (![B_194, C_195, A_148]: (k8_relset_1(u1_struct_0('#skF_2'), u1_struct_0(B_194), C_195, k1_tarski(A_148))=k2_pre_topc('#skF_2', k1_tarski(A_148)) | ~m1_subset_1(k1_tarski(A_148), k1_zfmisc_1(u1_struct_0(B_194))) | ~v3_borsuk_1(C_195, '#skF_2', B_194) | ~m1_subset_1(C_195, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0(B_194)))) | ~v5_pre_topc(C_195, '#skF_2', B_194) | ~v1_funct_2(C_195, u1_struct_0('#skF_2'), u1_struct_0(B_194)) | ~v1_funct_1(C_195) | ~m1_pre_topc(B_194, '#skF_2') | ~v4_tex_2(B_194, '#skF_2') | v2_struct_0(B_194) | v2_struct_0('#skF_2') | ~r2_hidden(A_148, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_457])).
% 3.27/1.54  tff(c_490, plain, (![B_200, C_201, A_202]: (k8_relset_1(u1_struct_0('#skF_2'), u1_struct_0(B_200), C_201, k1_tarski(A_202))=k2_pre_topc('#skF_2', k1_tarski(A_202)) | ~m1_subset_1(k1_tarski(A_202), k1_zfmisc_1(u1_struct_0(B_200))) | ~v3_borsuk_1(C_201, '#skF_2', B_200) | ~m1_subset_1(C_201, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0(B_200)))) | ~v5_pre_topc(C_201, '#skF_2', B_200) | ~v1_funct_2(C_201, u1_struct_0('#skF_2'), u1_struct_0(B_200)) | ~v1_funct_1(C_201) | ~m1_pre_topc(B_200, '#skF_2') | ~v4_tex_2(B_200, '#skF_2') | v2_struct_0(B_200) | ~r2_hidden(A_202, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_60, c_468])).
% 3.27/1.54  tff(c_512, plain, (![B_203, C_204, A_205]: (k8_relset_1(u1_struct_0('#skF_2'), u1_struct_0(B_203), C_204, k1_tarski(A_205))=k2_pre_topc('#skF_2', k1_tarski(A_205)) | ~v3_borsuk_1(C_204, '#skF_2', B_203) | ~m1_subset_1(C_204, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0(B_203)))) | ~v5_pre_topc(C_204, '#skF_2', B_203) | ~v1_funct_2(C_204, u1_struct_0('#skF_2'), u1_struct_0(B_203)) | ~v1_funct_1(C_204) | ~m1_pre_topc(B_203, '#skF_2') | ~v4_tex_2(B_203, '#skF_2') | v2_struct_0(B_203) | ~r2_hidden(A_205, u1_struct_0('#skF_3')) | ~r2_hidden(A_205, u1_struct_0(B_203)))), inference(resolution, [status(thm)], [c_4, c_490])).
% 3.27/1.54  tff(c_517, plain, (![A_205]: (k8_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4', k1_tarski(A_205))=k2_pre_topc('#skF_2', k1_tarski(A_205)) | ~v3_borsuk_1('#skF_4', '#skF_2', '#skF_3') | ~v5_pre_topc('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_2') | ~v4_tex_2('#skF_3', '#skF_2') | v2_struct_0('#skF_3') | ~r2_hidden(A_205, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_40, c_512])).
% 3.27/1.54  tff(c_521, plain, (![A_205]: (k8_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4', k1_tarski(A_205))=k2_pre_topc('#skF_2', k1_tarski(A_205)) | v2_struct_0('#skF_3') | ~r2_hidden(A_205, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_44, c_42, c_38, c_517])).
% 3.27/1.54  tff(c_523, plain, (![A_206]: (k8_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4', k1_tarski(A_206))=k2_pre_topc('#skF_2', k1_tarski(A_206)) | ~r2_hidden(A_206, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_52, c_521])).
% 3.27/1.54  tff(c_8, plain, (![A_6]: (l1_struct_0(A_6) | ~l1_pre_topc(A_6))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.27/1.54  tff(c_34, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_182])).
% 3.27/1.54  tff(c_96, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_6')=k1_tarski('#skF_6') | v1_xboole_0(u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_34, c_80])).
% 3.27/1.54  tff(c_268, plain, (v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_96])).
% 3.27/1.54  tff(c_10, plain, (![A_7]: (~v1_xboole_0(u1_struct_0(A_7)) | ~l1_struct_0(A_7) | v2_struct_0(A_7))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.27/1.54  tff(c_272, plain, (~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_268, c_10])).
% 3.27/1.54  tff(c_275, plain, (~l1_struct_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_60, c_272])).
% 3.27/1.54  tff(c_278, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_8, c_275])).
% 3.27/1.54  tff(c_282, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_278])).
% 3.27/1.54  tff(c_283, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_6')=k1_tarski('#skF_6')), inference(splitRight, [status(thm)], [c_96])).
% 3.27/1.54  tff(c_256, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_6')=k1_tarski('#skF_6')), inference(splitRight, [status(thm)], [c_95])).
% 3.27/1.54  tff(c_30, plain, (k8_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4', k6_domain_1(u1_struct_0('#skF_3'), '#skF_5'))!=k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_182])).
% 3.27/1.54  tff(c_62, plain, (k8_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4', k6_domain_1(u1_struct_0('#skF_3'), '#skF_6'))!=k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30])).
% 3.27/1.54  tff(c_263, plain, (k8_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4', k1_tarski('#skF_6'))!=k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_256, c_62])).
% 3.27/1.54  tff(c_289, plain, (k8_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4', k1_tarski('#skF_6'))!=k2_pre_topc('#skF_2', k1_tarski('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_283, c_263])).
% 3.27/1.54  tff(c_534, plain, (~r2_hidden('#skF_6', u1_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_523, c_289])).
% 3.27/1.54  tff(c_538, plain, (v1_xboole_0(u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_6, c_534])).
% 3.27/1.54  tff(c_541, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_61, c_538])).
% 3.27/1.54  tff(c_543, plain, $false, inference(negUnitSimplification, [status(thm)], [c_257, c_541])).
% 3.27/1.54  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.27/1.54  
% 3.27/1.54  Inference rules
% 3.27/1.54  ----------------------
% 3.27/1.54  #Ref     : 0
% 3.27/1.54  #Sup     : 98
% 3.27/1.54  #Fact    : 0
% 3.27/1.54  #Define  : 0
% 3.27/1.54  #Split   : 11
% 3.27/1.54  #Chain   : 0
% 3.27/1.54  #Close   : 0
% 3.27/1.54  
% 3.27/1.54  Ordering : KBO
% 3.27/1.54  
% 3.27/1.54  Simplification rules
% 3.27/1.54  ----------------------
% 3.27/1.54  #Subsume      : 7
% 3.27/1.54  #Demod        : 31
% 3.27/1.54  #Tautology    : 30
% 3.27/1.54  #SimpNegUnit  : 11
% 3.27/1.54  #BackRed      : 2
% 3.27/1.54  
% 3.27/1.54  #Partial instantiations: 0
% 3.27/1.54  #Strategies tried      : 1
% 3.27/1.54  
% 3.27/1.54  Timing (in seconds)
% 3.27/1.54  ----------------------
% 3.27/1.55  Preprocessing        : 0.38
% 3.27/1.55  Parsing              : 0.21
% 3.27/1.55  CNF conversion       : 0.03
% 3.27/1.55  Main loop            : 0.34
% 3.27/1.55  Inferencing          : 0.12
% 3.27/1.55  Reduction            : 0.10
% 3.27/1.55  Demodulation         : 0.07
% 3.27/1.55  BG Simplification    : 0.02
% 3.27/1.55  Subsumption          : 0.06
% 3.27/1.55  Abstraction          : 0.01
% 3.27/1.55  MUC search           : 0.00
% 3.27/1.55  Cooper               : 0.00
% 3.27/1.55  Total                : 0.75
% 3.27/1.55  Index Insertion      : 0.00
% 3.27/1.55  Index Deletion       : 0.00
% 3.27/1.55  Index Matching       : 0.00
% 3.27/1.55  BG Taut test         : 0.00
%------------------------------------------------------------------------------
