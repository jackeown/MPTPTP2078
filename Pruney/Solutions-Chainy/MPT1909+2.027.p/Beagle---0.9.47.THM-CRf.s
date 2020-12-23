%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:41 EST 2020

% Result     : Theorem 6.77s
% Output     : CNFRefutation 6.77s
% Verified   : 
% Statistics : Number of formulae       :  129 ( 307 expanded)
%              Number of leaves         :   49 ( 128 expanded)
%              Depth                    :   13
%              Number of atoms          :  277 (1449 expanded)
%              Number of equality atoms :   28 ( 171 expanded)
%              Maximal formula depth    :   20 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_pre_topc > v3_borsuk_1 > v1_funct_2 > v4_tex_2 > v3_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_pre_topc > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k8_relset_1 > k2_enumset1 > k1_enumset1 > k6_domain_1 > k2_zfmisc_1 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

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

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff(f_209,negated_conjecture,(
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

tff(f_60,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_93,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_86,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_170,axiom,(
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

tff(f_33,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

tff(f_100,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_69,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_117,axiom,(
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

tff(f_132,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( v1_xboole_0(B)
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
         => ~ v3_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_tex_2)).

tff(c_82,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_76,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_70,plain,(
    m1_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_80,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_72,plain,(
    v4_tex_2('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_54,plain,(
    '#skF_5' = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_58,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_83,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_58])).

tff(c_120,plain,(
    ! [B_132,A_133] :
      ( v1_xboole_0(B_132)
      | ~ m1_subset_1(B_132,A_133)
      | ~ v1_xboole_0(A_133) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_135,plain,
    ( v1_xboole_0('#skF_6')
    | ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_83,c_120])).

tff(c_137,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_135])).

tff(c_74,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_56,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_136,plain,
    ( v1_xboole_0('#skF_6')
    | ~ v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_56,c_120])).

tff(c_138,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_136])).

tff(c_181,plain,(
    ! [A_149,B_150] :
      ( k6_domain_1(A_149,B_150) = k1_tarski(B_150)
      | ~ m1_subset_1(B_150,A_149)
      | v1_xboole_0(A_149) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_196,plain,
    ( k6_domain_1(u1_struct_0('#skF_2'),'#skF_6') = k1_tarski('#skF_6')
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_56,c_181])).

tff(c_207,plain,(
    k6_domain_1(u1_struct_0('#skF_2'),'#skF_6') = k1_tarski('#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_138,c_196])).

tff(c_193,plain,
    ( k6_domain_1(u1_struct_0('#skF_3'),'#skF_6') = k1_tarski('#skF_6')
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_83,c_181])).

tff(c_204,plain,(
    k6_domain_1(u1_struct_0('#skF_3'),'#skF_6') = k1_tarski('#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_137,c_193])).

tff(c_52,plain,(
    k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4',k6_domain_1(u1_struct_0('#skF_3'),'#skF_5')) != k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_84,plain,(
    k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4',k6_domain_1(u1_struct_0('#skF_3'),'#skF_6')) != k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52])).

tff(c_208,plain,(
    k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4',k1_tarski('#skF_6')) != k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_204,c_84])).

tff(c_279,plain,(
    k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4',k1_tarski('#skF_6')) != k2_pre_topc('#skF_2',k1_tarski('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_207,c_208])).

tff(c_68,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_66,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_64,plain,(
    v5_pre_topc('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_60,plain,(
    v3_borsuk_1('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_248,plain,(
    ! [A_159,B_160] :
      ( m1_subset_1(k6_domain_1(A_159,B_160),k1_zfmisc_1(A_159))
      | ~ m1_subset_1(B_160,A_159)
      | v1_xboole_0(A_159) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_266,plain,
    ( m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3'))
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_204,c_248])).

tff(c_277,plain,
    ( m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_266])).

tff(c_278,plain,(
    m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_137,c_277])).

tff(c_62,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_78,plain,(
    v3_tdlat_3('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_263,plain,
    ( m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_2'))
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_207,c_248])).

tff(c_274,plain,
    ( m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_263])).

tff(c_275,plain,(
    m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_138,c_274])).

tff(c_1581,plain,(
    ! [A_251,B_252,C_253,E_254] :
      ( k8_relset_1(u1_struct_0(A_251),u1_struct_0(B_252),C_253,E_254) = k2_pre_topc(A_251,E_254)
      | ~ m1_subset_1(E_254,k1_zfmisc_1(u1_struct_0(A_251)))
      | ~ m1_subset_1(E_254,k1_zfmisc_1(u1_struct_0(B_252)))
      | ~ v3_borsuk_1(C_253,A_251,B_252)
      | ~ m1_subset_1(C_253,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_251),u1_struct_0(B_252))))
      | ~ v5_pre_topc(C_253,A_251,B_252)
      | ~ v1_funct_2(C_253,u1_struct_0(A_251),u1_struct_0(B_252))
      | ~ v1_funct_1(C_253)
      | ~ m1_pre_topc(B_252,A_251)
      | ~ v4_tex_2(B_252,A_251)
      | v2_struct_0(B_252)
      | ~ l1_pre_topc(A_251)
      | ~ v3_tdlat_3(A_251)
      | ~ v2_pre_topc(A_251)
      | v2_struct_0(A_251) ) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_1595,plain,(
    ! [B_252,C_253] :
      ( k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0(B_252),C_253,k1_tarski('#skF_6')) = k2_pre_topc('#skF_2',k1_tarski('#skF_6'))
      | ~ m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0(B_252)))
      | ~ v3_borsuk_1(C_253,'#skF_2',B_252)
      | ~ m1_subset_1(C_253,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0(B_252))))
      | ~ v5_pre_topc(C_253,'#skF_2',B_252)
      | ~ v1_funct_2(C_253,u1_struct_0('#skF_2'),u1_struct_0(B_252))
      | ~ v1_funct_1(C_253)
      | ~ m1_pre_topc(B_252,'#skF_2')
      | ~ v4_tex_2(B_252,'#skF_2')
      | v2_struct_0(B_252)
      | ~ l1_pre_topc('#skF_2')
      | ~ v3_tdlat_3('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_275,c_1581])).

tff(c_1619,plain,(
    ! [B_252,C_253] :
      ( k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0(B_252),C_253,k1_tarski('#skF_6')) = k2_pre_topc('#skF_2',k1_tarski('#skF_6'))
      | ~ m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0(B_252)))
      | ~ v3_borsuk_1(C_253,'#skF_2',B_252)
      | ~ m1_subset_1(C_253,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0(B_252))))
      | ~ v5_pre_topc(C_253,'#skF_2',B_252)
      | ~ v1_funct_2(C_253,u1_struct_0('#skF_2'),u1_struct_0(B_252))
      | ~ v1_funct_1(C_253)
      | ~ m1_pre_topc(B_252,'#skF_2')
      | ~ v4_tex_2(B_252,'#skF_2')
      | v2_struct_0(B_252)
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_76,c_1595])).

tff(c_1640,plain,(
    ! [B_257,C_258] :
      ( k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0(B_257),C_258,k1_tarski('#skF_6')) = k2_pre_topc('#skF_2',k1_tarski('#skF_6'))
      | ~ m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0(B_257)))
      | ~ v3_borsuk_1(C_258,'#skF_2',B_257)
      | ~ m1_subset_1(C_258,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0(B_257))))
      | ~ v5_pre_topc(C_258,'#skF_2',B_257)
      | ~ v1_funct_2(C_258,u1_struct_0('#skF_2'),u1_struct_0(B_257))
      | ~ v1_funct_1(C_258)
      | ~ m1_pre_topc(B_257,'#skF_2')
      | ~ v4_tex_2(B_257,'#skF_2')
      | v2_struct_0(B_257) ) ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_1619])).

tff(c_1651,plain,
    ( k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4',k1_tarski('#skF_6')) = k2_pre_topc('#skF_2',k1_tarski('#skF_6'))
    | ~ m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ v3_borsuk_1('#skF_4','#skF_2','#skF_3')
    | ~ v5_pre_topc('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ v4_tex_2('#skF_3','#skF_2')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_1640])).

tff(c_1660,plain,
    ( k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4',k1_tarski('#skF_6')) = k2_pre_topc('#skF_2',k1_tarski('#skF_6'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_68,c_66,c_64,c_60,c_278,c_1651])).

tff(c_1662,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_279,c_1660])).

tff(c_1664,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_136])).

tff(c_1663,plain,(
    v1_xboole_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_136])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( ~ v1_xboole_0(B_2)
      | B_2 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1671,plain,(
    ! [A_259] :
      ( A_259 = '#skF_6'
      | ~ v1_xboole_0(A_259) ) ),
    inference(resolution,[status(thm)],[c_1663,c_2])).

tff(c_1678,plain,(
    u1_struct_0('#skF_2') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_1664,c_1671])).

tff(c_1841,plain,(
    ! [B_283,A_284] :
      ( m1_subset_1(u1_struct_0(B_283),k1_zfmisc_1(u1_struct_0(A_284)))
      | ~ m1_pre_topc(B_283,A_284)
      | ~ l1_pre_topc(A_284) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_1856,plain,(
    ! [B_283] :
      ( m1_subset_1(u1_struct_0(B_283),k1_zfmisc_1('#skF_6'))
      | ~ m1_pre_topc(B_283,'#skF_2')
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1678,c_1841])).

tff(c_1862,plain,(
    ! [B_285] :
      ( m1_subset_1(u1_struct_0(B_285),k1_zfmisc_1('#skF_6'))
      | ~ m1_pre_topc(B_285,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_1856])).

tff(c_26,plain,(
    ! [A_33,B_34] :
      ( r1_tarski(A_33,B_34)
      | ~ m1_subset_1(A_33,k1_zfmisc_1(B_34)) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_1878,plain,(
    ! [B_286] :
      ( r1_tarski(u1_struct_0(B_286),'#skF_6')
      | ~ m1_pre_topc(B_286,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_1862,c_26])).

tff(c_1717,plain,(
    ! [B_264,A_265] :
      ( r2_hidden(B_264,A_265)
      | ~ m1_subset_1(B_264,A_265)
      | v1_xboole_0(A_265) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_30,plain,(
    ! [B_36,A_35] :
      ( ~ r1_tarski(B_36,A_35)
      | ~ r2_hidden(A_35,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1725,plain,(
    ! [A_265,B_264] :
      ( ~ r1_tarski(A_265,B_264)
      | ~ m1_subset_1(B_264,A_265)
      | v1_xboole_0(A_265) ) ),
    inference(resolution,[status(thm)],[c_1717,c_30])).

tff(c_1974,plain,(
    ! [B_298] :
      ( ~ m1_subset_1('#skF_6',u1_struct_0(B_298))
      | v1_xboole_0(u1_struct_0(B_298))
      | ~ m1_pre_topc(B_298,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_1878,c_1725])).

tff(c_1983,plain,
    ( v1_xboole_0(u1_struct_0('#skF_3'))
    | ~ m1_pre_topc('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_83,c_1974])).

tff(c_1991,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_1983])).

tff(c_1993,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_137,c_1991])).

tff(c_1995,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_135])).

tff(c_1994,plain,(
    v1_xboole_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_135])).

tff(c_2002,plain,(
    ! [A_299] :
      ( A_299 = '#skF_6'
      | ~ v1_xboole_0(A_299) ) ),
    inference(resolution,[status(thm)],[c_1994,c_2])).

tff(c_2009,plain,(
    u1_struct_0('#skF_3') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_1995,c_2002])).

tff(c_38,plain,(
    ! [B_50,A_48] :
      ( m1_subset_1(u1_struct_0(B_50),k1_zfmisc_1(u1_struct_0(A_48)))
      | ~ m1_pre_topc(B_50,A_48)
      | ~ l1_pre_topc(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_5122,plain,(
    ! [B_542,A_543] :
      ( v3_tex_2(u1_struct_0(B_542),A_543)
      | ~ m1_subset_1(u1_struct_0(B_542),k1_zfmisc_1(u1_struct_0(A_543)))
      | ~ v4_tex_2(B_542,A_543)
      | ~ m1_pre_topc(B_542,A_543)
      | ~ l1_pre_topc(A_543)
      | v2_struct_0(A_543) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_5161,plain,(
    ! [B_544,A_545] :
      ( v3_tex_2(u1_struct_0(B_544),A_545)
      | ~ v4_tex_2(B_544,A_545)
      | v2_struct_0(A_545)
      | ~ m1_pre_topc(B_544,A_545)
      | ~ l1_pre_topc(A_545) ) ),
    inference(resolution,[status(thm)],[c_38,c_5122])).

tff(c_5176,plain,(
    ! [A_546] :
      ( v3_tex_2('#skF_6',A_546)
      | ~ v4_tex_2('#skF_3',A_546)
      | v2_struct_0(A_546)
      | ~ m1_pre_topc('#skF_3',A_546)
      | ~ l1_pre_topc(A_546) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2009,c_5161])).

tff(c_5183,plain,
    ( v3_tex_2('#skF_6','#skF_2')
    | v2_struct_0('#skF_2')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_72,c_5176])).

tff(c_5188,plain,
    ( v3_tex_2('#skF_6','#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_70,c_5183])).

tff(c_5189,plain,(
    v3_tex_2('#skF_6','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_5188])).

tff(c_3877,plain,(
    ! [B_439,A_440] :
      ( m1_subset_1(u1_struct_0(B_439),k1_zfmisc_1(u1_struct_0(A_440)))
      | ~ m1_pre_topc(B_439,A_440)
      | ~ l1_pre_topc(A_440) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_3889,plain,(
    ! [A_440] :
      ( m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0(A_440)))
      | ~ m1_pre_topc('#skF_3',A_440)
      | ~ l1_pre_topc(A_440) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2009,c_3877])).

tff(c_4594,plain,(
    ! [B_500,A_501] :
      ( ~ v3_tex_2(B_500,A_501)
      | ~ m1_subset_1(B_500,k1_zfmisc_1(u1_struct_0(A_501)))
      | ~ v1_xboole_0(B_500)
      | ~ l1_pre_topc(A_501)
      | ~ v2_pre_topc(A_501)
      | v2_struct_0(A_501) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_4600,plain,(
    ! [A_440] :
      ( ~ v3_tex_2('#skF_6',A_440)
      | ~ v1_xboole_0('#skF_6')
      | ~ v2_pre_topc(A_440)
      | v2_struct_0(A_440)
      | ~ m1_pre_topc('#skF_3',A_440)
      | ~ l1_pre_topc(A_440) ) ),
    inference(resolution,[status(thm)],[c_3889,c_4594])).

tff(c_4625,plain,(
    ! [A_440] :
      ( ~ v3_tex_2('#skF_6',A_440)
      | ~ v2_pre_topc(A_440)
      | v2_struct_0(A_440)
      | ~ m1_pre_topc('#skF_3',A_440)
      | ~ l1_pre_topc(A_440) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1994,c_4600])).

tff(c_5197,plain,
    ( ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_5189,c_4625])).

tff(c_5207,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_70,c_80,c_5197])).

tff(c_5209,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_5207])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n015.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 14:45:23 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.19/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.77/2.45  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.77/2.46  
% 6.77/2.46  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.77/2.46  %$ v5_pre_topc > v3_borsuk_1 > v1_funct_2 > v4_tex_2 > v3_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_pre_topc > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k8_relset_1 > k2_enumset1 > k1_enumset1 > k6_domain_1 > k2_zfmisc_1 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 6.77/2.46  
% 6.77/2.46  %Foreground sorts:
% 6.77/2.46  
% 6.77/2.46  
% 6.77/2.46  %Background operators:
% 6.77/2.46  
% 6.77/2.46  
% 6.77/2.46  %Foreground operators:
% 6.77/2.46  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 6.77/2.46  tff(v3_borsuk_1, type, v3_borsuk_1: ($i * $i * $i) > $o).
% 6.77/2.46  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.77/2.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.77/2.46  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.77/2.46  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.77/2.46  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 6.77/2.46  tff(v4_tex_2, type, v4_tex_2: ($i * $i) > $o).
% 6.77/2.46  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 6.77/2.46  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 6.77/2.46  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 6.77/2.46  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.77/2.46  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.77/2.46  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.77/2.46  tff('#skF_5', type, '#skF_5': $i).
% 6.77/2.46  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 6.77/2.46  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.77/2.46  tff('#skF_6', type, '#skF_6': $i).
% 6.77/2.46  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.77/2.46  tff('#skF_2', type, '#skF_2': $i).
% 6.77/2.46  tff('#skF_3', type, '#skF_3': $i).
% 6.77/2.46  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 6.77/2.46  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.77/2.46  tff(v3_tdlat_3, type, v3_tdlat_3: $i > $o).
% 6.77/2.46  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 6.77/2.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.77/2.46  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.77/2.46  tff('#skF_4', type, '#skF_4': $i).
% 6.77/2.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.77/2.46  tff(v5_pre_topc, type, v5_pre_topc: ($i * $i * $i) > $o).
% 6.77/2.46  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 6.77/2.46  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 6.77/2.46  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 6.77/2.46  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 6.77/2.46  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 6.77/2.46  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.77/2.46  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 6.77/2.46  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.77/2.46  
% 6.77/2.48  tff(f_209, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v4_tex_2(B, A)) & m1_pre_topc(B, A)) => (![C]: ((((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & v5_pre_topc(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (v3_borsuk_1(C, A, B) => (![D]: (m1_subset_1(D, u1_struct_0(B)) => (![E]: (m1_subset_1(E, u1_struct_0(A)) => ((D = E) => (k8_relset_1(u1_struct_0(A), u1_struct_0(B), C, k6_domain_1(u1_struct_0(B), D)) = k2_pre_topc(A, k6_domain_1(u1_struct_0(A), E))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_tex_2)).
% 6.77/2.48  tff(f_60, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 6.77/2.48  tff(f_93, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 6.77/2.48  tff(f_86, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 6.77/2.48  tff(f_170, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v4_tex_2(B, A)) & m1_pre_topc(B, A)) => (![C]: ((((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & v5_pre_topc(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (v3_borsuk_1(C, A, B) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => (![E]: (m1_subset_1(E, k1_zfmisc_1(u1_struct_0(A))) => ((D = E) => (k8_relset_1(u1_struct_0(A), u1_struct_0(B), C, D) = k2_pre_topc(A, E)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t76_tex_2)).
% 6.77/2.48  tff(f_33, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 6.77/2.48  tff(f_100, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 6.77/2.48  tff(f_64, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 6.77/2.48  tff(f_69, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 6.77/2.48  tff(f_117, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (v4_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => v3_tex_2(C, A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_tex_2)).
% 6.77/2.48  tff(f_132, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ~v3_tex_2(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_tex_2)).
% 6.77/2.48  tff(c_82, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_209])).
% 6.77/2.48  tff(c_76, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_209])).
% 6.77/2.48  tff(c_70, plain, (m1_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_209])).
% 6.77/2.48  tff(c_80, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_209])).
% 6.77/2.48  tff(c_72, plain, (v4_tex_2('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_209])).
% 6.77/2.48  tff(c_54, plain, ('#skF_5'='#skF_6'), inference(cnfTransformation, [status(thm)], [f_209])).
% 6.77/2.48  tff(c_58, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_209])).
% 6.77/2.48  tff(c_83, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_58])).
% 6.77/2.48  tff(c_120, plain, (![B_132, A_133]: (v1_xboole_0(B_132) | ~m1_subset_1(B_132, A_133) | ~v1_xboole_0(A_133))), inference(cnfTransformation, [status(thm)], [f_60])).
% 6.77/2.48  tff(c_135, plain, (v1_xboole_0('#skF_6') | ~v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_83, c_120])).
% 6.77/2.48  tff(c_137, plain, (~v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_135])).
% 6.77/2.48  tff(c_74, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_209])).
% 6.77/2.48  tff(c_56, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_209])).
% 6.77/2.48  tff(c_136, plain, (v1_xboole_0('#skF_6') | ~v1_xboole_0(u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_56, c_120])).
% 6.77/2.48  tff(c_138, plain, (~v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_136])).
% 6.77/2.48  tff(c_181, plain, (![A_149, B_150]: (k6_domain_1(A_149, B_150)=k1_tarski(B_150) | ~m1_subset_1(B_150, A_149) | v1_xboole_0(A_149))), inference(cnfTransformation, [status(thm)], [f_93])).
% 6.77/2.48  tff(c_196, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_6')=k1_tarski('#skF_6') | v1_xboole_0(u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_56, c_181])).
% 6.77/2.48  tff(c_207, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_6')=k1_tarski('#skF_6')), inference(negUnitSimplification, [status(thm)], [c_138, c_196])).
% 6.77/2.48  tff(c_193, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_6')=k1_tarski('#skF_6') | v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_83, c_181])).
% 6.77/2.48  tff(c_204, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_6')=k1_tarski('#skF_6')), inference(negUnitSimplification, [status(thm)], [c_137, c_193])).
% 6.77/2.48  tff(c_52, plain, (k8_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4', k6_domain_1(u1_struct_0('#skF_3'), '#skF_5'))!=k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_209])).
% 6.77/2.48  tff(c_84, plain, (k8_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4', k6_domain_1(u1_struct_0('#skF_3'), '#skF_6'))!=k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52])).
% 6.77/2.48  tff(c_208, plain, (k8_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4', k1_tarski('#skF_6'))!=k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_204, c_84])).
% 6.77/2.48  tff(c_279, plain, (k8_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4', k1_tarski('#skF_6'))!=k2_pre_topc('#skF_2', k1_tarski('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_207, c_208])).
% 6.77/2.48  tff(c_68, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_209])).
% 6.77/2.48  tff(c_66, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_209])).
% 6.77/2.48  tff(c_64, plain, (v5_pre_topc('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_209])).
% 6.77/2.48  tff(c_60, plain, (v3_borsuk_1('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_209])).
% 6.77/2.48  tff(c_248, plain, (![A_159, B_160]: (m1_subset_1(k6_domain_1(A_159, B_160), k1_zfmisc_1(A_159)) | ~m1_subset_1(B_160, A_159) | v1_xboole_0(A_159))), inference(cnfTransformation, [status(thm)], [f_86])).
% 6.77/2.48  tff(c_266, plain, (m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_3')) | v1_xboole_0(u1_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_204, c_248])).
% 6.77/2.48  tff(c_277, plain, (m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | v1_xboole_0(u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_83, c_266])).
% 6.77/2.48  tff(c_278, plain, (m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_137, c_277])).
% 6.77/2.48  tff(c_62, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_209])).
% 6.77/2.48  tff(c_78, plain, (v3_tdlat_3('#skF_2')), inference(cnfTransformation, [status(thm)], [f_209])).
% 6.77/2.48  tff(c_263, plain, (m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_2')) | v1_xboole_0(u1_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_207, c_248])).
% 6.77/2.48  tff(c_274, plain, (m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | v1_xboole_0(u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_263])).
% 6.77/2.48  tff(c_275, plain, (m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_138, c_274])).
% 6.77/2.48  tff(c_1581, plain, (![A_251, B_252, C_253, E_254]: (k8_relset_1(u1_struct_0(A_251), u1_struct_0(B_252), C_253, E_254)=k2_pre_topc(A_251, E_254) | ~m1_subset_1(E_254, k1_zfmisc_1(u1_struct_0(A_251))) | ~m1_subset_1(E_254, k1_zfmisc_1(u1_struct_0(B_252))) | ~v3_borsuk_1(C_253, A_251, B_252) | ~m1_subset_1(C_253, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_251), u1_struct_0(B_252)))) | ~v5_pre_topc(C_253, A_251, B_252) | ~v1_funct_2(C_253, u1_struct_0(A_251), u1_struct_0(B_252)) | ~v1_funct_1(C_253) | ~m1_pre_topc(B_252, A_251) | ~v4_tex_2(B_252, A_251) | v2_struct_0(B_252) | ~l1_pre_topc(A_251) | ~v3_tdlat_3(A_251) | ~v2_pre_topc(A_251) | v2_struct_0(A_251))), inference(cnfTransformation, [status(thm)], [f_170])).
% 6.77/2.48  tff(c_1595, plain, (![B_252, C_253]: (k8_relset_1(u1_struct_0('#skF_2'), u1_struct_0(B_252), C_253, k1_tarski('#skF_6'))=k2_pre_topc('#skF_2', k1_tarski('#skF_6')) | ~m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0(B_252))) | ~v3_borsuk_1(C_253, '#skF_2', B_252) | ~m1_subset_1(C_253, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0(B_252)))) | ~v5_pre_topc(C_253, '#skF_2', B_252) | ~v1_funct_2(C_253, u1_struct_0('#skF_2'), u1_struct_0(B_252)) | ~v1_funct_1(C_253) | ~m1_pre_topc(B_252, '#skF_2') | ~v4_tex_2(B_252, '#skF_2') | v2_struct_0(B_252) | ~l1_pre_topc('#skF_2') | ~v3_tdlat_3('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_275, c_1581])).
% 6.77/2.48  tff(c_1619, plain, (![B_252, C_253]: (k8_relset_1(u1_struct_0('#skF_2'), u1_struct_0(B_252), C_253, k1_tarski('#skF_6'))=k2_pre_topc('#skF_2', k1_tarski('#skF_6')) | ~m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0(B_252))) | ~v3_borsuk_1(C_253, '#skF_2', B_252) | ~m1_subset_1(C_253, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0(B_252)))) | ~v5_pre_topc(C_253, '#skF_2', B_252) | ~v1_funct_2(C_253, u1_struct_0('#skF_2'), u1_struct_0(B_252)) | ~v1_funct_1(C_253) | ~m1_pre_topc(B_252, '#skF_2') | ~v4_tex_2(B_252, '#skF_2') | v2_struct_0(B_252) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_76, c_1595])).
% 6.77/2.48  tff(c_1640, plain, (![B_257, C_258]: (k8_relset_1(u1_struct_0('#skF_2'), u1_struct_0(B_257), C_258, k1_tarski('#skF_6'))=k2_pre_topc('#skF_2', k1_tarski('#skF_6')) | ~m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0(B_257))) | ~v3_borsuk_1(C_258, '#skF_2', B_257) | ~m1_subset_1(C_258, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0(B_257)))) | ~v5_pre_topc(C_258, '#skF_2', B_257) | ~v1_funct_2(C_258, u1_struct_0('#skF_2'), u1_struct_0(B_257)) | ~v1_funct_1(C_258) | ~m1_pre_topc(B_257, '#skF_2') | ~v4_tex_2(B_257, '#skF_2') | v2_struct_0(B_257))), inference(negUnitSimplification, [status(thm)], [c_82, c_1619])).
% 6.77/2.48  tff(c_1651, plain, (k8_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4', k1_tarski('#skF_6'))=k2_pre_topc('#skF_2', k1_tarski('#skF_6')) | ~m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~v3_borsuk_1('#skF_4', '#skF_2', '#skF_3') | ~v5_pre_topc('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_2') | ~v4_tex_2('#skF_3', '#skF_2') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_62, c_1640])).
% 6.77/2.48  tff(c_1660, plain, (k8_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4', k1_tarski('#skF_6'))=k2_pre_topc('#skF_2', k1_tarski('#skF_6')) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_68, c_66, c_64, c_60, c_278, c_1651])).
% 6.77/2.48  tff(c_1662, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_279, c_1660])).
% 6.77/2.48  tff(c_1664, plain, (v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_136])).
% 6.77/2.48  tff(c_1663, plain, (v1_xboole_0('#skF_6')), inference(splitRight, [status(thm)], [c_136])).
% 6.77/2.48  tff(c_2, plain, (![B_2, A_1]: (~v1_xboole_0(B_2) | B_2=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.77/2.48  tff(c_1671, plain, (![A_259]: (A_259='#skF_6' | ~v1_xboole_0(A_259))), inference(resolution, [status(thm)], [c_1663, c_2])).
% 6.77/2.48  tff(c_1678, plain, (u1_struct_0('#skF_2')='#skF_6'), inference(resolution, [status(thm)], [c_1664, c_1671])).
% 6.77/2.48  tff(c_1841, plain, (![B_283, A_284]: (m1_subset_1(u1_struct_0(B_283), k1_zfmisc_1(u1_struct_0(A_284))) | ~m1_pre_topc(B_283, A_284) | ~l1_pre_topc(A_284))), inference(cnfTransformation, [status(thm)], [f_100])).
% 6.77/2.48  tff(c_1856, plain, (![B_283]: (m1_subset_1(u1_struct_0(B_283), k1_zfmisc_1('#skF_6')) | ~m1_pre_topc(B_283, '#skF_2') | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1678, c_1841])).
% 6.77/2.48  tff(c_1862, plain, (![B_285]: (m1_subset_1(u1_struct_0(B_285), k1_zfmisc_1('#skF_6')) | ~m1_pre_topc(B_285, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_1856])).
% 6.77/2.48  tff(c_26, plain, (![A_33, B_34]: (r1_tarski(A_33, B_34) | ~m1_subset_1(A_33, k1_zfmisc_1(B_34)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 6.77/2.48  tff(c_1878, plain, (![B_286]: (r1_tarski(u1_struct_0(B_286), '#skF_6') | ~m1_pre_topc(B_286, '#skF_2'))), inference(resolution, [status(thm)], [c_1862, c_26])).
% 6.77/2.48  tff(c_1717, plain, (![B_264, A_265]: (r2_hidden(B_264, A_265) | ~m1_subset_1(B_264, A_265) | v1_xboole_0(A_265))), inference(cnfTransformation, [status(thm)], [f_60])).
% 6.77/2.48  tff(c_30, plain, (![B_36, A_35]: (~r1_tarski(B_36, A_35) | ~r2_hidden(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_69])).
% 6.77/2.48  tff(c_1725, plain, (![A_265, B_264]: (~r1_tarski(A_265, B_264) | ~m1_subset_1(B_264, A_265) | v1_xboole_0(A_265))), inference(resolution, [status(thm)], [c_1717, c_30])).
% 6.77/2.48  tff(c_1974, plain, (![B_298]: (~m1_subset_1('#skF_6', u1_struct_0(B_298)) | v1_xboole_0(u1_struct_0(B_298)) | ~m1_pre_topc(B_298, '#skF_2'))), inference(resolution, [status(thm)], [c_1878, c_1725])).
% 6.77/2.48  tff(c_1983, plain, (v1_xboole_0(u1_struct_0('#skF_3')) | ~m1_pre_topc('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_83, c_1974])).
% 6.77/2.48  tff(c_1991, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_1983])).
% 6.77/2.48  tff(c_1993, plain, $false, inference(negUnitSimplification, [status(thm)], [c_137, c_1991])).
% 6.77/2.48  tff(c_1995, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_135])).
% 6.77/2.48  tff(c_1994, plain, (v1_xboole_0('#skF_6')), inference(splitRight, [status(thm)], [c_135])).
% 6.77/2.48  tff(c_2002, plain, (![A_299]: (A_299='#skF_6' | ~v1_xboole_0(A_299))), inference(resolution, [status(thm)], [c_1994, c_2])).
% 6.77/2.48  tff(c_2009, plain, (u1_struct_0('#skF_3')='#skF_6'), inference(resolution, [status(thm)], [c_1995, c_2002])).
% 6.77/2.48  tff(c_38, plain, (![B_50, A_48]: (m1_subset_1(u1_struct_0(B_50), k1_zfmisc_1(u1_struct_0(A_48))) | ~m1_pre_topc(B_50, A_48) | ~l1_pre_topc(A_48))), inference(cnfTransformation, [status(thm)], [f_100])).
% 6.77/2.48  tff(c_5122, plain, (![B_542, A_543]: (v3_tex_2(u1_struct_0(B_542), A_543) | ~m1_subset_1(u1_struct_0(B_542), k1_zfmisc_1(u1_struct_0(A_543))) | ~v4_tex_2(B_542, A_543) | ~m1_pre_topc(B_542, A_543) | ~l1_pre_topc(A_543) | v2_struct_0(A_543))), inference(cnfTransformation, [status(thm)], [f_117])).
% 6.77/2.48  tff(c_5161, plain, (![B_544, A_545]: (v3_tex_2(u1_struct_0(B_544), A_545) | ~v4_tex_2(B_544, A_545) | v2_struct_0(A_545) | ~m1_pre_topc(B_544, A_545) | ~l1_pre_topc(A_545))), inference(resolution, [status(thm)], [c_38, c_5122])).
% 6.77/2.48  tff(c_5176, plain, (![A_546]: (v3_tex_2('#skF_6', A_546) | ~v4_tex_2('#skF_3', A_546) | v2_struct_0(A_546) | ~m1_pre_topc('#skF_3', A_546) | ~l1_pre_topc(A_546))), inference(superposition, [status(thm), theory('equality')], [c_2009, c_5161])).
% 6.77/2.48  tff(c_5183, plain, (v3_tex_2('#skF_6', '#skF_2') | v2_struct_0('#skF_2') | ~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_72, c_5176])).
% 6.77/2.48  tff(c_5188, plain, (v3_tex_2('#skF_6', '#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_70, c_5183])).
% 6.77/2.48  tff(c_5189, plain, (v3_tex_2('#skF_6', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_82, c_5188])).
% 6.77/2.48  tff(c_3877, plain, (![B_439, A_440]: (m1_subset_1(u1_struct_0(B_439), k1_zfmisc_1(u1_struct_0(A_440))) | ~m1_pre_topc(B_439, A_440) | ~l1_pre_topc(A_440))), inference(cnfTransformation, [status(thm)], [f_100])).
% 6.77/2.48  tff(c_3889, plain, (![A_440]: (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0(A_440))) | ~m1_pre_topc('#skF_3', A_440) | ~l1_pre_topc(A_440))), inference(superposition, [status(thm), theory('equality')], [c_2009, c_3877])).
% 6.77/2.48  tff(c_4594, plain, (![B_500, A_501]: (~v3_tex_2(B_500, A_501) | ~m1_subset_1(B_500, k1_zfmisc_1(u1_struct_0(A_501))) | ~v1_xboole_0(B_500) | ~l1_pre_topc(A_501) | ~v2_pre_topc(A_501) | v2_struct_0(A_501))), inference(cnfTransformation, [status(thm)], [f_132])).
% 6.77/2.48  tff(c_4600, plain, (![A_440]: (~v3_tex_2('#skF_6', A_440) | ~v1_xboole_0('#skF_6') | ~v2_pre_topc(A_440) | v2_struct_0(A_440) | ~m1_pre_topc('#skF_3', A_440) | ~l1_pre_topc(A_440))), inference(resolution, [status(thm)], [c_3889, c_4594])).
% 6.77/2.48  tff(c_4625, plain, (![A_440]: (~v3_tex_2('#skF_6', A_440) | ~v2_pre_topc(A_440) | v2_struct_0(A_440) | ~m1_pre_topc('#skF_3', A_440) | ~l1_pre_topc(A_440))), inference(demodulation, [status(thm), theory('equality')], [c_1994, c_4600])).
% 6.77/2.48  tff(c_5197, plain, (~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_5189, c_4625])).
% 6.77/2.48  tff(c_5207, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_70, c_80, c_5197])).
% 6.77/2.48  tff(c_5209, plain, $false, inference(negUnitSimplification, [status(thm)], [c_82, c_5207])).
% 6.77/2.48  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.77/2.48  
% 6.77/2.48  Inference rules
% 6.77/2.48  ----------------------
% 6.77/2.48  #Ref     : 0
% 6.77/2.48  #Sup     : 1121
% 6.77/2.48  #Fact    : 0
% 6.77/2.48  #Define  : 0
% 6.77/2.48  #Split   : 54
% 6.77/2.48  #Chain   : 0
% 6.77/2.48  #Close   : 0
% 6.77/2.48  
% 6.77/2.48  Ordering : KBO
% 6.77/2.48  
% 6.77/2.48  Simplification rules
% 6.77/2.48  ----------------------
% 6.77/2.48  #Subsume      : 195
% 6.77/2.48  #Demod        : 376
% 6.77/2.48  #Tautology    : 392
% 6.77/2.48  #SimpNegUnit  : 231
% 6.77/2.48  #BackRed      : 17
% 6.77/2.48  
% 6.77/2.48  #Partial instantiations: 0
% 6.77/2.48  #Strategies tried      : 1
% 6.77/2.48  
% 6.77/2.48  Timing (in seconds)
% 6.77/2.48  ----------------------
% 6.77/2.48  Preprocessing        : 0.50
% 6.77/2.48  Parsing              : 0.22
% 6.77/2.48  CNF conversion       : 0.05
% 6.77/2.48  Main loop            : 1.15
% 6.77/2.48  Inferencing          : 0.40
% 6.77/2.48  Reduction            : 0.36
% 6.77/2.48  Demodulation         : 0.24
% 6.77/2.48  BG Simplification    : 0.07
% 6.77/2.48  Subsumption          : 0.25
% 6.77/2.48  Abstraction          : 0.05
% 6.77/2.48  MUC search           : 0.00
% 6.77/2.48  Cooper               : 0.00
% 6.77/2.48  Total                : 1.69
% 6.77/2.48  Index Insertion      : 0.00
% 6.77/2.48  Index Deletion       : 0.00
% 6.77/2.48  Index Matching       : 0.00
% 6.77/2.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
