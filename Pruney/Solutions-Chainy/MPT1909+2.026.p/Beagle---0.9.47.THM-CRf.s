%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:41 EST 2020

% Result     : Theorem 4.27s
% Output     : CNFRefutation 4.60s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 185 expanded)
%              Number of leaves         :   49 (  89 expanded)
%              Depth                    :   15
%              Number of atoms          :  268 ( 835 expanded)
%              Number of equality atoms :   24 ( 102 expanded)
%              Maximal formula depth    :   20 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_pre_topc > v3_borsuk_1 > v1_funct_2 > v4_tex_2 > v3_tex_2 > r2_hidden > m1_subset_1 > m1_pre_topc > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_pre_topc > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k8_relset_1 > k2_enumset1 > k1_enumset1 > k6_domain_1 > k2_zfmisc_1 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2

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

tff(f_195,negated_conjecture,(
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

tff(f_79,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_86,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_103,axiom,(
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

tff(f_118,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( v1_xboole_0(B)
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
         => ~ v3_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_tex_2)).

tff(f_62,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_56,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(k1_tarski(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).

tff(f_72,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(B)))
             => m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_pre_topc)).

tff(f_156,axiom,(
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

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_52,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(c_74,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_68,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_62,plain,(
    m1_pre_topc('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_72,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_64,plain,(
    v4_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_50,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_120,plain,(
    ! [A_136,B_137] :
      ( k6_domain_1(A_136,B_137) = k1_tarski(B_137)
      | ~ m1_subset_1(B_137,A_136)
      | v1_xboole_0(A_136) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_135,plain,
    ( k6_domain_1(u1_struct_0('#skF_4'),'#skF_6') = k1_tarski('#skF_6')
    | v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_50,c_120])).

tff(c_137,plain,(
    v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_135])).

tff(c_30,plain,(
    ! [B_52,A_50] :
      ( m1_subset_1(u1_struct_0(B_52),k1_zfmisc_1(u1_struct_0(A_50)))
      | ~ m1_pre_topc(B_52,A_50)
      | ~ l1_pre_topc(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_483,plain,(
    ! [B_231,A_232] :
      ( v3_tex_2(u1_struct_0(B_231),A_232)
      | ~ m1_subset_1(u1_struct_0(B_231),k1_zfmisc_1(u1_struct_0(A_232)))
      | ~ v4_tex_2(B_231,A_232)
      | ~ m1_pre_topc(B_231,A_232)
      | ~ l1_pre_topc(A_232)
      | v2_struct_0(A_232) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_488,plain,(
    ! [B_233,A_234] :
      ( v3_tex_2(u1_struct_0(B_233),A_234)
      | ~ v4_tex_2(B_233,A_234)
      | v2_struct_0(A_234)
      | ~ m1_pre_topc(B_233,A_234)
      | ~ l1_pre_topc(A_234) ) ),
    inference(resolution,[status(thm)],[c_30,c_483])).

tff(c_275,plain,(
    ! [B_189,A_190] :
      ( ~ v3_tex_2(B_189,A_190)
      | ~ m1_subset_1(B_189,k1_zfmisc_1(u1_struct_0(A_190)))
      | ~ v1_xboole_0(B_189)
      | ~ l1_pre_topc(A_190)
      | ~ v2_pre_topc(A_190)
      | v2_struct_0(A_190) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_283,plain,(
    ! [B_52,A_50] :
      ( ~ v3_tex_2(u1_struct_0(B_52),A_50)
      | ~ v1_xboole_0(u1_struct_0(B_52))
      | ~ v2_pre_topc(A_50)
      | v2_struct_0(A_50)
      | ~ m1_pre_topc(B_52,A_50)
      | ~ l1_pre_topc(A_50) ) ),
    inference(resolution,[status(thm)],[c_30,c_275])).

tff(c_493,plain,(
    ! [B_235,A_236] :
      ( ~ v1_xboole_0(u1_struct_0(B_235))
      | ~ v2_pre_topc(A_236)
      | ~ v4_tex_2(B_235,A_236)
      | v2_struct_0(A_236)
      | ~ m1_pre_topc(B_235,A_236)
      | ~ l1_pre_topc(A_236) ) ),
    inference(resolution,[status(thm)],[c_488,c_283])).

tff(c_520,plain,(
    ! [A_239] :
      ( ~ v2_pre_topc(A_239)
      | ~ v4_tex_2('#skF_4',A_239)
      | v2_struct_0(A_239)
      | ~ m1_pre_topc('#skF_4',A_239)
      | ~ l1_pre_topc(A_239) ) ),
    inference(resolution,[status(thm)],[c_137,c_493])).

tff(c_527,plain,
    ( ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_520])).

tff(c_531,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_62,c_72,c_527])).

tff(c_533,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_531])).

tff(c_535,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_135])).

tff(c_24,plain,(
    ! [A_39,B_40] :
      ( r2_hidden(A_39,B_40)
      | v1_xboole_0(B_40)
      | ~ m1_subset_1(A_39,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_66,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_60,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_58,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_56,plain,(
    v5_pre_topc('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_52,plain,(
    v3_borsuk_1('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_54,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_22,plain,(
    ! [A_37,B_38] :
      ( m1_subset_1(k1_tarski(A_37),k1_zfmisc_1(B_38))
      | ~ r2_hidden(A_37,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_70,plain,(
    v3_tdlat_3('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_726,plain,(
    ! [C_302,A_303,B_304] :
      ( m1_subset_1(C_302,k1_zfmisc_1(u1_struct_0(A_303)))
      | ~ m1_subset_1(C_302,k1_zfmisc_1(u1_struct_0(B_304)))
      | ~ m1_pre_topc(B_304,A_303)
      | ~ l1_pre_topc(A_303) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_736,plain,(
    ! [A_309,A_310,B_311] :
      ( m1_subset_1(k1_tarski(A_309),k1_zfmisc_1(u1_struct_0(A_310)))
      | ~ m1_pre_topc(B_311,A_310)
      | ~ l1_pre_topc(A_310)
      | ~ r2_hidden(A_309,u1_struct_0(B_311)) ) ),
    inference(resolution,[status(thm)],[c_22,c_726])).

tff(c_738,plain,(
    ! [A_309] :
      ( m1_subset_1(k1_tarski(A_309),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ r2_hidden(A_309,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_62,c_736])).

tff(c_741,plain,(
    ! [A_309] :
      ( m1_subset_1(k1_tarski(A_309),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ r2_hidden(A_309,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_738])).

tff(c_1077,plain,(
    ! [A_388,B_389,C_390,E_391] :
      ( k8_relset_1(u1_struct_0(A_388),u1_struct_0(B_389),C_390,E_391) = k2_pre_topc(A_388,E_391)
      | ~ m1_subset_1(E_391,k1_zfmisc_1(u1_struct_0(A_388)))
      | ~ m1_subset_1(E_391,k1_zfmisc_1(u1_struct_0(B_389)))
      | ~ v3_borsuk_1(C_390,A_388,B_389)
      | ~ m1_subset_1(C_390,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_388),u1_struct_0(B_389))))
      | ~ v5_pre_topc(C_390,A_388,B_389)
      | ~ v1_funct_2(C_390,u1_struct_0(A_388),u1_struct_0(B_389))
      | ~ v1_funct_1(C_390)
      | ~ m1_pre_topc(B_389,A_388)
      | ~ v4_tex_2(B_389,A_388)
      | v2_struct_0(B_389)
      | ~ l1_pre_topc(A_388)
      | ~ v3_tdlat_3(A_388)
      | ~ v2_pre_topc(A_388)
      | v2_struct_0(A_388) ) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_1083,plain,(
    ! [B_389,C_390,A_309] :
      ( k8_relset_1(u1_struct_0('#skF_3'),u1_struct_0(B_389),C_390,k1_tarski(A_309)) = k2_pre_topc('#skF_3',k1_tarski(A_309))
      | ~ m1_subset_1(k1_tarski(A_309),k1_zfmisc_1(u1_struct_0(B_389)))
      | ~ v3_borsuk_1(C_390,'#skF_3',B_389)
      | ~ m1_subset_1(C_390,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_389))))
      | ~ v5_pre_topc(C_390,'#skF_3',B_389)
      | ~ v1_funct_2(C_390,u1_struct_0('#skF_3'),u1_struct_0(B_389))
      | ~ v1_funct_1(C_390)
      | ~ m1_pre_topc(B_389,'#skF_3')
      | ~ v4_tex_2(B_389,'#skF_3')
      | v2_struct_0(B_389)
      | ~ l1_pre_topc('#skF_3')
      | ~ v3_tdlat_3('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ r2_hidden(A_309,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_741,c_1077])).

tff(c_1093,plain,(
    ! [B_389,C_390,A_309] :
      ( k8_relset_1(u1_struct_0('#skF_3'),u1_struct_0(B_389),C_390,k1_tarski(A_309)) = k2_pre_topc('#skF_3',k1_tarski(A_309))
      | ~ m1_subset_1(k1_tarski(A_309),k1_zfmisc_1(u1_struct_0(B_389)))
      | ~ v3_borsuk_1(C_390,'#skF_3',B_389)
      | ~ m1_subset_1(C_390,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_389))))
      | ~ v5_pre_topc(C_390,'#skF_3',B_389)
      | ~ v1_funct_2(C_390,u1_struct_0('#skF_3'),u1_struct_0(B_389))
      | ~ v1_funct_1(C_390)
      | ~ m1_pre_topc(B_389,'#skF_3')
      | ~ v4_tex_2(B_389,'#skF_3')
      | v2_struct_0(B_389)
      | v2_struct_0('#skF_3')
      | ~ r2_hidden(A_309,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_68,c_1083])).

tff(c_1136,plain,(
    ! [B_395,C_396,A_397] :
      ( k8_relset_1(u1_struct_0('#skF_3'),u1_struct_0(B_395),C_396,k1_tarski(A_397)) = k2_pre_topc('#skF_3',k1_tarski(A_397))
      | ~ m1_subset_1(k1_tarski(A_397),k1_zfmisc_1(u1_struct_0(B_395)))
      | ~ v3_borsuk_1(C_396,'#skF_3',B_395)
      | ~ m1_subset_1(C_396,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_395))))
      | ~ v5_pre_topc(C_396,'#skF_3',B_395)
      | ~ v1_funct_2(C_396,u1_struct_0('#skF_3'),u1_struct_0(B_395))
      | ~ v1_funct_1(C_396)
      | ~ m1_pre_topc(B_395,'#skF_3')
      | ~ v4_tex_2(B_395,'#skF_3')
      | v2_struct_0(B_395)
      | ~ r2_hidden(A_397,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_1093])).

tff(c_1322,plain,(
    ! [B_427,C_428,A_429] :
      ( k8_relset_1(u1_struct_0('#skF_3'),u1_struct_0(B_427),C_428,k1_tarski(A_429)) = k2_pre_topc('#skF_3',k1_tarski(A_429))
      | ~ v3_borsuk_1(C_428,'#skF_3',B_427)
      | ~ m1_subset_1(C_428,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_427))))
      | ~ v5_pre_topc(C_428,'#skF_3',B_427)
      | ~ v1_funct_2(C_428,u1_struct_0('#skF_3'),u1_struct_0(B_427))
      | ~ v1_funct_1(C_428)
      | ~ m1_pre_topc(B_427,'#skF_3')
      | ~ v4_tex_2(B_427,'#skF_3')
      | v2_struct_0(B_427)
      | ~ r2_hidden(A_429,u1_struct_0('#skF_4'))
      | ~ r2_hidden(A_429,u1_struct_0(B_427)) ) ),
    inference(resolution,[status(thm)],[c_22,c_1136])).

tff(c_1327,plain,(
    ! [A_429] :
      ( k8_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5',k1_tarski(A_429)) = k2_pre_topc('#skF_3',k1_tarski(A_429))
      | ~ v3_borsuk_1('#skF_5','#skF_3','#skF_4')
      | ~ v5_pre_topc('#skF_5','#skF_3','#skF_4')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc('#skF_4','#skF_3')
      | ~ v4_tex_2('#skF_4','#skF_3')
      | v2_struct_0('#skF_4')
      | ~ r2_hidden(A_429,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_54,c_1322])).

tff(c_1331,plain,(
    ! [A_429] :
      ( k8_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5',k1_tarski(A_429)) = k2_pre_topc('#skF_3',k1_tarski(A_429))
      | v2_struct_0('#skF_4')
      | ~ r2_hidden(A_429,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_60,c_58,c_56,c_52,c_1327])).

tff(c_1333,plain,(
    ! [A_430] :
      ( k8_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5',k1_tarski(A_430)) = k2_pre_topc('#skF_3',k1_tarski(A_430))
      | ~ r2_hidden(A_430,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_1331])).

tff(c_46,plain,(
    '#skF_7' = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_48,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_75,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_48])).

tff(c_136,plain,
    ( k6_domain_1(u1_struct_0('#skF_3'),'#skF_6') = k1_tarski('#skF_6')
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_75,c_120])).

tff(c_541,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_136])).

tff(c_568,plain,(
    ! [B_247,A_248] :
      ( m1_subset_1(u1_struct_0(B_247),k1_zfmisc_1(u1_struct_0(A_248)))
      | ~ m1_pre_topc(B_247,A_248)
      | ~ l1_pre_topc(A_248) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_542,plain,(
    ! [C_240,A_241,B_242] :
      ( r2_hidden(C_240,A_241)
      | ~ r2_hidden(C_240,B_242)
      | ~ m1_subset_1(B_242,k1_zfmisc_1(A_241)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_549,plain,(
    ! [A_243,A_244] :
      ( r2_hidden('#skF_1'(A_243),A_244)
      | ~ m1_subset_1(A_243,k1_zfmisc_1(A_244))
      | v1_xboole_0(A_243) ) ),
    inference(resolution,[status(thm)],[c_4,c_542])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_556,plain,(
    ! [A_244,A_243] :
      ( ~ v1_xboole_0(A_244)
      | ~ m1_subset_1(A_243,k1_zfmisc_1(A_244))
      | v1_xboole_0(A_243) ) ),
    inference(resolution,[status(thm)],[c_549,c_2])).

tff(c_586,plain,(
    ! [A_253,B_254] :
      ( ~ v1_xboole_0(u1_struct_0(A_253))
      | v1_xboole_0(u1_struct_0(B_254))
      | ~ m1_pre_topc(B_254,A_253)
      | ~ l1_pre_topc(A_253) ) ),
    inference(resolution,[status(thm)],[c_568,c_556])).

tff(c_588,plain,(
    ! [B_254] :
      ( v1_xboole_0(u1_struct_0(B_254))
      | ~ m1_pre_topc(B_254,'#skF_3')
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_541,c_586])).

tff(c_601,plain,(
    ! [B_260] :
      ( v1_xboole_0(u1_struct_0(B_260))
      | ~ m1_pre_topc(B_260,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_588])).

tff(c_606,plain,(
    ~ m1_pre_topc('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_601,c_535])).

tff(c_611,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_606])).

tff(c_612,plain,(
    k6_domain_1(u1_struct_0('#skF_3'),'#skF_6') = k1_tarski('#skF_6') ),
    inference(splitRight,[status(thm)],[c_136])).

tff(c_534,plain,(
    k6_domain_1(u1_struct_0('#skF_4'),'#skF_6') = k1_tarski('#skF_6') ),
    inference(splitRight,[status(thm)],[c_135])).

tff(c_44,plain,(
    k8_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5',k6_domain_1(u1_struct_0('#skF_4'),'#skF_6')) != k2_pre_topc('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),'#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_76,plain,(
    k8_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5',k6_domain_1(u1_struct_0('#skF_4'),'#skF_6')) != k2_pre_topc('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),'#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44])).

tff(c_536,plain,(
    k8_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5',k1_tarski('#skF_6')) != k2_pre_topc('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),'#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_534,c_76])).

tff(c_663,plain,(
    k8_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5',k1_tarski('#skF_6')) != k2_pre_topc('#skF_3',k1_tarski('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_612,c_536])).

tff(c_1344,plain,(
    ~ r2_hidden('#skF_6',u1_struct_0('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1333,c_663])).

tff(c_1354,plain,
    ( v1_xboole_0(u1_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_24,c_1344])).

tff(c_1359,plain,(
    v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_1354])).

tff(c_1361,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_535,c_1359])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:36:34 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.27/1.74  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.27/1.75  
% 4.27/1.75  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.27/1.75  %$ v5_pre_topc > v3_borsuk_1 > v1_funct_2 > v4_tex_2 > v3_tex_2 > r2_hidden > m1_subset_1 > m1_pre_topc > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_pre_topc > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k8_relset_1 > k2_enumset1 > k1_enumset1 > k6_domain_1 > k2_zfmisc_1 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2
% 4.27/1.75  
% 4.27/1.75  %Foreground sorts:
% 4.27/1.75  
% 4.27/1.75  
% 4.27/1.75  %Background operators:
% 4.27/1.75  
% 4.27/1.75  
% 4.27/1.75  %Foreground operators:
% 4.27/1.75  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.27/1.75  tff(v3_borsuk_1, type, v3_borsuk_1: ($i * $i * $i) > $o).
% 4.27/1.75  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.27/1.75  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.27/1.75  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.27/1.75  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.27/1.75  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 4.27/1.75  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.27/1.75  tff(v4_tex_2, type, v4_tex_2: ($i * $i) > $o).
% 4.27/1.75  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.27/1.75  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.27/1.75  tff('#skF_7', type, '#skF_7': $i).
% 4.27/1.75  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 4.27/1.75  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.27/1.75  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.27/1.75  tff('#skF_5', type, '#skF_5': $i).
% 4.27/1.75  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 4.27/1.75  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.27/1.75  tff('#skF_6', type, '#skF_6': $i).
% 4.27/1.75  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.27/1.75  tff('#skF_3', type, '#skF_3': $i).
% 4.27/1.75  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.27/1.75  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.27/1.75  tff(v3_tdlat_3, type, v3_tdlat_3: $i > $o).
% 4.27/1.75  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 4.27/1.75  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.27/1.75  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.27/1.75  tff('#skF_4', type, '#skF_4': $i).
% 4.27/1.75  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.27/1.75  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.27/1.75  tff(v5_pre_topc, type, v5_pre_topc: ($i * $i * $i) > $o).
% 4.27/1.75  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 4.27/1.75  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.27/1.75  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 4.27/1.75  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.27/1.75  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.27/1.75  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 4.27/1.75  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.27/1.75  
% 4.60/1.77  tff(f_195, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v4_tex_2(B, A)) & m1_pre_topc(B, A)) => (![C]: ((((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & v5_pre_topc(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (v3_borsuk_1(C, A, B) => (![D]: (m1_subset_1(D, u1_struct_0(B)) => (![E]: (m1_subset_1(E, u1_struct_0(A)) => ((D = E) => (k8_relset_1(u1_struct_0(A), u1_struct_0(B), C, k6_domain_1(u1_struct_0(B), D)) = k2_pre_topc(A, k6_domain_1(u1_struct_0(A), E))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_tex_2)).
% 4.60/1.77  tff(f_79, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 4.60/1.77  tff(f_86, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 4.60/1.77  tff(f_103, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (v4_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => v3_tex_2(C, A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_tex_2)).
% 4.60/1.77  tff(f_118, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ~v3_tex_2(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_tex_2)).
% 4.60/1.77  tff(f_62, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 4.60/1.77  tff(f_56, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(k1_tarski(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_subset_1)).
% 4.60/1.77  tff(f_72, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B))) => m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_pre_topc)).
% 4.60/1.77  tff(f_156, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v4_tex_2(B, A)) & m1_pre_topc(B, A)) => (![C]: ((((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & v5_pre_topc(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (v3_borsuk_1(C, A, B) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => (![E]: (m1_subset_1(E, k1_zfmisc_1(u1_struct_0(A))) => ((D = E) => (k8_relset_1(u1_struct_0(A), u1_struct_0(B), C, D) = k2_pre_topc(A, E)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t76_tex_2)).
% 4.60/1.77  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 4.60/1.77  tff(f_52, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 4.60/1.77  tff(c_74, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_195])).
% 4.60/1.77  tff(c_68, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_195])).
% 4.60/1.77  tff(c_62, plain, (m1_pre_topc('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_195])).
% 4.60/1.77  tff(c_72, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_195])).
% 4.60/1.77  tff(c_64, plain, (v4_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_195])).
% 4.60/1.77  tff(c_50, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_195])).
% 4.60/1.77  tff(c_120, plain, (![A_136, B_137]: (k6_domain_1(A_136, B_137)=k1_tarski(B_137) | ~m1_subset_1(B_137, A_136) | v1_xboole_0(A_136))), inference(cnfTransformation, [status(thm)], [f_79])).
% 4.60/1.77  tff(c_135, plain, (k6_domain_1(u1_struct_0('#skF_4'), '#skF_6')=k1_tarski('#skF_6') | v1_xboole_0(u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_50, c_120])).
% 4.60/1.77  tff(c_137, plain, (v1_xboole_0(u1_struct_0('#skF_4'))), inference(splitLeft, [status(thm)], [c_135])).
% 4.60/1.77  tff(c_30, plain, (![B_52, A_50]: (m1_subset_1(u1_struct_0(B_52), k1_zfmisc_1(u1_struct_0(A_50))) | ~m1_pre_topc(B_52, A_50) | ~l1_pre_topc(A_50))), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.60/1.77  tff(c_483, plain, (![B_231, A_232]: (v3_tex_2(u1_struct_0(B_231), A_232) | ~m1_subset_1(u1_struct_0(B_231), k1_zfmisc_1(u1_struct_0(A_232))) | ~v4_tex_2(B_231, A_232) | ~m1_pre_topc(B_231, A_232) | ~l1_pre_topc(A_232) | v2_struct_0(A_232))), inference(cnfTransformation, [status(thm)], [f_103])).
% 4.60/1.77  tff(c_488, plain, (![B_233, A_234]: (v3_tex_2(u1_struct_0(B_233), A_234) | ~v4_tex_2(B_233, A_234) | v2_struct_0(A_234) | ~m1_pre_topc(B_233, A_234) | ~l1_pre_topc(A_234))), inference(resolution, [status(thm)], [c_30, c_483])).
% 4.60/1.77  tff(c_275, plain, (![B_189, A_190]: (~v3_tex_2(B_189, A_190) | ~m1_subset_1(B_189, k1_zfmisc_1(u1_struct_0(A_190))) | ~v1_xboole_0(B_189) | ~l1_pre_topc(A_190) | ~v2_pre_topc(A_190) | v2_struct_0(A_190))), inference(cnfTransformation, [status(thm)], [f_118])).
% 4.60/1.77  tff(c_283, plain, (![B_52, A_50]: (~v3_tex_2(u1_struct_0(B_52), A_50) | ~v1_xboole_0(u1_struct_0(B_52)) | ~v2_pre_topc(A_50) | v2_struct_0(A_50) | ~m1_pre_topc(B_52, A_50) | ~l1_pre_topc(A_50))), inference(resolution, [status(thm)], [c_30, c_275])).
% 4.60/1.77  tff(c_493, plain, (![B_235, A_236]: (~v1_xboole_0(u1_struct_0(B_235)) | ~v2_pre_topc(A_236) | ~v4_tex_2(B_235, A_236) | v2_struct_0(A_236) | ~m1_pre_topc(B_235, A_236) | ~l1_pre_topc(A_236))), inference(resolution, [status(thm)], [c_488, c_283])).
% 4.60/1.77  tff(c_520, plain, (![A_239]: (~v2_pre_topc(A_239) | ~v4_tex_2('#skF_4', A_239) | v2_struct_0(A_239) | ~m1_pre_topc('#skF_4', A_239) | ~l1_pre_topc(A_239))), inference(resolution, [status(thm)], [c_137, c_493])).
% 4.60/1.77  tff(c_527, plain, (~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_64, c_520])).
% 4.60/1.77  tff(c_531, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_62, c_72, c_527])).
% 4.60/1.77  tff(c_533, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_531])).
% 4.60/1.77  tff(c_535, plain, (~v1_xboole_0(u1_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_135])).
% 4.60/1.77  tff(c_24, plain, (![A_39, B_40]: (r2_hidden(A_39, B_40) | v1_xboole_0(B_40) | ~m1_subset_1(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.60/1.77  tff(c_66, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_195])).
% 4.60/1.77  tff(c_60, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_195])).
% 4.60/1.77  tff(c_58, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_195])).
% 4.60/1.77  tff(c_56, plain, (v5_pre_topc('#skF_5', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_195])).
% 4.60/1.77  tff(c_52, plain, (v3_borsuk_1('#skF_5', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_195])).
% 4.60/1.77  tff(c_54, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_195])).
% 4.60/1.77  tff(c_22, plain, (![A_37, B_38]: (m1_subset_1(k1_tarski(A_37), k1_zfmisc_1(B_38)) | ~r2_hidden(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.60/1.77  tff(c_70, plain, (v3_tdlat_3('#skF_3')), inference(cnfTransformation, [status(thm)], [f_195])).
% 4.60/1.77  tff(c_726, plain, (![C_302, A_303, B_304]: (m1_subset_1(C_302, k1_zfmisc_1(u1_struct_0(A_303))) | ~m1_subset_1(C_302, k1_zfmisc_1(u1_struct_0(B_304))) | ~m1_pre_topc(B_304, A_303) | ~l1_pre_topc(A_303))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.60/1.77  tff(c_736, plain, (![A_309, A_310, B_311]: (m1_subset_1(k1_tarski(A_309), k1_zfmisc_1(u1_struct_0(A_310))) | ~m1_pre_topc(B_311, A_310) | ~l1_pre_topc(A_310) | ~r2_hidden(A_309, u1_struct_0(B_311)))), inference(resolution, [status(thm)], [c_22, c_726])).
% 4.60/1.77  tff(c_738, plain, (![A_309]: (m1_subset_1(k1_tarski(A_309), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~r2_hidden(A_309, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_62, c_736])).
% 4.60/1.77  tff(c_741, plain, (![A_309]: (m1_subset_1(k1_tarski(A_309), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~r2_hidden(A_309, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_738])).
% 4.60/1.77  tff(c_1077, plain, (![A_388, B_389, C_390, E_391]: (k8_relset_1(u1_struct_0(A_388), u1_struct_0(B_389), C_390, E_391)=k2_pre_topc(A_388, E_391) | ~m1_subset_1(E_391, k1_zfmisc_1(u1_struct_0(A_388))) | ~m1_subset_1(E_391, k1_zfmisc_1(u1_struct_0(B_389))) | ~v3_borsuk_1(C_390, A_388, B_389) | ~m1_subset_1(C_390, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_388), u1_struct_0(B_389)))) | ~v5_pre_topc(C_390, A_388, B_389) | ~v1_funct_2(C_390, u1_struct_0(A_388), u1_struct_0(B_389)) | ~v1_funct_1(C_390) | ~m1_pre_topc(B_389, A_388) | ~v4_tex_2(B_389, A_388) | v2_struct_0(B_389) | ~l1_pre_topc(A_388) | ~v3_tdlat_3(A_388) | ~v2_pre_topc(A_388) | v2_struct_0(A_388))), inference(cnfTransformation, [status(thm)], [f_156])).
% 4.60/1.77  tff(c_1083, plain, (![B_389, C_390, A_309]: (k8_relset_1(u1_struct_0('#skF_3'), u1_struct_0(B_389), C_390, k1_tarski(A_309))=k2_pre_topc('#skF_3', k1_tarski(A_309)) | ~m1_subset_1(k1_tarski(A_309), k1_zfmisc_1(u1_struct_0(B_389))) | ~v3_borsuk_1(C_390, '#skF_3', B_389) | ~m1_subset_1(C_390, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_389)))) | ~v5_pre_topc(C_390, '#skF_3', B_389) | ~v1_funct_2(C_390, u1_struct_0('#skF_3'), u1_struct_0(B_389)) | ~v1_funct_1(C_390) | ~m1_pre_topc(B_389, '#skF_3') | ~v4_tex_2(B_389, '#skF_3') | v2_struct_0(B_389) | ~l1_pre_topc('#skF_3') | ~v3_tdlat_3('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~r2_hidden(A_309, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_741, c_1077])).
% 4.60/1.77  tff(c_1093, plain, (![B_389, C_390, A_309]: (k8_relset_1(u1_struct_0('#skF_3'), u1_struct_0(B_389), C_390, k1_tarski(A_309))=k2_pre_topc('#skF_3', k1_tarski(A_309)) | ~m1_subset_1(k1_tarski(A_309), k1_zfmisc_1(u1_struct_0(B_389))) | ~v3_borsuk_1(C_390, '#skF_3', B_389) | ~m1_subset_1(C_390, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_389)))) | ~v5_pre_topc(C_390, '#skF_3', B_389) | ~v1_funct_2(C_390, u1_struct_0('#skF_3'), u1_struct_0(B_389)) | ~v1_funct_1(C_390) | ~m1_pre_topc(B_389, '#skF_3') | ~v4_tex_2(B_389, '#skF_3') | v2_struct_0(B_389) | v2_struct_0('#skF_3') | ~r2_hidden(A_309, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_68, c_1083])).
% 4.60/1.77  tff(c_1136, plain, (![B_395, C_396, A_397]: (k8_relset_1(u1_struct_0('#skF_3'), u1_struct_0(B_395), C_396, k1_tarski(A_397))=k2_pre_topc('#skF_3', k1_tarski(A_397)) | ~m1_subset_1(k1_tarski(A_397), k1_zfmisc_1(u1_struct_0(B_395))) | ~v3_borsuk_1(C_396, '#skF_3', B_395) | ~m1_subset_1(C_396, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_395)))) | ~v5_pre_topc(C_396, '#skF_3', B_395) | ~v1_funct_2(C_396, u1_struct_0('#skF_3'), u1_struct_0(B_395)) | ~v1_funct_1(C_396) | ~m1_pre_topc(B_395, '#skF_3') | ~v4_tex_2(B_395, '#skF_3') | v2_struct_0(B_395) | ~r2_hidden(A_397, u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_74, c_1093])).
% 4.60/1.77  tff(c_1322, plain, (![B_427, C_428, A_429]: (k8_relset_1(u1_struct_0('#skF_3'), u1_struct_0(B_427), C_428, k1_tarski(A_429))=k2_pre_topc('#skF_3', k1_tarski(A_429)) | ~v3_borsuk_1(C_428, '#skF_3', B_427) | ~m1_subset_1(C_428, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_427)))) | ~v5_pre_topc(C_428, '#skF_3', B_427) | ~v1_funct_2(C_428, u1_struct_0('#skF_3'), u1_struct_0(B_427)) | ~v1_funct_1(C_428) | ~m1_pre_topc(B_427, '#skF_3') | ~v4_tex_2(B_427, '#skF_3') | v2_struct_0(B_427) | ~r2_hidden(A_429, u1_struct_0('#skF_4')) | ~r2_hidden(A_429, u1_struct_0(B_427)))), inference(resolution, [status(thm)], [c_22, c_1136])).
% 4.60/1.77  tff(c_1327, plain, (![A_429]: (k8_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5', k1_tarski(A_429))=k2_pre_topc('#skF_3', k1_tarski(A_429)) | ~v3_borsuk_1('#skF_5', '#skF_3', '#skF_4') | ~v5_pre_topc('#skF_5', '#skF_3', '#skF_4') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_4')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_3') | ~v4_tex_2('#skF_4', '#skF_3') | v2_struct_0('#skF_4') | ~r2_hidden(A_429, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_54, c_1322])).
% 4.60/1.77  tff(c_1331, plain, (![A_429]: (k8_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5', k1_tarski(A_429))=k2_pre_topc('#skF_3', k1_tarski(A_429)) | v2_struct_0('#skF_4') | ~r2_hidden(A_429, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_60, c_58, c_56, c_52, c_1327])).
% 4.60/1.77  tff(c_1333, plain, (![A_430]: (k8_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5', k1_tarski(A_430))=k2_pre_topc('#skF_3', k1_tarski(A_430)) | ~r2_hidden(A_430, u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_66, c_1331])).
% 4.60/1.77  tff(c_46, plain, ('#skF_7'='#skF_6'), inference(cnfTransformation, [status(thm)], [f_195])).
% 4.60/1.77  tff(c_48, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_195])).
% 4.60/1.77  tff(c_75, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_48])).
% 4.60/1.77  tff(c_136, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_6')=k1_tarski('#skF_6') | v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_75, c_120])).
% 4.60/1.77  tff(c_541, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_136])).
% 4.60/1.77  tff(c_568, plain, (![B_247, A_248]: (m1_subset_1(u1_struct_0(B_247), k1_zfmisc_1(u1_struct_0(A_248))) | ~m1_pre_topc(B_247, A_248) | ~l1_pre_topc(A_248))), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.60/1.77  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.60/1.77  tff(c_542, plain, (![C_240, A_241, B_242]: (r2_hidden(C_240, A_241) | ~r2_hidden(C_240, B_242) | ~m1_subset_1(B_242, k1_zfmisc_1(A_241)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.60/1.77  tff(c_549, plain, (![A_243, A_244]: (r2_hidden('#skF_1'(A_243), A_244) | ~m1_subset_1(A_243, k1_zfmisc_1(A_244)) | v1_xboole_0(A_243))), inference(resolution, [status(thm)], [c_4, c_542])).
% 4.60/1.77  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.60/1.77  tff(c_556, plain, (![A_244, A_243]: (~v1_xboole_0(A_244) | ~m1_subset_1(A_243, k1_zfmisc_1(A_244)) | v1_xboole_0(A_243))), inference(resolution, [status(thm)], [c_549, c_2])).
% 4.60/1.77  tff(c_586, plain, (![A_253, B_254]: (~v1_xboole_0(u1_struct_0(A_253)) | v1_xboole_0(u1_struct_0(B_254)) | ~m1_pre_topc(B_254, A_253) | ~l1_pre_topc(A_253))), inference(resolution, [status(thm)], [c_568, c_556])).
% 4.60/1.77  tff(c_588, plain, (![B_254]: (v1_xboole_0(u1_struct_0(B_254)) | ~m1_pre_topc(B_254, '#skF_3') | ~l1_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_541, c_586])).
% 4.60/1.77  tff(c_601, plain, (![B_260]: (v1_xboole_0(u1_struct_0(B_260)) | ~m1_pre_topc(B_260, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_588])).
% 4.60/1.77  tff(c_606, plain, (~m1_pre_topc('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_601, c_535])).
% 4.60/1.77  tff(c_611, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_62, c_606])).
% 4.60/1.77  tff(c_612, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_6')=k1_tarski('#skF_6')), inference(splitRight, [status(thm)], [c_136])).
% 4.60/1.77  tff(c_534, plain, (k6_domain_1(u1_struct_0('#skF_4'), '#skF_6')=k1_tarski('#skF_6')), inference(splitRight, [status(thm)], [c_135])).
% 4.60/1.77  tff(c_44, plain, (k8_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5', k6_domain_1(u1_struct_0('#skF_4'), '#skF_6'))!=k2_pre_topc('#skF_3', k6_domain_1(u1_struct_0('#skF_3'), '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_195])).
% 4.60/1.77  tff(c_76, plain, (k8_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5', k6_domain_1(u1_struct_0('#skF_4'), '#skF_6'))!=k2_pre_topc('#skF_3', k6_domain_1(u1_struct_0('#skF_3'), '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44])).
% 4.60/1.77  tff(c_536, plain, (k8_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5', k1_tarski('#skF_6'))!=k2_pre_topc('#skF_3', k6_domain_1(u1_struct_0('#skF_3'), '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_534, c_76])).
% 4.60/1.77  tff(c_663, plain, (k8_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5', k1_tarski('#skF_6'))!=k2_pre_topc('#skF_3', k1_tarski('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_612, c_536])).
% 4.60/1.77  tff(c_1344, plain, (~r2_hidden('#skF_6', u1_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1333, c_663])).
% 4.60/1.77  tff(c_1354, plain, (v1_xboole_0(u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_24, c_1344])).
% 4.60/1.77  tff(c_1359, plain, (v1_xboole_0(u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_1354])).
% 4.60/1.77  tff(c_1361, plain, $false, inference(negUnitSimplification, [status(thm)], [c_535, c_1359])).
% 4.60/1.77  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.60/1.77  
% 4.60/1.77  Inference rules
% 4.60/1.77  ----------------------
% 4.60/1.77  #Ref     : 0
% 4.60/1.77  #Sup     : 294
% 4.60/1.77  #Fact    : 0
% 4.60/1.77  #Define  : 0
% 4.60/1.77  #Split   : 20
% 4.60/1.77  #Chain   : 0
% 4.60/1.77  #Close   : 0
% 4.60/1.77  
% 4.60/1.77  Ordering : KBO
% 4.60/1.77  
% 4.60/1.77  Simplification rules
% 4.60/1.77  ----------------------
% 4.60/1.77  #Subsume      : 38
% 4.60/1.77  #Demod        : 43
% 4.60/1.77  #Tautology    : 54
% 4.60/1.77  #SimpNegUnit  : 16
% 4.60/1.77  #BackRed      : 1
% 4.60/1.77  
% 4.60/1.77  #Partial instantiations: 0
% 4.60/1.77  #Strategies tried      : 1
% 4.60/1.77  
% 4.60/1.77  Timing (in seconds)
% 4.60/1.77  ----------------------
% 4.68/1.78  Preprocessing        : 0.37
% 4.68/1.78  Parsing              : 0.20
% 4.68/1.78  CNF conversion       : 0.03
% 4.68/1.78  Main loop            : 0.62
% 4.68/1.78  Inferencing          : 0.22
% 4.68/1.78  Reduction            : 0.16
% 4.68/1.78  Demodulation         : 0.11
% 4.68/1.78  BG Simplification    : 0.03
% 4.68/1.78  Subsumption          : 0.16
% 4.68/1.78  Abstraction          : 0.03
% 4.68/1.78  MUC search           : 0.00
% 4.68/1.78  Cooper               : 0.00
% 4.68/1.78  Total                : 1.04
% 4.68/1.78  Index Insertion      : 0.00
% 4.68/1.78  Index Deletion       : 0.00
% 4.68/1.78  Index Matching       : 0.00
% 4.68/1.78  BG Taut test         : 0.00
%------------------------------------------------------------------------------
