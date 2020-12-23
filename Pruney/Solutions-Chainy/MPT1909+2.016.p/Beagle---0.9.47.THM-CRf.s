%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:39 EST 2020

% Result     : Theorem 4.68s
% Output     : CNFRefutation 5.02s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 215 expanded)
%              Number of leaves         :   41 (  95 expanded)
%              Depth                    :   15
%              Number of atoms          :  298 (1069 expanded)
%              Number of equality atoms :   24 ( 130 expanded)
%              Maximal formula depth    :   20 (   5 average)
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

tff(f_177,negated_conjecture,(
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

tff(f_61,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_68,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_85,axiom,(
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

tff(f_100,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( v1_xboole_0(B)
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
         => ~ v3_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_tex_2)).

tff(f_44,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(k1_tarski(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_subset_1)).

tff(f_54,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(B)))
             => m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_pre_topc)).

tff(f_138,axiom,(
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

tff(f_38,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

tff(c_58,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_52,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_46,plain,(
    m1_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_56,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_48,plain,(
    v4_tex_2('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_30,plain,(
    '#skF_5' = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_34,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_59,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_34])).

tff(c_90,plain,(
    ! [A_100,B_101] :
      ( k6_domain_1(A_100,B_101) = k1_tarski(B_101)
      | ~ m1_subset_1(B_101,A_100)
      | v1_xboole_0(A_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_106,plain,
    ( k6_domain_1(u1_struct_0('#skF_3'),'#skF_6') = k1_tarski('#skF_6')
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_59,c_90])).

tff(c_333,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_106])).

tff(c_14,plain,(
    ! [B_20,A_18] :
      ( m1_subset_1(u1_struct_0(B_20),k1_zfmisc_1(u1_struct_0(A_18)))
      | ~ m1_pre_topc(B_20,A_18)
      | ~ l1_pre_topc(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_457,plain,(
    ! [B_188,A_189] :
      ( v3_tex_2(u1_struct_0(B_188),A_189)
      | ~ m1_subset_1(u1_struct_0(B_188),k1_zfmisc_1(u1_struct_0(A_189)))
      | ~ v4_tex_2(B_188,A_189)
      | ~ m1_pre_topc(B_188,A_189)
      | ~ l1_pre_topc(A_189)
      | v2_struct_0(A_189) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_482,plain,(
    ! [B_194,A_195] :
      ( v3_tex_2(u1_struct_0(B_194),A_195)
      | ~ v4_tex_2(B_194,A_195)
      | v2_struct_0(A_195)
      | ~ m1_pre_topc(B_194,A_195)
      | ~ l1_pre_topc(A_195) ) ),
    inference(resolution,[status(thm)],[c_14,c_457])).

tff(c_396,plain,(
    ! [B_172,A_173] :
      ( ~ v3_tex_2(B_172,A_173)
      | ~ m1_subset_1(B_172,k1_zfmisc_1(u1_struct_0(A_173)))
      | ~ v1_xboole_0(B_172)
      | ~ l1_pre_topc(A_173)
      | ~ v2_pre_topc(A_173)
      | v2_struct_0(A_173) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_415,plain,(
    ! [B_20,A_18] :
      ( ~ v3_tex_2(u1_struct_0(B_20),A_18)
      | ~ v1_xboole_0(u1_struct_0(B_20))
      | ~ v2_pre_topc(A_18)
      | v2_struct_0(A_18)
      | ~ m1_pre_topc(B_20,A_18)
      | ~ l1_pre_topc(A_18) ) ),
    inference(resolution,[status(thm)],[c_14,c_396])).

tff(c_487,plain,(
    ! [B_196,A_197] :
      ( ~ v1_xboole_0(u1_struct_0(B_196))
      | ~ v2_pre_topc(A_197)
      | ~ v4_tex_2(B_196,A_197)
      | v2_struct_0(A_197)
      | ~ m1_pre_topc(B_196,A_197)
      | ~ l1_pre_topc(A_197) ) ),
    inference(resolution,[status(thm)],[c_482,c_415])).

tff(c_491,plain,(
    ! [A_198] :
      ( ~ v2_pre_topc(A_198)
      | ~ v4_tex_2('#skF_3',A_198)
      | v2_struct_0(A_198)
      | ~ m1_pre_topc('#skF_3',A_198)
      | ~ l1_pre_topc(A_198) ) ),
    inference(resolution,[status(thm)],[c_333,c_487])).

tff(c_498,plain,
    ( ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_491])).

tff(c_502,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_46,c_56,c_498])).

tff(c_504,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_502])).

tff(c_506,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_106])).

tff(c_8,plain,(
    ! [A_7,B_8] :
      ( r2_hidden(A_7,B_8)
      | v1_xboole_0(B_8)
      | ~ m1_subset_1(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_50,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_44,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_42,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_40,plain,(
    v5_pre_topc('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_36,plain,(
    v3_borsuk_1('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_38,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_4,plain,(
    ! [A_2,B_3] :
      ( m1_subset_1(k1_tarski(A_2),k1_zfmisc_1(B_3))
      | ~ r2_hidden(A_2,B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_54,plain,(
    v3_tdlat_3('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_525,plain,(
    ! [C_207,A_208,B_209] :
      ( m1_subset_1(C_207,k1_zfmisc_1(u1_struct_0(A_208)))
      | ~ m1_subset_1(C_207,k1_zfmisc_1(u1_struct_0(B_209)))
      | ~ m1_pre_topc(B_209,A_208)
      | ~ l1_pre_topc(A_208) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_533,plain,(
    ! [A_210,A_211,B_212] :
      ( m1_subset_1(k1_tarski(A_210),k1_zfmisc_1(u1_struct_0(A_211)))
      | ~ m1_pre_topc(B_212,A_211)
      | ~ l1_pre_topc(A_211)
      | ~ r2_hidden(A_210,u1_struct_0(B_212)) ) ),
    inference(resolution,[status(thm)],[c_4,c_525])).

tff(c_535,plain,(
    ! [A_210] :
      ( m1_subset_1(k1_tarski(A_210),k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ r2_hidden(A_210,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_46,c_533])).

tff(c_538,plain,(
    ! [A_210] :
      ( m1_subset_1(k1_tarski(A_210),k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ r2_hidden(A_210,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_535])).

tff(c_677,plain,(
    ! [A_252,B_253,C_254,E_255] :
      ( k8_relset_1(u1_struct_0(A_252),u1_struct_0(B_253),C_254,E_255) = k2_pre_topc(A_252,E_255)
      | ~ m1_subset_1(E_255,k1_zfmisc_1(u1_struct_0(A_252)))
      | ~ m1_subset_1(E_255,k1_zfmisc_1(u1_struct_0(B_253)))
      | ~ v3_borsuk_1(C_254,A_252,B_253)
      | ~ m1_subset_1(C_254,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_252),u1_struct_0(B_253))))
      | ~ v5_pre_topc(C_254,A_252,B_253)
      | ~ v1_funct_2(C_254,u1_struct_0(A_252),u1_struct_0(B_253))
      | ~ v1_funct_1(C_254)
      | ~ m1_pre_topc(B_253,A_252)
      | ~ v4_tex_2(B_253,A_252)
      | v2_struct_0(B_253)
      | ~ l1_pre_topc(A_252)
      | ~ v3_tdlat_3(A_252)
      | ~ v2_pre_topc(A_252)
      | v2_struct_0(A_252) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_685,plain,(
    ! [B_253,C_254,A_210] :
      ( k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0(B_253),C_254,k1_tarski(A_210)) = k2_pre_topc('#skF_2',k1_tarski(A_210))
      | ~ m1_subset_1(k1_tarski(A_210),k1_zfmisc_1(u1_struct_0(B_253)))
      | ~ v3_borsuk_1(C_254,'#skF_2',B_253)
      | ~ m1_subset_1(C_254,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0(B_253))))
      | ~ v5_pre_topc(C_254,'#skF_2',B_253)
      | ~ v1_funct_2(C_254,u1_struct_0('#skF_2'),u1_struct_0(B_253))
      | ~ v1_funct_1(C_254)
      | ~ m1_pre_topc(B_253,'#skF_2')
      | ~ v4_tex_2(B_253,'#skF_2')
      | v2_struct_0(B_253)
      | ~ l1_pre_topc('#skF_2')
      | ~ v3_tdlat_3('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ r2_hidden(A_210,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_538,c_677])).

tff(c_696,plain,(
    ! [B_253,C_254,A_210] :
      ( k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0(B_253),C_254,k1_tarski(A_210)) = k2_pre_topc('#skF_2',k1_tarski(A_210))
      | ~ m1_subset_1(k1_tarski(A_210),k1_zfmisc_1(u1_struct_0(B_253)))
      | ~ v3_borsuk_1(C_254,'#skF_2',B_253)
      | ~ m1_subset_1(C_254,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0(B_253))))
      | ~ v5_pre_topc(C_254,'#skF_2',B_253)
      | ~ v1_funct_2(C_254,u1_struct_0('#skF_2'),u1_struct_0(B_253))
      | ~ v1_funct_1(C_254)
      | ~ m1_pre_topc(B_253,'#skF_2')
      | ~ v4_tex_2(B_253,'#skF_2')
      | v2_struct_0(B_253)
      | v2_struct_0('#skF_2')
      | ~ r2_hidden(A_210,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_685])).

tff(c_716,plain,(
    ! [B_265,C_266,A_267] :
      ( k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0(B_265),C_266,k1_tarski(A_267)) = k2_pre_topc('#skF_2',k1_tarski(A_267))
      | ~ m1_subset_1(k1_tarski(A_267),k1_zfmisc_1(u1_struct_0(B_265)))
      | ~ v3_borsuk_1(C_266,'#skF_2',B_265)
      | ~ m1_subset_1(C_266,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0(B_265))))
      | ~ v5_pre_topc(C_266,'#skF_2',B_265)
      | ~ v1_funct_2(C_266,u1_struct_0('#skF_2'),u1_struct_0(B_265))
      | ~ v1_funct_1(C_266)
      | ~ m1_pre_topc(B_265,'#skF_2')
      | ~ v4_tex_2(B_265,'#skF_2')
      | v2_struct_0(B_265)
      | ~ r2_hidden(A_267,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_696])).

tff(c_760,plain,(
    ! [B_275,C_276,A_277] :
      ( k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0(B_275),C_276,k1_tarski(A_277)) = k2_pre_topc('#skF_2',k1_tarski(A_277))
      | ~ v3_borsuk_1(C_276,'#skF_2',B_275)
      | ~ m1_subset_1(C_276,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0(B_275))))
      | ~ v5_pre_topc(C_276,'#skF_2',B_275)
      | ~ v1_funct_2(C_276,u1_struct_0('#skF_2'),u1_struct_0(B_275))
      | ~ v1_funct_1(C_276)
      | ~ m1_pre_topc(B_275,'#skF_2')
      | ~ v4_tex_2(B_275,'#skF_2')
      | v2_struct_0(B_275)
      | ~ r2_hidden(A_277,u1_struct_0('#skF_3'))
      | ~ r2_hidden(A_277,u1_struct_0(B_275)) ) ),
    inference(resolution,[status(thm)],[c_4,c_716])).

tff(c_762,plain,(
    ! [A_277] :
      ( k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4',k1_tarski(A_277)) = k2_pre_topc('#skF_2',k1_tarski(A_277))
      | ~ v3_borsuk_1('#skF_4','#skF_2','#skF_3')
      | ~ v5_pre_topc('#skF_4','#skF_2','#skF_3')
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_4')
      | ~ m1_pre_topc('#skF_3','#skF_2')
      | ~ v4_tex_2('#skF_3','#skF_2')
      | v2_struct_0('#skF_3')
      | ~ r2_hidden(A_277,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_38,c_760])).

tff(c_768,plain,(
    ! [A_277] :
      ( k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4',k1_tarski(A_277)) = k2_pre_topc('#skF_2',k1_tarski(A_277))
      | v2_struct_0('#skF_3')
      | ~ r2_hidden(A_277,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_40,c_36,c_762])).

tff(c_771,plain,(
    ! [A_278] :
      ( k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4',k1_tarski(A_278)) = k2_pre_topc('#skF_2',k1_tarski(A_278))
      | ~ r2_hidden(A_278,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_768])).

tff(c_505,plain,(
    k6_domain_1(u1_struct_0('#skF_3'),'#skF_6') = k1_tarski('#skF_6') ),
    inference(splitRight,[status(thm)],[c_106])).

tff(c_32,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_105,plain,
    ( k6_domain_1(u1_struct_0('#skF_2'),'#skF_6') = k1_tarski('#skF_6')
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_32,c_90])).

tff(c_107,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_105])).

tff(c_108,plain,(
    ! [B_102,A_103] :
      ( m1_subset_1(u1_struct_0(B_102),k1_zfmisc_1(u1_struct_0(A_103)))
      | ~ m1_pre_topc(B_102,A_103)
      | ~ l1_pre_topc(A_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_6,plain,(
    ! [B_6,A_4] :
      ( v1_xboole_0(B_6)
      | ~ m1_subset_1(B_6,k1_zfmisc_1(A_4))
      | ~ v1_xboole_0(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_301,plain,(
    ! [B_149,A_150] :
      ( v1_xboole_0(u1_struct_0(B_149))
      | ~ v1_xboole_0(u1_struct_0(A_150))
      | ~ m1_pre_topc(B_149,A_150)
      | ~ l1_pre_topc(A_150) ) ),
    inference(resolution,[status(thm)],[c_108,c_6])).

tff(c_303,plain,(
    ! [B_149] :
      ( v1_xboole_0(u1_struct_0(B_149))
      | ~ m1_pre_topc(B_149,'#skF_2')
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_107,c_301])).

tff(c_307,plain,(
    ! [B_151] :
      ( v1_xboole_0(u1_struct_0(B_151))
      | ~ m1_pre_topc(B_151,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_303])).

tff(c_117,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_106])).

tff(c_260,plain,(
    ! [B_142,A_143] :
      ( v3_tex_2(u1_struct_0(B_142),A_143)
      | ~ m1_subset_1(u1_struct_0(B_142),k1_zfmisc_1(u1_struct_0(A_143)))
      | ~ v4_tex_2(B_142,A_143)
      | ~ m1_pre_topc(B_142,A_143)
      | ~ l1_pre_topc(A_143)
      | v2_struct_0(A_143) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_265,plain,(
    ! [B_144,A_145] :
      ( v3_tex_2(u1_struct_0(B_144),A_145)
      | ~ v4_tex_2(B_144,A_145)
      | v2_struct_0(A_145)
      | ~ m1_pre_topc(B_144,A_145)
      | ~ l1_pre_topc(A_145) ) ),
    inference(resolution,[status(thm)],[c_14,c_260])).

tff(c_197,plain,(
    ! [B_125,A_126] :
      ( ~ v3_tex_2(B_125,A_126)
      | ~ m1_subset_1(B_125,k1_zfmisc_1(u1_struct_0(A_126)))
      | ~ v1_xboole_0(B_125)
      | ~ l1_pre_topc(A_126)
      | ~ v2_pre_topc(A_126)
      | v2_struct_0(A_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_216,plain,(
    ! [B_20,A_18] :
      ( ~ v3_tex_2(u1_struct_0(B_20),A_18)
      | ~ v1_xboole_0(u1_struct_0(B_20))
      | ~ v2_pre_topc(A_18)
      | v2_struct_0(A_18)
      | ~ m1_pre_topc(B_20,A_18)
      | ~ l1_pre_topc(A_18) ) ),
    inference(resolution,[status(thm)],[c_14,c_197])).

tff(c_270,plain,(
    ! [B_146,A_147] :
      ( ~ v1_xboole_0(u1_struct_0(B_146))
      | ~ v2_pre_topc(A_147)
      | ~ v4_tex_2(B_146,A_147)
      | v2_struct_0(A_147)
      | ~ m1_pre_topc(B_146,A_147)
      | ~ l1_pre_topc(A_147) ) ),
    inference(resolution,[status(thm)],[c_265,c_216])).

tff(c_280,plain,(
    ! [A_148] :
      ( ~ v2_pre_topc(A_148)
      | ~ v4_tex_2('#skF_3',A_148)
      | v2_struct_0(A_148)
      | ~ m1_pre_topc('#skF_3',A_148)
      | ~ l1_pre_topc(A_148) ) ),
    inference(resolution,[status(thm)],[c_117,c_270])).

tff(c_287,plain,
    ( ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_280])).

tff(c_291,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_46,c_56,c_287])).

tff(c_293,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_291])).

tff(c_295,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_106])).

tff(c_312,plain,(
    ~ m1_pre_topc('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_307,c_295])).

tff(c_317,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_312])).

tff(c_318,plain,(
    k6_domain_1(u1_struct_0('#skF_2'),'#skF_6') = k1_tarski('#skF_6') ),
    inference(splitRight,[status(thm)],[c_105])).

tff(c_28,plain,(
    k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4',k6_domain_1(u1_struct_0('#skF_3'),'#skF_5')) != k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_60,plain,(
    k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4',k6_domain_1(u1_struct_0('#skF_3'),'#skF_6')) != k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28])).

tff(c_507,plain,(
    k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4',k6_domain_1(u1_struct_0('#skF_3'),'#skF_6')) != k2_pre_topc('#skF_2',k1_tarski('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_318,c_60])).

tff(c_508,plain,(
    k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4',k1_tarski('#skF_6')) != k2_pre_topc('#skF_2',k1_tarski('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_505,c_507])).

tff(c_782,plain,(
    ~ r2_hidden('#skF_6',u1_struct_0('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_771,c_508])).

tff(c_786,plain,
    ( v1_xboole_0(u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_8,c_782])).

tff(c_789,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_786])).

tff(c_791,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_506,c_789])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 18:41:50 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.68/2.21  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.02/2.22  
% 5.02/2.22  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.02/2.22  %$ v5_pre_topc > v3_borsuk_1 > v1_funct_2 > v4_tex_2 > v3_tex_2 > r2_hidden > m1_subset_1 > m1_pre_topc > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_pre_topc > k8_relset_1 > k6_domain_1 > k2_zfmisc_1 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 5.02/2.22  
% 5.02/2.22  %Foreground sorts:
% 5.02/2.22  
% 5.02/2.22  
% 5.02/2.22  %Background operators:
% 5.02/2.22  
% 5.02/2.22  
% 5.02/2.22  %Foreground operators:
% 5.02/2.22  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 5.02/2.22  tff(v3_borsuk_1, type, v3_borsuk_1: ($i * $i * $i) > $o).
% 5.02/2.22  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.02/2.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.02/2.22  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.02/2.22  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.02/2.22  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 5.02/2.22  tff(v4_tex_2, type, v4_tex_2: ($i * $i) > $o).
% 5.02/2.22  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 5.02/2.22  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 5.02/2.22  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.02/2.22  tff('#skF_5', type, '#skF_5': $i).
% 5.02/2.22  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 5.02/2.23  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.02/2.23  tff('#skF_6', type, '#skF_6': $i).
% 5.02/2.23  tff('#skF_2', type, '#skF_2': $i).
% 5.02/2.23  tff('#skF_3', type, '#skF_3': $i).
% 5.02/2.23  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.02/2.23  tff(v3_tdlat_3, type, v3_tdlat_3: $i > $o).
% 5.02/2.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.02/2.23  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.02/2.23  tff('#skF_4', type, '#skF_4': $i).
% 5.02/2.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.02/2.23  tff(v5_pre_topc, type, v5_pre_topc: ($i * $i * $i) > $o).
% 5.02/2.23  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 5.02/2.23  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 5.02/2.23  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.02/2.23  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.02/2.23  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.02/2.23  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 5.02/2.23  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.02/2.23  
% 5.02/2.26  tff(f_177, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v4_tex_2(B, A)) & m1_pre_topc(B, A)) => (![C]: ((((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & v5_pre_topc(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (v3_borsuk_1(C, A, B) => (![D]: (m1_subset_1(D, u1_struct_0(B)) => (![E]: (m1_subset_1(E, u1_struct_0(A)) => ((D = E) => (k8_relset_1(u1_struct_0(A), u1_struct_0(B), C, k6_domain_1(u1_struct_0(B), D)) = k2_pre_topc(A, k6_domain_1(u1_struct_0(A), E))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_tex_2)).
% 5.02/2.26  tff(f_61, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 5.02/2.26  tff(f_68, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 5.02/2.26  tff(f_85, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (v4_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => v3_tex_2(C, A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_tex_2)).
% 5.02/2.26  tff(f_100, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ~v3_tex_2(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_tex_2)).
% 5.02/2.26  tff(f_44, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 5.02/2.26  tff(f_31, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(k1_tarski(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_subset_1)).
% 5.02/2.26  tff(f_54, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B))) => m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_pre_topc)).
% 5.02/2.26  tff(f_138, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v4_tex_2(B, A)) & m1_pre_topc(B, A)) => (![C]: ((((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & v5_pre_topc(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (v3_borsuk_1(C, A, B) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => (![E]: (m1_subset_1(E, k1_zfmisc_1(u1_struct_0(A))) => ((D = E) => (k8_relset_1(u1_struct_0(A), u1_struct_0(B), C, D) = k2_pre_topc(A, E)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t76_tex_2)).
% 5.02/2.26  tff(f_38, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 5.02/2.26  tff(c_58, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_177])).
% 5.02/2.26  tff(c_52, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_177])).
% 5.02/2.26  tff(c_46, plain, (m1_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_177])).
% 5.02/2.26  tff(c_56, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_177])).
% 5.02/2.26  tff(c_48, plain, (v4_tex_2('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_177])).
% 5.02/2.26  tff(c_30, plain, ('#skF_5'='#skF_6'), inference(cnfTransformation, [status(thm)], [f_177])).
% 5.02/2.26  tff(c_34, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_177])).
% 5.02/2.26  tff(c_59, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_34])).
% 5.02/2.26  tff(c_90, plain, (![A_100, B_101]: (k6_domain_1(A_100, B_101)=k1_tarski(B_101) | ~m1_subset_1(B_101, A_100) | v1_xboole_0(A_100))), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.02/2.26  tff(c_106, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_6')=k1_tarski('#skF_6') | v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_59, c_90])).
% 5.02/2.26  tff(c_333, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_106])).
% 5.02/2.26  tff(c_14, plain, (![B_20, A_18]: (m1_subset_1(u1_struct_0(B_20), k1_zfmisc_1(u1_struct_0(A_18))) | ~m1_pre_topc(B_20, A_18) | ~l1_pre_topc(A_18))), inference(cnfTransformation, [status(thm)], [f_68])).
% 5.02/2.26  tff(c_457, plain, (![B_188, A_189]: (v3_tex_2(u1_struct_0(B_188), A_189) | ~m1_subset_1(u1_struct_0(B_188), k1_zfmisc_1(u1_struct_0(A_189))) | ~v4_tex_2(B_188, A_189) | ~m1_pre_topc(B_188, A_189) | ~l1_pre_topc(A_189) | v2_struct_0(A_189))), inference(cnfTransformation, [status(thm)], [f_85])).
% 5.02/2.26  tff(c_482, plain, (![B_194, A_195]: (v3_tex_2(u1_struct_0(B_194), A_195) | ~v4_tex_2(B_194, A_195) | v2_struct_0(A_195) | ~m1_pre_topc(B_194, A_195) | ~l1_pre_topc(A_195))), inference(resolution, [status(thm)], [c_14, c_457])).
% 5.02/2.26  tff(c_396, plain, (![B_172, A_173]: (~v3_tex_2(B_172, A_173) | ~m1_subset_1(B_172, k1_zfmisc_1(u1_struct_0(A_173))) | ~v1_xboole_0(B_172) | ~l1_pre_topc(A_173) | ~v2_pre_topc(A_173) | v2_struct_0(A_173))), inference(cnfTransformation, [status(thm)], [f_100])).
% 5.02/2.26  tff(c_415, plain, (![B_20, A_18]: (~v3_tex_2(u1_struct_0(B_20), A_18) | ~v1_xboole_0(u1_struct_0(B_20)) | ~v2_pre_topc(A_18) | v2_struct_0(A_18) | ~m1_pre_topc(B_20, A_18) | ~l1_pre_topc(A_18))), inference(resolution, [status(thm)], [c_14, c_396])).
% 5.02/2.26  tff(c_487, plain, (![B_196, A_197]: (~v1_xboole_0(u1_struct_0(B_196)) | ~v2_pre_topc(A_197) | ~v4_tex_2(B_196, A_197) | v2_struct_0(A_197) | ~m1_pre_topc(B_196, A_197) | ~l1_pre_topc(A_197))), inference(resolution, [status(thm)], [c_482, c_415])).
% 5.02/2.26  tff(c_491, plain, (![A_198]: (~v2_pre_topc(A_198) | ~v4_tex_2('#skF_3', A_198) | v2_struct_0(A_198) | ~m1_pre_topc('#skF_3', A_198) | ~l1_pre_topc(A_198))), inference(resolution, [status(thm)], [c_333, c_487])).
% 5.02/2.26  tff(c_498, plain, (~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_48, c_491])).
% 5.02/2.26  tff(c_502, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_46, c_56, c_498])).
% 5.02/2.26  tff(c_504, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_502])).
% 5.02/2.26  tff(c_506, plain, (~v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_106])).
% 5.02/2.26  tff(c_8, plain, (![A_7, B_8]: (r2_hidden(A_7, B_8) | v1_xboole_0(B_8) | ~m1_subset_1(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.02/2.26  tff(c_50, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_177])).
% 5.02/2.26  tff(c_44, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_177])).
% 5.02/2.26  tff(c_42, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_177])).
% 5.02/2.26  tff(c_40, plain, (v5_pre_topc('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_177])).
% 5.02/2.26  tff(c_36, plain, (v3_borsuk_1('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_177])).
% 5.02/2.26  tff(c_38, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_177])).
% 5.02/2.26  tff(c_4, plain, (![A_2, B_3]: (m1_subset_1(k1_tarski(A_2), k1_zfmisc_1(B_3)) | ~r2_hidden(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.02/2.26  tff(c_54, plain, (v3_tdlat_3('#skF_2')), inference(cnfTransformation, [status(thm)], [f_177])).
% 5.02/2.26  tff(c_525, plain, (![C_207, A_208, B_209]: (m1_subset_1(C_207, k1_zfmisc_1(u1_struct_0(A_208))) | ~m1_subset_1(C_207, k1_zfmisc_1(u1_struct_0(B_209))) | ~m1_pre_topc(B_209, A_208) | ~l1_pre_topc(A_208))), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.02/2.26  tff(c_533, plain, (![A_210, A_211, B_212]: (m1_subset_1(k1_tarski(A_210), k1_zfmisc_1(u1_struct_0(A_211))) | ~m1_pre_topc(B_212, A_211) | ~l1_pre_topc(A_211) | ~r2_hidden(A_210, u1_struct_0(B_212)))), inference(resolution, [status(thm)], [c_4, c_525])).
% 5.02/2.26  tff(c_535, plain, (![A_210]: (m1_subset_1(k1_tarski(A_210), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~r2_hidden(A_210, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_46, c_533])).
% 5.02/2.26  tff(c_538, plain, (![A_210]: (m1_subset_1(k1_tarski(A_210), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~r2_hidden(A_210, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_535])).
% 5.02/2.26  tff(c_677, plain, (![A_252, B_253, C_254, E_255]: (k8_relset_1(u1_struct_0(A_252), u1_struct_0(B_253), C_254, E_255)=k2_pre_topc(A_252, E_255) | ~m1_subset_1(E_255, k1_zfmisc_1(u1_struct_0(A_252))) | ~m1_subset_1(E_255, k1_zfmisc_1(u1_struct_0(B_253))) | ~v3_borsuk_1(C_254, A_252, B_253) | ~m1_subset_1(C_254, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_252), u1_struct_0(B_253)))) | ~v5_pre_topc(C_254, A_252, B_253) | ~v1_funct_2(C_254, u1_struct_0(A_252), u1_struct_0(B_253)) | ~v1_funct_1(C_254) | ~m1_pre_topc(B_253, A_252) | ~v4_tex_2(B_253, A_252) | v2_struct_0(B_253) | ~l1_pre_topc(A_252) | ~v3_tdlat_3(A_252) | ~v2_pre_topc(A_252) | v2_struct_0(A_252))), inference(cnfTransformation, [status(thm)], [f_138])).
% 5.02/2.26  tff(c_685, plain, (![B_253, C_254, A_210]: (k8_relset_1(u1_struct_0('#skF_2'), u1_struct_0(B_253), C_254, k1_tarski(A_210))=k2_pre_topc('#skF_2', k1_tarski(A_210)) | ~m1_subset_1(k1_tarski(A_210), k1_zfmisc_1(u1_struct_0(B_253))) | ~v3_borsuk_1(C_254, '#skF_2', B_253) | ~m1_subset_1(C_254, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0(B_253)))) | ~v5_pre_topc(C_254, '#skF_2', B_253) | ~v1_funct_2(C_254, u1_struct_0('#skF_2'), u1_struct_0(B_253)) | ~v1_funct_1(C_254) | ~m1_pre_topc(B_253, '#skF_2') | ~v4_tex_2(B_253, '#skF_2') | v2_struct_0(B_253) | ~l1_pre_topc('#skF_2') | ~v3_tdlat_3('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~r2_hidden(A_210, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_538, c_677])).
% 5.02/2.26  tff(c_696, plain, (![B_253, C_254, A_210]: (k8_relset_1(u1_struct_0('#skF_2'), u1_struct_0(B_253), C_254, k1_tarski(A_210))=k2_pre_topc('#skF_2', k1_tarski(A_210)) | ~m1_subset_1(k1_tarski(A_210), k1_zfmisc_1(u1_struct_0(B_253))) | ~v3_borsuk_1(C_254, '#skF_2', B_253) | ~m1_subset_1(C_254, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0(B_253)))) | ~v5_pre_topc(C_254, '#skF_2', B_253) | ~v1_funct_2(C_254, u1_struct_0('#skF_2'), u1_struct_0(B_253)) | ~v1_funct_1(C_254) | ~m1_pre_topc(B_253, '#skF_2') | ~v4_tex_2(B_253, '#skF_2') | v2_struct_0(B_253) | v2_struct_0('#skF_2') | ~r2_hidden(A_210, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_685])).
% 5.02/2.26  tff(c_716, plain, (![B_265, C_266, A_267]: (k8_relset_1(u1_struct_0('#skF_2'), u1_struct_0(B_265), C_266, k1_tarski(A_267))=k2_pre_topc('#skF_2', k1_tarski(A_267)) | ~m1_subset_1(k1_tarski(A_267), k1_zfmisc_1(u1_struct_0(B_265))) | ~v3_borsuk_1(C_266, '#skF_2', B_265) | ~m1_subset_1(C_266, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0(B_265)))) | ~v5_pre_topc(C_266, '#skF_2', B_265) | ~v1_funct_2(C_266, u1_struct_0('#skF_2'), u1_struct_0(B_265)) | ~v1_funct_1(C_266) | ~m1_pre_topc(B_265, '#skF_2') | ~v4_tex_2(B_265, '#skF_2') | v2_struct_0(B_265) | ~r2_hidden(A_267, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_58, c_696])).
% 5.02/2.26  tff(c_760, plain, (![B_275, C_276, A_277]: (k8_relset_1(u1_struct_0('#skF_2'), u1_struct_0(B_275), C_276, k1_tarski(A_277))=k2_pre_topc('#skF_2', k1_tarski(A_277)) | ~v3_borsuk_1(C_276, '#skF_2', B_275) | ~m1_subset_1(C_276, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0(B_275)))) | ~v5_pre_topc(C_276, '#skF_2', B_275) | ~v1_funct_2(C_276, u1_struct_0('#skF_2'), u1_struct_0(B_275)) | ~v1_funct_1(C_276) | ~m1_pre_topc(B_275, '#skF_2') | ~v4_tex_2(B_275, '#skF_2') | v2_struct_0(B_275) | ~r2_hidden(A_277, u1_struct_0('#skF_3')) | ~r2_hidden(A_277, u1_struct_0(B_275)))), inference(resolution, [status(thm)], [c_4, c_716])).
% 5.02/2.26  tff(c_762, plain, (![A_277]: (k8_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4', k1_tarski(A_277))=k2_pre_topc('#skF_2', k1_tarski(A_277)) | ~v3_borsuk_1('#skF_4', '#skF_2', '#skF_3') | ~v5_pre_topc('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_2') | ~v4_tex_2('#skF_3', '#skF_2') | v2_struct_0('#skF_3') | ~r2_hidden(A_277, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_38, c_760])).
% 5.02/2.26  tff(c_768, plain, (![A_277]: (k8_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4', k1_tarski(A_277))=k2_pre_topc('#skF_2', k1_tarski(A_277)) | v2_struct_0('#skF_3') | ~r2_hidden(A_277, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_40, c_36, c_762])).
% 5.02/2.26  tff(c_771, plain, (![A_278]: (k8_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4', k1_tarski(A_278))=k2_pre_topc('#skF_2', k1_tarski(A_278)) | ~r2_hidden(A_278, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_50, c_768])).
% 5.02/2.26  tff(c_505, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_6')=k1_tarski('#skF_6')), inference(splitRight, [status(thm)], [c_106])).
% 5.02/2.26  tff(c_32, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_177])).
% 5.02/2.26  tff(c_105, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_6')=k1_tarski('#skF_6') | v1_xboole_0(u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_32, c_90])).
% 5.02/2.26  tff(c_107, plain, (v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_105])).
% 5.02/2.26  tff(c_108, plain, (![B_102, A_103]: (m1_subset_1(u1_struct_0(B_102), k1_zfmisc_1(u1_struct_0(A_103))) | ~m1_pre_topc(B_102, A_103) | ~l1_pre_topc(A_103))), inference(cnfTransformation, [status(thm)], [f_68])).
% 5.02/2.26  tff(c_6, plain, (![B_6, A_4]: (v1_xboole_0(B_6) | ~m1_subset_1(B_6, k1_zfmisc_1(A_4)) | ~v1_xboole_0(A_4))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.02/2.26  tff(c_301, plain, (![B_149, A_150]: (v1_xboole_0(u1_struct_0(B_149)) | ~v1_xboole_0(u1_struct_0(A_150)) | ~m1_pre_topc(B_149, A_150) | ~l1_pre_topc(A_150))), inference(resolution, [status(thm)], [c_108, c_6])).
% 5.02/2.26  tff(c_303, plain, (![B_149]: (v1_xboole_0(u1_struct_0(B_149)) | ~m1_pre_topc(B_149, '#skF_2') | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_107, c_301])).
% 5.02/2.26  tff(c_307, plain, (![B_151]: (v1_xboole_0(u1_struct_0(B_151)) | ~m1_pre_topc(B_151, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_303])).
% 5.02/2.26  tff(c_117, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_106])).
% 5.02/2.26  tff(c_260, plain, (![B_142, A_143]: (v3_tex_2(u1_struct_0(B_142), A_143) | ~m1_subset_1(u1_struct_0(B_142), k1_zfmisc_1(u1_struct_0(A_143))) | ~v4_tex_2(B_142, A_143) | ~m1_pre_topc(B_142, A_143) | ~l1_pre_topc(A_143) | v2_struct_0(A_143))), inference(cnfTransformation, [status(thm)], [f_85])).
% 5.02/2.26  tff(c_265, plain, (![B_144, A_145]: (v3_tex_2(u1_struct_0(B_144), A_145) | ~v4_tex_2(B_144, A_145) | v2_struct_0(A_145) | ~m1_pre_topc(B_144, A_145) | ~l1_pre_topc(A_145))), inference(resolution, [status(thm)], [c_14, c_260])).
% 5.02/2.26  tff(c_197, plain, (![B_125, A_126]: (~v3_tex_2(B_125, A_126) | ~m1_subset_1(B_125, k1_zfmisc_1(u1_struct_0(A_126))) | ~v1_xboole_0(B_125) | ~l1_pre_topc(A_126) | ~v2_pre_topc(A_126) | v2_struct_0(A_126))), inference(cnfTransformation, [status(thm)], [f_100])).
% 5.02/2.26  tff(c_216, plain, (![B_20, A_18]: (~v3_tex_2(u1_struct_0(B_20), A_18) | ~v1_xboole_0(u1_struct_0(B_20)) | ~v2_pre_topc(A_18) | v2_struct_0(A_18) | ~m1_pre_topc(B_20, A_18) | ~l1_pre_topc(A_18))), inference(resolution, [status(thm)], [c_14, c_197])).
% 5.02/2.26  tff(c_270, plain, (![B_146, A_147]: (~v1_xboole_0(u1_struct_0(B_146)) | ~v2_pre_topc(A_147) | ~v4_tex_2(B_146, A_147) | v2_struct_0(A_147) | ~m1_pre_topc(B_146, A_147) | ~l1_pre_topc(A_147))), inference(resolution, [status(thm)], [c_265, c_216])).
% 5.02/2.26  tff(c_280, plain, (![A_148]: (~v2_pre_topc(A_148) | ~v4_tex_2('#skF_3', A_148) | v2_struct_0(A_148) | ~m1_pre_topc('#skF_3', A_148) | ~l1_pre_topc(A_148))), inference(resolution, [status(thm)], [c_117, c_270])).
% 5.02/2.26  tff(c_287, plain, (~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_48, c_280])).
% 5.02/2.26  tff(c_291, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_46, c_56, c_287])).
% 5.02/2.26  tff(c_293, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_291])).
% 5.02/2.26  tff(c_295, plain, (~v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_106])).
% 5.02/2.26  tff(c_312, plain, (~m1_pre_topc('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_307, c_295])).
% 5.02/2.26  tff(c_317, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_312])).
% 5.02/2.26  tff(c_318, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_6')=k1_tarski('#skF_6')), inference(splitRight, [status(thm)], [c_105])).
% 5.02/2.26  tff(c_28, plain, (k8_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4', k6_domain_1(u1_struct_0('#skF_3'), '#skF_5'))!=k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_177])).
% 5.02/2.26  tff(c_60, plain, (k8_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4', k6_domain_1(u1_struct_0('#skF_3'), '#skF_6'))!=k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28])).
% 5.02/2.26  tff(c_507, plain, (k8_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4', k6_domain_1(u1_struct_0('#skF_3'), '#skF_6'))!=k2_pre_topc('#skF_2', k1_tarski('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_318, c_60])).
% 5.02/2.26  tff(c_508, plain, (k8_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4', k1_tarski('#skF_6'))!=k2_pre_topc('#skF_2', k1_tarski('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_505, c_507])).
% 5.02/2.26  tff(c_782, plain, (~r2_hidden('#skF_6', u1_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_771, c_508])).
% 5.02/2.26  tff(c_786, plain, (v1_xboole_0(u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_8, c_782])).
% 5.02/2.26  tff(c_789, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_59, c_786])).
% 5.02/2.26  tff(c_791, plain, $false, inference(negUnitSimplification, [status(thm)], [c_506, c_789])).
% 5.02/2.26  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.02/2.26  
% 5.02/2.26  Inference rules
% 5.02/2.26  ----------------------
% 5.02/2.26  #Ref     : 0
% 5.02/2.26  #Sup     : 151
% 5.02/2.26  #Fact    : 0
% 5.02/2.26  #Define  : 0
% 5.02/2.26  #Split   : 17
% 5.02/2.26  #Chain   : 0
% 5.02/2.26  #Close   : 0
% 5.02/2.26  
% 5.02/2.26  Ordering : KBO
% 5.02/2.26  
% 5.02/2.26  Simplification rules
% 5.02/2.26  ----------------------
% 5.02/2.26  #Subsume      : 16
% 5.02/2.26  #Demod        : 48
% 5.02/2.26  #Tautology    : 35
% 5.02/2.26  #SimpNegUnit  : 14
% 5.02/2.26  #BackRed      : 2
% 5.02/2.26  
% 5.02/2.26  #Partial instantiations: 0
% 5.02/2.26  #Strategies tried      : 1
% 5.02/2.26  
% 5.02/2.26  Timing (in seconds)
% 5.02/2.26  ----------------------
% 5.02/2.27  Preprocessing        : 0.59
% 5.02/2.27  Parsing              : 0.30
% 5.02/2.27  CNF conversion       : 0.05
% 5.02/2.27  Main loop            : 0.79
% 5.02/2.27  Inferencing          : 0.30
% 5.02/2.27  Reduction            : 0.22
% 5.02/2.27  Demodulation         : 0.15
% 5.02/2.27  BG Simplification    : 0.04
% 5.02/2.27  Subsumption          : 0.15
% 5.02/2.27  Abstraction          : 0.03
% 5.02/2.27  MUC search           : 0.00
% 5.02/2.27  Cooper               : 0.00
% 5.02/2.27  Total                : 1.45
% 5.02/2.27  Index Insertion      : 0.00
% 5.02/2.27  Index Deletion       : 0.00
% 5.02/2.27  Index Matching       : 0.00
% 5.02/2.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
