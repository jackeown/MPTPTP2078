%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:38 EST 2020

% Result     : Theorem 2.89s
% Output     : CNFRefutation 2.89s
% Verified   : 
% Statistics : Number of formulae       :  118 ( 294 expanded)
%              Number of leaves         :   41 ( 123 expanded)
%              Depth                    :   12
%              Number of atoms          :  251 (1442 expanded)
%              Number of equality atoms :   24 ( 182 expanded)
%              Maximal formula depth    :   20 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_pre_topc > v3_borsuk_1 > v1_funct_2 > v4_tex_2 > v4_pre_topc > m1_subset_1 > m1_pre_topc > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_pre_topc > k8_relset_1 > k6_domain_1 > k2_zfmisc_1 > k2_tarski > k2_pre_topc > k10_relat_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4

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

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

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

tff(f_167,negated_conjecture,(
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

tff(f_38,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_47,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_54,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_83,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_69,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ? [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
          & ~ v1_xboole_0(B)
          & v4_pre_topc(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc7_pre_topc)).

tff(f_34,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_90,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_128,axiom,(
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

tff(c_48,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_36,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_419,plain,(
    ! [A_136,B_137,C_138,D_139] :
      ( k8_relset_1(A_136,B_137,C_138,D_139) = k10_relat_1(C_138,D_139)
      | ~ m1_subset_1(C_138,k1_zfmisc_1(k2_zfmisc_1(A_136,B_137))) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_426,plain,(
    ! [D_139] : k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4',D_139) = k10_relat_1('#skF_4',D_139) ),
    inference(resolution,[status(thm)],[c_36,c_419])).

tff(c_54,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_50,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_44,plain,(
    m1_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_85,plain,(
    ! [B_86,A_87] :
      ( v2_pre_topc(B_86)
      | ~ m1_pre_topc(B_86,A_87)
      | ~ l1_pre_topc(A_87)
      | ~ v2_pre_topc(A_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_88,plain,
    ( v2_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_85])).

tff(c_91,plain,(
    v2_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_50,c_88])).

tff(c_72,plain,(
    ! [B_82,A_83] :
      ( l1_pre_topc(B_82)
      | ~ m1_pre_topc(B_82,A_83)
      | ~ l1_pre_topc(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_75,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_72])).

tff(c_78,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_75])).

tff(c_28,plain,(
    '#skF_5' = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_32,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_57,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_32])).

tff(c_94,plain,(
    ! [A_90,B_91] :
      ( k6_domain_1(A_90,B_91) = k1_tarski(B_91)
      | ~ m1_subset_1(B_91,A_90)
      | v1_xboole_0(A_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_106,plain,
    ( k6_domain_1(u1_struct_0('#skF_3'),'#skF_6') = k1_tarski('#skF_6')
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_57,c_94])).

tff(c_261,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_106])).

tff(c_315,plain,(
    ! [A_122] :
      ( m1_subset_1('#skF_1'(A_122),k1_zfmisc_1(u1_struct_0(A_122)))
      | ~ l1_pre_topc(A_122)
      | ~ v2_pre_topc(A_122)
      | v2_struct_0(A_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_4,plain,(
    ! [B_4,A_2] :
      ( v1_xboole_0(B_4)
      | ~ m1_subset_1(B_4,k1_zfmisc_1(A_2))
      | ~ v1_xboole_0(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_324,plain,(
    ! [A_123] :
      ( v1_xboole_0('#skF_1'(A_123))
      | ~ v1_xboole_0(u1_struct_0(A_123))
      | ~ l1_pre_topc(A_123)
      | ~ v2_pre_topc(A_123)
      | v2_struct_0(A_123) ) ),
    inference(resolution,[status(thm)],[c_315,c_4])).

tff(c_330,plain,
    ( v1_xboole_0('#skF_1'('#skF_3'))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_261,c_324])).

tff(c_334,plain,
    ( v1_xboole_0('#skF_1'('#skF_3'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_78,c_330])).

tff(c_335,plain,(
    v1_xboole_0('#skF_1'('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_334])).

tff(c_14,plain,(
    ! [A_15] :
      ( ~ v1_xboole_0('#skF_1'(A_15))
      | ~ l1_pre_topc(A_15)
      | ~ v2_pre_topc(A_15)
      | v2_struct_0(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_346,plain,
    ( ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_335,c_14])).

tff(c_349,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_78,c_346])).

tff(c_351,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_349])).

tff(c_352,plain,(
    k6_domain_1(u1_struct_0('#skF_3'),'#skF_6') = k1_tarski('#skF_6') ),
    inference(splitRight,[status(thm)],[c_106])).

tff(c_30,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_105,plain,
    ( k6_domain_1(u1_struct_0('#skF_2'),'#skF_6') = k1_tarski('#skF_6')
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_30,c_94])).

tff(c_107,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_105])).

tff(c_205,plain,(
    ! [B_106,A_107] :
      ( m1_subset_1(u1_struct_0(B_106),k1_zfmisc_1(u1_struct_0(A_107)))
      | ~ m1_pre_topc(B_106,A_107)
      | ~ l1_pre_topc(A_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_237,plain,(
    ! [B_110,A_111] :
      ( v1_xboole_0(u1_struct_0(B_110))
      | ~ v1_xboole_0(u1_struct_0(A_111))
      | ~ m1_pre_topc(B_110,A_111)
      | ~ l1_pre_topc(A_111) ) ),
    inference(resolution,[status(thm)],[c_205,c_4])).

tff(c_239,plain,(
    ! [B_110] :
      ( v1_xboole_0(u1_struct_0(B_110))
      | ~ m1_pre_topc(B_110,'#skF_2')
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_107,c_237])).

tff(c_244,plain,(
    ! [B_112] :
      ( v1_xboole_0(u1_struct_0(B_112))
      | ~ m1_pre_topc(B_112,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_239])).

tff(c_108,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_106])).

tff(c_142,plain,(
    ! [A_99] :
      ( m1_subset_1('#skF_1'(A_99),k1_zfmisc_1(u1_struct_0(A_99)))
      | ~ l1_pre_topc(A_99)
      | ~ v2_pre_topc(A_99)
      | v2_struct_0(A_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_168,plain,(
    ! [A_105] :
      ( v1_xboole_0('#skF_1'(A_105))
      | ~ v1_xboole_0(u1_struct_0(A_105))
      | ~ l1_pre_topc(A_105)
      | ~ v2_pre_topc(A_105)
      | v2_struct_0(A_105) ) ),
    inference(resolution,[status(thm)],[c_142,c_4])).

tff(c_177,plain,
    ( v1_xboole_0('#skF_1'('#skF_3'))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_108,c_168])).

tff(c_185,plain,
    ( v1_xboole_0('#skF_1'('#skF_3'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_78,c_177])).

tff(c_186,plain,(
    v1_xboole_0('#skF_1'('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_185])).

tff(c_193,plain,
    ( ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_186,c_14])).

tff(c_196,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_78,c_193])).

tff(c_198,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_196])).

tff(c_200,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_106])).

tff(c_249,plain,(
    ~ m1_pre_topc('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_244,c_200])).

tff(c_254,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_249])).

tff(c_255,plain,(
    k6_domain_1(u1_struct_0('#skF_2'),'#skF_6') = k1_tarski('#skF_6') ),
    inference(splitRight,[status(thm)],[c_105])).

tff(c_26,plain,(
    k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4',k6_domain_1(u1_struct_0('#skF_3'),'#skF_5')) != k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_58,plain,(
    k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4',k6_domain_1(u1_struct_0('#skF_3'),'#skF_6')) != k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26])).

tff(c_358,plain,(
    k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4',k1_tarski('#skF_6')) != k2_pre_topc('#skF_2',k1_tarski('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_352,c_255,c_58])).

tff(c_427,plain,(
    k2_pre_topc('#skF_2',k1_tarski('#skF_6')) != k10_relat_1('#skF_4',k1_tarski('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_426,c_358])).

tff(c_46,plain,(
    v4_tex_2('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_42,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_40,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_38,plain,(
    v5_pre_topc('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_34,plain,(
    v3_borsuk_1('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_353,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_106])).

tff(c_368,plain,(
    ! [A_130,B_131] :
      ( m1_subset_1(k6_domain_1(A_130,B_131),k1_zfmisc_1(A_130))
      | ~ m1_subset_1(B_131,A_130)
      | v1_xboole_0(A_130) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_377,plain,
    ( m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3'))
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_352,c_368])).

tff(c_384,plain,
    ( m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_377])).

tff(c_385,plain,(
    m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_353,c_384])).

tff(c_56,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_52,plain,(
    v3_tdlat_3('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_256,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_105])).

tff(c_380,plain,
    ( m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_2'))
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_255,c_368])).

tff(c_387,plain,
    ( m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_380])).

tff(c_388,plain,(
    m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_256,c_387])).

tff(c_437,plain,(
    ! [A_141,B_142,C_143,E_144] :
      ( k8_relset_1(u1_struct_0(A_141),u1_struct_0(B_142),C_143,E_144) = k2_pre_topc(A_141,E_144)
      | ~ m1_subset_1(E_144,k1_zfmisc_1(u1_struct_0(A_141)))
      | ~ m1_subset_1(E_144,k1_zfmisc_1(u1_struct_0(B_142)))
      | ~ v3_borsuk_1(C_143,A_141,B_142)
      | ~ m1_subset_1(C_143,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_141),u1_struct_0(B_142))))
      | ~ v5_pre_topc(C_143,A_141,B_142)
      | ~ v1_funct_2(C_143,u1_struct_0(A_141),u1_struct_0(B_142))
      | ~ v1_funct_1(C_143)
      | ~ m1_pre_topc(B_142,A_141)
      | ~ v4_tex_2(B_142,A_141)
      | v2_struct_0(B_142)
      | ~ l1_pre_topc(A_141)
      | ~ v3_tdlat_3(A_141)
      | ~ v2_pre_topc(A_141)
      | v2_struct_0(A_141) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_441,plain,(
    ! [B_142,C_143] :
      ( k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0(B_142),C_143,k1_tarski('#skF_6')) = k2_pre_topc('#skF_2',k1_tarski('#skF_6'))
      | ~ m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0(B_142)))
      | ~ v3_borsuk_1(C_143,'#skF_2',B_142)
      | ~ m1_subset_1(C_143,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0(B_142))))
      | ~ v5_pre_topc(C_143,'#skF_2',B_142)
      | ~ v1_funct_2(C_143,u1_struct_0('#skF_2'),u1_struct_0(B_142))
      | ~ v1_funct_1(C_143)
      | ~ m1_pre_topc(B_142,'#skF_2')
      | ~ v4_tex_2(B_142,'#skF_2')
      | v2_struct_0(B_142)
      | ~ l1_pre_topc('#skF_2')
      | ~ v3_tdlat_3('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_388,c_437])).

tff(c_452,plain,(
    ! [B_142,C_143] :
      ( k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0(B_142),C_143,k1_tarski('#skF_6')) = k2_pre_topc('#skF_2',k1_tarski('#skF_6'))
      | ~ m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0(B_142)))
      | ~ v3_borsuk_1(C_143,'#skF_2',B_142)
      | ~ m1_subset_1(C_143,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0(B_142))))
      | ~ v5_pre_topc(C_143,'#skF_2',B_142)
      | ~ v1_funct_2(C_143,u1_struct_0('#skF_2'),u1_struct_0(B_142))
      | ~ v1_funct_1(C_143)
      | ~ m1_pre_topc(B_142,'#skF_2')
      | ~ v4_tex_2(B_142,'#skF_2')
      | v2_struct_0(B_142)
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_441])).

tff(c_505,plain,(
    ! [B_149,C_150] :
      ( k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0(B_149),C_150,k1_tarski('#skF_6')) = k2_pre_topc('#skF_2',k1_tarski('#skF_6'))
      | ~ m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0(B_149)))
      | ~ v3_borsuk_1(C_150,'#skF_2',B_149)
      | ~ m1_subset_1(C_150,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0(B_149))))
      | ~ v5_pre_topc(C_150,'#skF_2',B_149)
      | ~ v1_funct_2(C_150,u1_struct_0('#skF_2'),u1_struct_0(B_149))
      | ~ v1_funct_1(C_150)
      | ~ m1_pre_topc(B_149,'#skF_2')
      | ~ v4_tex_2(B_149,'#skF_2')
      | v2_struct_0(B_149) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_452])).

tff(c_512,plain,
    ( k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4',k1_tarski('#skF_6')) = k2_pre_topc('#skF_2',k1_tarski('#skF_6'))
    | ~ m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ v3_borsuk_1('#skF_4','#skF_2','#skF_3')
    | ~ v5_pre_topc('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ v4_tex_2('#skF_3','#skF_2')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_505])).

tff(c_516,plain,
    ( k2_pre_topc('#skF_2',k1_tarski('#skF_6')) = k10_relat_1('#skF_4',k1_tarski('#skF_6'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_40,c_38,c_34,c_385,c_426,c_512])).

tff(c_518,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_427,c_516])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 20:32:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.89/1.52  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.89/1.53  
% 2.89/1.53  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.89/1.53  %$ v5_pre_topc > v3_borsuk_1 > v1_funct_2 > v4_tex_2 > v4_pre_topc > m1_subset_1 > m1_pre_topc > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_pre_topc > k8_relset_1 > k6_domain_1 > k2_zfmisc_1 > k2_tarski > k2_pre_topc > k10_relat_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4
% 2.89/1.53  
% 2.89/1.53  %Foreground sorts:
% 2.89/1.53  
% 2.89/1.53  
% 2.89/1.53  %Background operators:
% 2.89/1.53  
% 2.89/1.53  
% 2.89/1.53  %Foreground operators:
% 2.89/1.53  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.89/1.53  tff(v3_borsuk_1, type, v3_borsuk_1: ($i * $i * $i) > $o).
% 2.89/1.53  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.89/1.53  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.89/1.53  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.89/1.53  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 2.89/1.53  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.89/1.53  tff(v4_tex_2, type, v4_tex_2: ($i * $i) > $o).
% 2.89/1.53  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.89/1.53  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.89/1.53  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.89/1.53  tff('#skF_5', type, '#skF_5': $i).
% 2.89/1.53  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.89/1.53  tff('#skF_6', type, '#skF_6': $i).
% 2.89/1.53  tff('#skF_2', type, '#skF_2': $i).
% 2.89/1.53  tff('#skF_3', type, '#skF_3': $i).
% 2.89/1.53  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.89/1.53  tff(v3_tdlat_3, type, v3_tdlat_3: $i > $o).
% 2.89/1.53  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 2.89/1.53  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.89/1.53  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.89/1.53  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.89/1.53  tff('#skF_4', type, '#skF_4': $i).
% 2.89/1.53  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.89/1.53  tff(v5_pre_topc, type, v5_pre_topc: ($i * $i * $i) > $o).
% 2.89/1.53  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.89/1.53  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.89/1.53  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.89/1.53  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.89/1.53  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 2.89/1.53  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.89/1.53  
% 2.89/1.55  tff(f_167, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v4_tex_2(B, A)) & m1_pre_topc(B, A)) => (![C]: ((((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & v5_pre_topc(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (v3_borsuk_1(C, A, B) => (![D]: (m1_subset_1(D, u1_struct_0(B)) => (![E]: (m1_subset_1(E, u1_struct_0(A)) => ((D = E) => (k8_relset_1(u1_struct_0(A), u1_struct_0(B), C, k6_domain_1(u1_struct_0(B), D)) = k2_pre_topc(A, k6_domain_1(u1_struct_0(A), E))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_tex_2)).
% 2.89/1.55  tff(f_38, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 2.89/1.55  tff(f_47, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_pre_topc)).
% 2.89/1.55  tff(f_54, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 2.89/1.55  tff(f_83, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 2.89/1.55  tff(f_69, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (?[B]: ((m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) & ~v1_xboole_0(B)) & v4_pre_topc(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc7_pre_topc)).
% 2.89/1.55  tff(f_34, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_subset_1)).
% 2.89/1.55  tff(f_90, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 2.89/1.55  tff(f_76, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 2.89/1.55  tff(f_128, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v4_tex_2(B, A)) & m1_pre_topc(B, A)) => (![C]: ((((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & v5_pre_topc(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (v3_borsuk_1(C, A, B) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => (![E]: (m1_subset_1(E, k1_zfmisc_1(u1_struct_0(A))) => ((D = E) => (k8_relset_1(u1_struct_0(A), u1_struct_0(B), C, D) = k2_pre_topc(A, E)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t76_tex_2)).
% 2.89/1.55  tff(c_48, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_167])).
% 2.89/1.55  tff(c_36, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_167])).
% 2.89/1.55  tff(c_419, plain, (![A_136, B_137, C_138, D_139]: (k8_relset_1(A_136, B_137, C_138, D_139)=k10_relat_1(C_138, D_139) | ~m1_subset_1(C_138, k1_zfmisc_1(k2_zfmisc_1(A_136, B_137))))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.89/1.55  tff(c_426, plain, (![D_139]: (k8_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4', D_139)=k10_relat_1('#skF_4', D_139))), inference(resolution, [status(thm)], [c_36, c_419])).
% 2.89/1.55  tff(c_54, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_167])).
% 2.89/1.55  tff(c_50, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_167])).
% 2.89/1.55  tff(c_44, plain, (m1_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_167])).
% 2.89/1.55  tff(c_85, plain, (![B_86, A_87]: (v2_pre_topc(B_86) | ~m1_pre_topc(B_86, A_87) | ~l1_pre_topc(A_87) | ~v2_pre_topc(A_87))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.89/1.55  tff(c_88, plain, (v2_pre_topc('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_44, c_85])).
% 2.89/1.55  tff(c_91, plain, (v2_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_50, c_88])).
% 2.89/1.55  tff(c_72, plain, (![B_82, A_83]: (l1_pre_topc(B_82) | ~m1_pre_topc(B_82, A_83) | ~l1_pre_topc(A_83))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.89/1.55  tff(c_75, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_44, c_72])).
% 2.89/1.55  tff(c_78, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_75])).
% 2.89/1.55  tff(c_28, plain, ('#skF_5'='#skF_6'), inference(cnfTransformation, [status(thm)], [f_167])).
% 2.89/1.55  tff(c_32, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_167])).
% 2.89/1.55  tff(c_57, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_32])).
% 2.89/1.55  tff(c_94, plain, (![A_90, B_91]: (k6_domain_1(A_90, B_91)=k1_tarski(B_91) | ~m1_subset_1(B_91, A_90) | v1_xboole_0(A_90))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.89/1.55  tff(c_106, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_6')=k1_tarski('#skF_6') | v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_57, c_94])).
% 2.89/1.55  tff(c_261, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_106])).
% 2.89/1.55  tff(c_315, plain, (![A_122]: (m1_subset_1('#skF_1'(A_122), k1_zfmisc_1(u1_struct_0(A_122))) | ~l1_pre_topc(A_122) | ~v2_pre_topc(A_122) | v2_struct_0(A_122))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.89/1.55  tff(c_4, plain, (![B_4, A_2]: (v1_xboole_0(B_4) | ~m1_subset_1(B_4, k1_zfmisc_1(A_2)) | ~v1_xboole_0(A_2))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.89/1.55  tff(c_324, plain, (![A_123]: (v1_xboole_0('#skF_1'(A_123)) | ~v1_xboole_0(u1_struct_0(A_123)) | ~l1_pre_topc(A_123) | ~v2_pre_topc(A_123) | v2_struct_0(A_123))), inference(resolution, [status(thm)], [c_315, c_4])).
% 2.89/1.55  tff(c_330, plain, (v1_xboole_0('#skF_1'('#skF_3')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_261, c_324])).
% 2.89/1.55  tff(c_334, plain, (v1_xboole_0('#skF_1'('#skF_3')) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_91, c_78, c_330])).
% 2.89/1.55  tff(c_335, plain, (v1_xboole_0('#skF_1'('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_48, c_334])).
% 2.89/1.55  tff(c_14, plain, (![A_15]: (~v1_xboole_0('#skF_1'(A_15)) | ~l1_pre_topc(A_15) | ~v2_pre_topc(A_15) | v2_struct_0(A_15))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.89/1.55  tff(c_346, plain, (~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_335, c_14])).
% 2.89/1.55  tff(c_349, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_91, c_78, c_346])).
% 2.89/1.55  tff(c_351, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_349])).
% 2.89/1.55  tff(c_352, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_6')=k1_tarski('#skF_6')), inference(splitRight, [status(thm)], [c_106])).
% 2.89/1.55  tff(c_30, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_167])).
% 2.89/1.55  tff(c_105, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_6')=k1_tarski('#skF_6') | v1_xboole_0(u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_30, c_94])).
% 2.89/1.55  tff(c_107, plain, (v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_105])).
% 2.89/1.55  tff(c_205, plain, (![B_106, A_107]: (m1_subset_1(u1_struct_0(B_106), k1_zfmisc_1(u1_struct_0(A_107))) | ~m1_pre_topc(B_106, A_107) | ~l1_pre_topc(A_107))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.89/1.55  tff(c_237, plain, (![B_110, A_111]: (v1_xboole_0(u1_struct_0(B_110)) | ~v1_xboole_0(u1_struct_0(A_111)) | ~m1_pre_topc(B_110, A_111) | ~l1_pre_topc(A_111))), inference(resolution, [status(thm)], [c_205, c_4])).
% 2.89/1.55  tff(c_239, plain, (![B_110]: (v1_xboole_0(u1_struct_0(B_110)) | ~m1_pre_topc(B_110, '#skF_2') | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_107, c_237])).
% 2.89/1.55  tff(c_244, plain, (![B_112]: (v1_xboole_0(u1_struct_0(B_112)) | ~m1_pre_topc(B_112, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_239])).
% 2.89/1.55  tff(c_108, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_106])).
% 2.89/1.55  tff(c_142, plain, (![A_99]: (m1_subset_1('#skF_1'(A_99), k1_zfmisc_1(u1_struct_0(A_99))) | ~l1_pre_topc(A_99) | ~v2_pre_topc(A_99) | v2_struct_0(A_99))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.89/1.55  tff(c_168, plain, (![A_105]: (v1_xboole_0('#skF_1'(A_105)) | ~v1_xboole_0(u1_struct_0(A_105)) | ~l1_pre_topc(A_105) | ~v2_pre_topc(A_105) | v2_struct_0(A_105))), inference(resolution, [status(thm)], [c_142, c_4])).
% 2.89/1.55  tff(c_177, plain, (v1_xboole_0('#skF_1'('#skF_3')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_108, c_168])).
% 2.89/1.55  tff(c_185, plain, (v1_xboole_0('#skF_1'('#skF_3')) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_91, c_78, c_177])).
% 2.89/1.55  tff(c_186, plain, (v1_xboole_0('#skF_1'('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_48, c_185])).
% 2.89/1.55  tff(c_193, plain, (~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_186, c_14])).
% 2.89/1.55  tff(c_196, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_91, c_78, c_193])).
% 2.89/1.55  tff(c_198, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_196])).
% 2.89/1.55  tff(c_200, plain, (~v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_106])).
% 2.89/1.55  tff(c_249, plain, (~m1_pre_topc('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_244, c_200])).
% 2.89/1.55  tff(c_254, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_249])).
% 2.89/1.55  tff(c_255, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_6')=k1_tarski('#skF_6')), inference(splitRight, [status(thm)], [c_105])).
% 2.89/1.55  tff(c_26, plain, (k8_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4', k6_domain_1(u1_struct_0('#skF_3'), '#skF_5'))!=k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_167])).
% 2.89/1.55  tff(c_58, plain, (k8_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4', k6_domain_1(u1_struct_0('#skF_3'), '#skF_6'))!=k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26])).
% 2.89/1.55  tff(c_358, plain, (k8_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4', k1_tarski('#skF_6'))!=k2_pre_topc('#skF_2', k1_tarski('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_352, c_255, c_58])).
% 2.89/1.55  tff(c_427, plain, (k2_pre_topc('#skF_2', k1_tarski('#skF_6'))!=k10_relat_1('#skF_4', k1_tarski('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_426, c_358])).
% 2.89/1.55  tff(c_46, plain, (v4_tex_2('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_167])).
% 2.89/1.55  tff(c_42, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_167])).
% 2.89/1.55  tff(c_40, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_167])).
% 2.89/1.55  tff(c_38, plain, (v5_pre_topc('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_167])).
% 2.89/1.55  tff(c_34, plain, (v3_borsuk_1('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_167])).
% 2.89/1.55  tff(c_353, plain, (~v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_106])).
% 2.89/1.55  tff(c_368, plain, (![A_130, B_131]: (m1_subset_1(k6_domain_1(A_130, B_131), k1_zfmisc_1(A_130)) | ~m1_subset_1(B_131, A_130) | v1_xboole_0(A_130))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.89/1.55  tff(c_377, plain, (m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_3')) | v1_xboole_0(u1_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_352, c_368])).
% 2.89/1.55  tff(c_384, plain, (m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | v1_xboole_0(u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_57, c_377])).
% 2.89/1.55  tff(c_385, plain, (m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_353, c_384])).
% 2.89/1.55  tff(c_56, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_167])).
% 2.89/1.55  tff(c_52, plain, (v3_tdlat_3('#skF_2')), inference(cnfTransformation, [status(thm)], [f_167])).
% 2.89/1.55  tff(c_256, plain, (~v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_105])).
% 2.89/1.55  tff(c_380, plain, (m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_2')) | v1_xboole_0(u1_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_255, c_368])).
% 2.89/1.55  tff(c_387, plain, (m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | v1_xboole_0(u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_380])).
% 2.89/1.55  tff(c_388, plain, (m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_256, c_387])).
% 2.89/1.55  tff(c_437, plain, (![A_141, B_142, C_143, E_144]: (k8_relset_1(u1_struct_0(A_141), u1_struct_0(B_142), C_143, E_144)=k2_pre_topc(A_141, E_144) | ~m1_subset_1(E_144, k1_zfmisc_1(u1_struct_0(A_141))) | ~m1_subset_1(E_144, k1_zfmisc_1(u1_struct_0(B_142))) | ~v3_borsuk_1(C_143, A_141, B_142) | ~m1_subset_1(C_143, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_141), u1_struct_0(B_142)))) | ~v5_pre_topc(C_143, A_141, B_142) | ~v1_funct_2(C_143, u1_struct_0(A_141), u1_struct_0(B_142)) | ~v1_funct_1(C_143) | ~m1_pre_topc(B_142, A_141) | ~v4_tex_2(B_142, A_141) | v2_struct_0(B_142) | ~l1_pre_topc(A_141) | ~v3_tdlat_3(A_141) | ~v2_pre_topc(A_141) | v2_struct_0(A_141))), inference(cnfTransformation, [status(thm)], [f_128])).
% 2.89/1.55  tff(c_441, plain, (![B_142, C_143]: (k8_relset_1(u1_struct_0('#skF_2'), u1_struct_0(B_142), C_143, k1_tarski('#skF_6'))=k2_pre_topc('#skF_2', k1_tarski('#skF_6')) | ~m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0(B_142))) | ~v3_borsuk_1(C_143, '#skF_2', B_142) | ~m1_subset_1(C_143, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0(B_142)))) | ~v5_pre_topc(C_143, '#skF_2', B_142) | ~v1_funct_2(C_143, u1_struct_0('#skF_2'), u1_struct_0(B_142)) | ~v1_funct_1(C_143) | ~m1_pre_topc(B_142, '#skF_2') | ~v4_tex_2(B_142, '#skF_2') | v2_struct_0(B_142) | ~l1_pre_topc('#skF_2') | ~v3_tdlat_3('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_388, c_437])).
% 2.89/1.55  tff(c_452, plain, (![B_142, C_143]: (k8_relset_1(u1_struct_0('#skF_2'), u1_struct_0(B_142), C_143, k1_tarski('#skF_6'))=k2_pre_topc('#skF_2', k1_tarski('#skF_6')) | ~m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0(B_142))) | ~v3_borsuk_1(C_143, '#skF_2', B_142) | ~m1_subset_1(C_143, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0(B_142)))) | ~v5_pre_topc(C_143, '#skF_2', B_142) | ~v1_funct_2(C_143, u1_struct_0('#skF_2'), u1_struct_0(B_142)) | ~v1_funct_1(C_143) | ~m1_pre_topc(B_142, '#skF_2') | ~v4_tex_2(B_142, '#skF_2') | v2_struct_0(B_142) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_441])).
% 2.89/1.55  tff(c_505, plain, (![B_149, C_150]: (k8_relset_1(u1_struct_0('#skF_2'), u1_struct_0(B_149), C_150, k1_tarski('#skF_6'))=k2_pre_topc('#skF_2', k1_tarski('#skF_6')) | ~m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0(B_149))) | ~v3_borsuk_1(C_150, '#skF_2', B_149) | ~m1_subset_1(C_150, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0(B_149)))) | ~v5_pre_topc(C_150, '#skF_2', B_149) | ~v1_funct_2(C_150, u1_struct_0('#skF_2'), u1_struct_0(B_149)) | ~v1_funct_1(C_150) | ~m1_pre_topc(B_149, '#skF_2') | ~v4_tex_2(B_149, '#skF_2') | v2_struct_0(B_149))), inference(negUnitSimplification, [status(thm)], [c_56, c_452])).
% 2.89/1.55  tff(c_512, plain, (k8_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4', k1_tarski('#skF_6'))=k2_pre_topc('#skF_2', k1_tarski('#skF_6')) | ~m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~v3_borsuk_1('#skF_4', '#skF_2', '#skF_3') | ~v5_pre_topc('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_2') | ~v4_tex_2('#skF_3', '#skF_2') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_36, c_505])).
% 2.89/1.55  tff(c_516, plain, (k2_pre_topc('#skF_2', k1_tarski('#skF_6'))=k10_relat_1('#skF_4', k1_tarski('#skF_6')) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_40, c_38, c_34, c_385, c_426, c_512])).
% 2.89/1.55  tff(c_518, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_427, c_516])).
% 2.89/1.55  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.89/1.55  
% 2.89/1.55  Inference rules
% 2.89/1.55  ----------------------
% 2.89/1.55  #Ref     : 0
% 2.89/1.55  #Sup     : 95
% 2.89/1.55  #Fact    : 0
% 2.89/1.55  #Define  : 0
% 2.89/1.55  #Split   : 8
% 2.89/1.55  #Chain   : 0
% 2.89/1.55  #Close   : 0
% 2.89/1.55  
% 2.89/1.55  Ordering : KBO
% 2.89/1.55  
% 2.89/1.55  Simplification rules
% 2.89/1.55  ----------------------
% 2.89/1.55  #Subsume      : 5
% 2.89/1.55  #Demod        : 54
% 2.89/1.55  #Tautology    : 24
% 2.89/1.55  #SimpNegUnit  : 14
% 2.89/1.55  #BackRed      : 1
% 2.89/1.55  
% 2.89/1.55  #Partial instantiations: 0
% 2.89/1.55  #Strategies tried      : 1
% 2.89/1.55  
% 2.89/1.55  Timing (in seconds)
% 2.89/1.55  ----------------------
% 2.89/1.55  Preprocessing        : 0.37
% 2.89/1.55  Parsing              : 0.20
% 2.89/1.55  CNF conversion       : 0.03
% 2.89/1.55  Main loop            : 0.30
% 2.89/1.55  Inferencing          : 0.11
% 2.89/1.55  Reduction            : 0.09
% 2.89/1.55  Demodulation         : 0.06
% 2.89/1.55  BG Simplification    : 0.02
% 2.89/1.55  Subsumption          : 0.05
% 2.89/1.55  Abstraction          : 0.01
% 2.89/1.55  MUC search           : 0.00
% 2.89/1.55  Cooper               : 0.00
% 2.89/1.55  Total                : 0.71
% 2.89/1.55  Index Insertion      : 0.00
% 2.89/1.55  Index Deletion       : 0.00
% 2.89/1.55  Index Matching       : 0.00
% 2.89/1.55  BG Taut test         : 0.00
%------------------------------------------------------------------------------
