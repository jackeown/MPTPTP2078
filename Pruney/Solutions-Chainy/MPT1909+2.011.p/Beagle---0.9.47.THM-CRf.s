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
% DateTime   : Thu Dec  3 10:30:39 EST 2020

% Result     : Theorem 3.42s
% Output     : CNFRefutation 3.42s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 181 expanded)
%              Number of leaves         :   41 (  84 expanded)
%              Depth                    :   15
%              Number of atoms          :  262 ( 899 expanded)
%              Number of equality atoms :   22 ( 106 expanded)
%              Maximal formula depth    :   20 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_pre_topc > v3_borsuk_1 > v1_funct_2 > v4_tex_2 > r2_hidden > m1_subset_1 > m1_pre_topc > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_pre_topc > k8_relset_1 > k6_domain_1 > k2_zfmisc_1 > k2_tarski > k2_pre_topc > k1_connsp_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k1_connsp_2,type,(
    k1_connsp_2: ( $i * $i ) > $i )).

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

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tex_2)).

tff(f_53,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_60,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_77,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_100,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => r2_hidden(B,k1_connsp_2(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_connsp_2)).

tff(f_88,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => m1_subset_1(k1_connsp_2(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_connsp_2)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

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

tff(f_70,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(B)))
             => m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_pre_topc)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_tex_2)).

tff(c_46,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_52,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_48,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_42,plain,(
    m1_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_79,plain,(
    ! [B_93,A_94] :
      ( v2_pre_topc(B_93)
      | ~ m1_pre_topc(B_93,A_94)
      | ~ l1_pre_topc(A_94)
      | ~ v2_pre_topc(A_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_82,plain,
    ( v2_pre_topc('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_79])).

tff(c_85,plain,(
    v2_pre_topc('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_48,c_82])).

tff(c_70,plain,(
    ! [B_87,A_88] :
      ( l1_pre_topc(B_87)
      | ~ m1_pre_topc(B_87,A_88)
      | ~ l1_pre_topc(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_73,plain,
    ( l1_pre_topc('#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_70])).

tff(c_76,plain,(
    l1_pre_topc('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_73])).

tff(c_30,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_94,plain,(
    ! [A_98,B_99] :
      ( k6_domain_1(A_98,B_99) = k1_tarski(B_99)
      | ~ m1_subset_1(B_99,A_98)
      | v1_xboole_0(A_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_110,plain,
    ( k6_domain_1(u1_struct_0('#skF_2'),'#skF_4') = k1_tarski('#skF_4')
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_30,c_94])).

tff(c_235,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_110])).

tff(c_20,plain,(
    ! [B_28,A_26] :
      ( r2_hidden(B_28,k1_connsp_2(A_26,B_28))
      | ~ m1_subset_1(B_28,u1_struct_0(A_26))
      | ~ l1_pre_topc(A_26)
      | ~ v2_pre_topc(A_26)
      | v2_struct_0(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_303,plain,(
    ! [A_154,B_155] :
      ( m1_subset_1(k1_connsp_2(A_154,B_155),k1_zfmisc_1(u1_struct_0(A_154)))
      | ~ m1_subset_1(B_155,u1_struct_0(A_154))
      | ~ l1_pre_topc(A_154)
      | ~ v2_pre_topc(A_154)
      | v2_struct_0(A_154) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_8,plain,(
    ! [C_8,B_7,A_6] :
      ( ~ v1_xboole_0(C_8)
      | ~ m1_subset_1(B_7,k1_zfmisc_1(C_8))
      | ~ r2_hidden(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_346,plain,(
    ! [A_163,A_164,B_165] :
      ( ~ v1_xboole_0(u1_struct_0(A_163))
      | ~ r2_hidden(A_164,k1_connsp_2(A_163,B_165))
      | ~ m1_subset_1(B_165,u1_struct_0(A_163))
      | ~ l1_pre_topc(A_163)
      | ~ v2_pre_topc(A_163)
      | v2_struct_0(A_163) ) ),
    inference(resolution,[status(thm)],[c_303,c_8])).

tff(c_356,plain,(
    ! [A_166,B_167] :
      ( ~ v1_xboole_0(u1_struct_0(A_166))
      | ~ m1_subset_1(B_167,u1_struct_0(A_166))
      | ~ l1_pre_topc(A_166)
      | ~ v2_pre_topc(A_166)
      | v2_struct_0(A_166) ) ),
    inference(resolution,[status(thm)],[c_20,c_346])).

tff(c_362,plain,
    ( ~ v1_xboole_0(u1_struct_0('#skF_2'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_356])).

tff(c_369,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_76,c_235,c_362])).

tff(c_371,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_369])).

tff(c_373,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_110])).

tff(c_6,plain,(
    ! [A_4,B_5] :
      ( r2_hidden(A_4,B_5)
      | v1_xboole_0(B_5)
      | ~ m1_subset_1(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_44,plain,(
    v4_tex_2('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_40,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_38,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_36,plain,(
    v5_pre_topc('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_32,plain,(
    v3_borsuk_1('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_34,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_4,plain,(
    ! [A_2,B_3] :
      ( m1_subset_1(k1_tarski(A_2),k1_zfmisc_1(B_3))
      | ~ r2_hidden(A_2,B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_54,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_50,plain,(
    v3_tdlat_3('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_374,plain,(
    ! [C_168,A_169,B_170] :
      ( m1_subset_1(C_168,k1_zfmisc_1(u1_struct_0(A_169)))
      | ~ m1_subset_1(C_168,k1_zfmisc_1(u1_struct_0(B_170)))
      | ~ m1_pre_topc(B_170,A_169)
      | ~ l1_pre_topc(A_169) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_405,plain,(
    ! [A_178,A_179,B_180] :
      ( m1_subset_1(k1_tarski(A_178),k1_zfmisc_1(u1_struct_0(A_179)))
      | ~ m1_pre_topc(B_180,A_179)
      | ~ l1_pre_topc(A_179)
      | ~ r2_hidden(A_178,u1_struct_0(B_180)) ) ),
    inference(resolution,[status(thm)],[c_4,c_374])).

tff(c_407,plain,(
    ! [A_178] :
      ( m1_subset_1(k1_tarski(A_178),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ r2_hidden(A_178,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_42,c_405])).

tff(c_410,plain,(
    ! [A_178] :
      ( m1_subset_1(k1_tarski(A_178),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ r2_hidden(A_178,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_407])).

tff(c_470,plain,(
    ! [A_195,B_196,C_197,E_198] :
      ( k8_relset_1(u1_struct_0(A_195),u1_struct_0(B_196),C_197,E_198) = k2_pre_topc(A_195,E_198)
      | ~ m1_subset_1(E_198,k1_zfmisc_1(u1_struct_0(A_195)))
      | ~ m1_subset_1(E_198,k1_zfmisc_1(u1_struct_0(B_196)))
      | ~ v3_borsuk_1(C_197,A_195,B_196)
      | ~ m1_subset_1(C_197,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_195),u1_struct_0(B_196))))
      | ~ v5_pre_topc(C_197,A_195,B_196)
      | ~ v1_funct_2(C_197,u1_struct_0(A_195),u1_struct_0(B_196))
      | ~ v1_funct_1(C_197)
      | ~ m1_pre_topc(B_196,A_195)
      | ~ v4_tex_2(B_196,A_195)
      | v2_struct_0(B_196)
      | ~ l1_pre_topc(A_195)
      | ~ v3_tdlat_3(A_195)
      | ~ v2_pre_topc(A_195)
      | v2_struct_0(A_195) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_476,plain,(
    ! [B_196,C_197,A_178] :
      ( k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0(B_196),C_197,k1_tarski(A_178)) = k2_pre_topc('#skF_1',k1_tarski(A_178))
      | ~ m1_subset_1(k1_tarski(A_178),k1_zfmisc_1(u1_struct_0(B_196)))
      | ~ v3_borsuk_1(C_197,'#skF_1',B_196)
      | ~ m1_subset_1(C_197,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_196))))
      | ~ v5_pre_topc(C_197,'#skF_1',B_196)
      | ~ v1_funct_2(C_197,u1_struct_0('#skF_1'),u1_struct_0(B_196))
      | ~ v1_funct_1(C_197)
      | ~ m1_pre_topc(B_196,'#skF_1')
      | ~ v4_tex_2(B_196,'#skF_1')
      | v2_struct_0(B_196)
      | ~ l1_pre_topc('#skF_1')
      | ~ v3_tdlat_3('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1')
      | ~ r2_hidden(A_178,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_410,c_470])).

tff(c_484,plain,(
    ! [B_196,C_197,A_178] :
      ( k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0(B_196),C_197,k1_tarski(A_178)) = k2_pre_topc('#skF_1',k1_tarski(A_178))
      | ~ m1_subset_1(k1_tarski(A_178),k1_zfmisc_1(u1_struct_0(B_196)))
      | ~ v3_borsuk_1(C_197,'#skF_1',B_196)
      | ~ m1_subset_1(C_197,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_196))))
      | ~ v5_pre_topc(C_197,'#skF_1',B_196)
      | ~ v1_funct_2(C_197,u1_struct_0('#skF_1'),u1_struct_0(B_196))
      | ~ v1_funct_1(C_197)
      | ~ m1_pre_topc(B_196,'#skF_1')
      | ~ v4_tex_2(B_196,'#skF_1')
      | v2_struct_0(B_196)
      | v2_struct_0('#skF_1')
      | ~ r2_hidden(A_178,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_476])).

tff(c_509,plain,(
    ! [B_207,C_208,A_209] :
      ( k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0(B_207),C_208,k1_tarski(A_209)) = k2_pre_topc('#skF_1',k1_tarski(A_209))
      | ~ m1_subset_1(k1_tarski(A_209),k1_zfmisc_1(u1_struct_0(B_207)))
      | ~ v3_borsuk_1(C_208,'#skF_1',B_207)
      | ~ m1_subset_1(C_208,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_207))))
      | ~ v5_pre_topc(C_208,'#skF_1',B_207)
      | ~ v1_funct_2(C_208,u1_struct_0('#skF_1'),u1_struct_0(B_207))
      | ~ v1_funct_1(C_208)
      | ~ m1_pre_topc(B_207,'#skF_1')
      | ~ v4_tex_2(B_207,'#skF_1')
      | v2_struct_0(B_207)
      | ~ r2_hidden(A_209,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_484])).

tff(c_683,plain,(
    ! [B_249,C_250,A_251] :
      ( k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0(B_249),C_250,k1_tarski(A_251)) = k2_pre_topc('#skF_1',k1_tarski(A_251))
      | ~ v3_borsuk_1(C_250,'#skF_1',B_249)
      | ~ m1_subset_1(C_250,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_249))))
      | ~ v5_pre_topc(C_250,'#skF_1',B_249)
      | ~ v1_funct_2(C_250,u1_struct_0('#skF_1'),u1_struct_0(B_249))
      | ~ v1_funct_1(C_250)
      | ~ m1_pre_topc(B_249,'#skF_1')
      | ~ v4_tex_2(B_249,'#skF_1')
      | v2_struct_0(B_249)
      | ~ r2_hidden(A_251,u1_struct_0('#skF_2'))
      | ~ r2_hidden(A_251,u1_struct_0(B_249)) ) ),
    inference(resolution,[status(thm)],[c_4,c_509])).

tff(c_685,plain,(
    ! [A_251] :
      ( k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',k1_tarski(A_251)) = k2_pre_topc('#skF_1',k1_tarski(A_251))
      | ~ v3_borsuk_1('#skF_3','#skF_1','#skF_2')
      | ~ v5_pre_topc('#skF_3','#skF_1','#skF_2')
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ m1_pre_topc('#skF_2','#skF_1')
      | ~ v4_tex_2('#skF_2','#skF_1')
      | v2_struct_0('#skF_2')
      | ~ r2_hidden(A_251,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_34,c_683])).

tff(c_691,plain,(
    ! [A_251] :
      ( k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',k1_tarski(A_251)) = k2_pre_topc('#skF_1',k1_tarski(A_251))
      | v2_struct_0('#skF_2')
      | ~ r2_hidden(A_251,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_38,c_36,c_32,c_685])).

tff(c_694,plain,(
    ! [A_252] :
      ( k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',k1_tarski(A_252)) = k2_pre_topc('#skF_1',k1_tarski(A_252))
      | ~ r2_hidden(A_252,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_691])).

tff(c_372,plain,(
    k6_domain_1(u1_struct_0('#skF_2'),'#skF_4') = k1_tarski('#skF_4') ),
    inference(splitRight,[status(thm)],[c_110])).

tff(c_26,plain,(
    '#skF_5' = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_28,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_55,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_28])).

tff(c_109,plain,
    ( k6_domain_1(u1_struct_0('#skF_1'),'#skF_4') = k1_tarski('#skF_4')
    | v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_55,c_94])).

tff(c_116,plain,(
    v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_109])).

tff(c_182,plain,(
    ! [A_123,B_124] :
      ( m1_subset_1(k1_connsp_2(A_123,B_124),k1_zfmisc_1(u1_struct_0(A_123)))
      | ~ m1_subset_1(B_124,u1_struct_0(A_123))
      | ~ l1_pre_topc(A_123)
      | ~ v2_pre_topc(A_123)
      | v2_struct_0(A_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_211,plain,(
    ! [A_129,A_130,B_131] :
      ( ~ v1_xboole_0(u1_struct_0(A_129))
      | ~ r2_hidden(A_130,k1_connsp_2(A_129,B_131))
      | ~ m1_subset_1(B_131,u1_struct_0(A_129))
      | ~ l1_pre_topc(A_129)
      | ~ v2_pre_topc(A_129)
      | v2_struct_0(A_129) ) ),
    inference(resolution,[status(thm)],[c_182,c_8])).

tff(c_221,plain,(
    ! [A_132,B_133] :
      ( ~ v1_xboole_0(u1_struct_0(A_132))
      | ~ m1_subset_1(B_133,u1_struct_0(A_132))
      | ~ l1_pre_topc(A_132)
      | ~ v2_pre_topc(A_132)
      | v2_struct_0(A_132) ) ),
    inference(resolution,[status(thm)],[c_20,c_211])).

tff(c_224,plain,
    ( ~ v1_xboole_0(u1_struct_0('#skF_1'))
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_55,c_221])).

tff(c_230,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_48,c_116,c_224])).

tff(c_232,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_230])).

tff(c_233,plain,(
    k6_domain_1(u1_struct_0('#skF_1'),'#skF_4') = k1_tarski('#skF_4') ),
    inference(splitRight,[status(thm)],[c_109])).

tff(c_24,plain,(
    k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',k6_domain_1(u1_struct_0('#skF_2'),'#skF_4')) != k2_pre_topc('#skF_1',k6_domain_1(u1_struct_0('#skF_1'),'#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_56,plain,(
    k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',k6_domain_1(u1_struct_0('#skF_2'),'#skF_4')) != k2_pre_topc('#skF_1',k6_domain_1(u1_struct_0('#skF_1'),'#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24])).

tff(c_391,plain,(
    k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',k1_tarski('#skF_4')) != k2_pre_topc('#skF_1',k1_tarski('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_372,c_233,c_56])).

tff(c_705,plain,(
    ~ r2_hidden('#skF_4',u1_struct_0('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_694,c_391])).

tff(c_714,plain,
    ( v1_xboole_0(u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_6,c_705])).

tff(c_717,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_714])).

tff(c_719,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_373,c_717])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 16:46:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.42/1.56  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.42/1.57  
% 3.42/1.57  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.42/1.57  %$ v5_pre_topc > v3_borsuk_1 > v1_funct_2 > v4_tex_2 > r2_hidden > m1_subset_1 > m1_pre_topc > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_pre_topc > k8_relset_1 > k6_domain_1 > k2_zfmisc_1 > k2_tarski > k2_pre_topc > k1_connsp_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.42/1.57  
% 3.42/1.57  %Foreground sorts:
% 3.42/1.57  
% 3.42/1.57  
% 3.42/1.57  %Background operators:
% 3.42/1.57  
% 3.42/1.57  
% 3.42/1.57  %Foreground operators:
% 3.42/1.57  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.42/1.57  tff(v3_borsuk_1, type, v3_borsuk_1: ($i * $i * $i) > $o).
% 3.42/1.57  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.42/1.57  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.42/1.57  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.42/1.57  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.42/1.57  tff(k1_connsp_2, type, k1_connsp_2: ($i * $i) > $i).
% 3.42/1.57  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 3.42/1.57  tff(v4_tex_2, type, v4_tex_2: ($i * $i) > $o).
% 3.42/1.57  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.42/1.57  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 3.42/1.57  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.42/1.57  tff('#skF_5', type, '#skF_5': $i).
% 3.42/1.57  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.42/1.57  tff('#skF_2', type, '#skF_2': $i).
% 3.42/1.57  tff('#skF_3', type, '#skF_3': $i).
% 3.42/1.57  tff('#skF_1', type, '#skF_1': $i).
% 3.42/1.57  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.42/1.57  tff(v3_tdlat_3, type, v3_tdlat_3: $i > $o).
% 3.42/1.57  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.42/1.57  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.42/1.57  tff('#skF_4', type, '#skF_4': $i).
% 3.42/1.57  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.42/1.57  tff(v5_pre_topc, type, v5_pre_topc: ($i * $i * $i) > $o).
% 3.42/1.57  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.42/1.57  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.42/1.57  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.42/1.57  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.42/1.57  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 3.42/1.57  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.42/1.57  
% 3.42/1.59  tff(f_177, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v4_tex_2(B, A)) & m1_pre_topc(B, A)) => (![C]: ((((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & v5_pre_topc(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (v3_borsuk_1(C, A, B) => (![D]: (m1_subset_1(D, u1_struct_0(B)) => (![E]: (m1_subset_1(E, u1_struct_0(A)) => ((D = E) => (k8_relset_1(u1_struct_0(A), u1_struct_0(B), C, k6_domain_1(u1_struct_0(B), D)) = k2_pre_topc(A, k6_domain_1(u1_struct_0(A), E))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_tex_2)).
% 3.42/1.59  tff(f_53, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_pre_topc)).
% 3.42/1.59  tff(f_60, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 3.42/1.59  tff(f_77, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 3.42/1.59  tff(f_100, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => r2_hidden(B, k1_connsp_2(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_connsp_2)).
% 3.42/1.59  tff(f_88, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => m1_subset_1(k1_connsp_2(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_connsp_2)).
% 3.42/1.59  tff(f_44, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 3.42/1.59  tff(f_37, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 3.42/1.59  tff(f_31, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(k1_tarski(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_subset_1)).
% 3.42/1.59  tff(f_70, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B))) => m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_pre_topc)).
% 3.42/1.59  tff(f_138, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v4_tex_2(B, A)) & m1_pre_topc(B, A)) => (![C]: ((((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & v5_pre_topc(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (v3_borsuk_1(C, A, B) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => (![E]: (m1_subset_1(E, k1_zfmisc_1(u1_struct_0(A))) => ((D = E) => (k8_relset_1(u1_struct_0(A), u1_struct_0(B), C, D) = k2_pre_topc(A, E)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t76_tex_2)).
% 3.42/1.59  tff(c_46, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_177])).
% 3.42/1.59  tff(c_52, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_177])).
% 3.42/1.59  tff(c_48, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_177])).
% 3.42/1.59  tff(c_42, plain, (m1_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_177])).
% 3.42/1.59  tff(c_79, plain, (![B_93, A_94]: (v2_pre_topc(B_93) | ~m1_pre_topc(B_93, A_94) | ~l1_pre_topc(A_94) | ~v2_pre_topc(A_94))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.42/1.59  tff(c_82, plain, (v2_pre_topc('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_42, c_79])).
% 3.42/1.59  tff(c_85, plain, (v2_pre_topc('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_48, c_82])).
% 3.42/1.59  tff(c_70, plain, (![B_87, A_88]: (l1_pre_topc(B_87) | ~m1_pre_topc(B_87, A_88) | ~l1_pre_topc(A_88))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.42/1.59  tff(c_73, plain, (l1_pre_topc('#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_42, c_70])).
% 3.42/1.59  tff(c_76, plain, (l1_pre_topc('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_73])).
% 3.42/1.59  tff(c_30, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_177])).
% 3.42/1.59  tff(c_94, plain, (![A_98, B_99]: (k6_domain_1(A_98, B_99)=k1_tarski(B_99) | ~m1_subset_1(B_99, A_98) | v1_xboole_0(A_98))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.42/1.59  tff(c_110, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_4')=k1_tarski('#skF_4') | v1_xboole_0(u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_30, c_94])).
% 3.42/1.59  tff(c_235, plain, (v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_110])).
% 3.42/1.59  tff(c_20, plain, (![B_28, A_26]: (r2_hidden(B_28, k1_connsp_2(A_26, B_28)) | ~m1_subset_1(B_28, u1_struct_0(A_26)) | ~l1_pre_topc(A_26) | ~v2_pre_topc(A_26) | v2_struct_0(A_26))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.42/1.59  tff(c_303, plain, (![A_154, B_155]: (m1_subset_1(k1_connsp_2(A_154, B_155), k1_zfmisc_1(u1_struct_0(A_154))) | ~m1_subset_1(B_155, u1_struct_0(A_154)) | ~l1_pre_topc(A_154) | ~v2_pre_topc(A_154) | v2_struct_0(A_154))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.42/1.59  tff(c_8, plain, (![C_8, B_7, A_6]: (~v1_xboole_0(C_8) | ~m1_subset_1(B_7, k1_zfmisc_1(C_8)) | ~r2_hidden(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.42/1.59  tff(c_346, plain, (![A_163, A_164, B_165]: (~v1_xboole_0(u1_struct_0(A_163)) | ~r2_hidden(A_164, k1_connsp_2(A_163, B_165)) | ~m1_subset_1(B_165, u1_struct_0(A_163)) | ~l1_pre_topc(A_163) | ~v2_pre_topc(A_163) | v2_struct_0(A_163))), inference(resolution, [status(thm)], [c_303, c_8])).
% 3.42/1.59  tff(c_356, plain, (![A_166, B_167]: (~v1_xboole_0(u1_struct_0(A_166)) | ~m1_subset_1(B_167, u1_struct_0(A_166)) | ~l1_pre_topc(A_166) | ~v2_pre_topc(A_166) | v2_struct_0(A_166))), inference(resolution, [status(thm)], [c_20, c_346])).
% 3.42/1.59  tff(c_362, plain, (~v1_xboole_0(u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_30, c_356])).
% 3.42/1.59  tff(c_369, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_85, c_76, c_235, c_362])).
% 3.42/1.59  tff(c_371, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_369])).
% 3.42/1.59  tff(c_373, plain, (~v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_110])).
% 3.42/1.59  tff(c_6, plain, (![A_4, B_5]: (r2_hidden(A_4, B_5) | v1_xboole_0(B_5) | ~m1_subset_1(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.42/1.59  tff(c_44, plain, (v4_tex_2('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_177])).
% 3.42/1.59  tff(c_40, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_177])).
% 3.42/1.59  tff(c_38, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_177])).
% 3.42/1.59  tff(c_36, plain, (v5_pre_topc('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_177])).
% 3.42/1.59  tff(c_32, plain, (v3_borsuk_1('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_177])).
% 3.42/1.59  tff(c_34, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_177])).
% 3.42/1.59  tff(c_4, plain, (![A_2, B_3]: (m1_subset_1(k1_tarski(A_2), k1_zfmisc_1(B_3)) | ~r2_hidden(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.42/1.59  tff(c_54, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_177])).
% 3.42/1.59  tff(c_50, plain, (v3_tdlat_3('#skF_1')), inference(cnfTransformation, [status(thm)], [f_177])).
% 3.42/1.59  tff(c_374, plain, (![C_168, A_169, B_170]: (m1_subset_1(C_168, k1_zfmisc_1(u1_struct_0(A_169))) | ~m1_subset_1(C_168, k1_zfmisc_1(u1_struct_0(B_170))) | ~m1_pre_topc(B_170, A_169) | ~l1_pre_topc(A_169))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.42/1.59  tff(c_405, plain, (![A_178, A_179, B_180]: (m1_subset_1(k1_tarski(A_178), k1_zfmisc_1(u1_struct_0(A_179))) | ~m1_pre_topc(B_180, A_179) | ~l1_pre_topc(A_179) | ~r2_hidden(A_178, u1_struct_0(B_180)))), inference(resolution, [status(thm)], [c_4, c_374])).
% 3.42/1.59  tff(c_407, plain, (![A_178]: (m1_subset_1(k1_tarski(A_178), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~r2_hidden(A_178, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_42, c_405])).
% 3.42/1.59  tff(c_410, plain, (![A_178]: (m1_subset_1(k1_tarski(A_178), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~r2_hidden(A_178, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_407])).
% 3.42/1.59  tff(c_470, plain, (![A_195, B_196, C_197, E_198]: (k8_relset_1(u1_struct_0(A_195), u1_struct_0(B_196), C_197, E_198)=k2_pre_topc(A_195, E_198) | ~m1_subset_1(E_198, k1_zfmisc_1(u1_struct_0(A_195))) | ~m1_subset_1(E_198, k1_zfmisc_1(u1_struct_0(B_196))) | ~v3_borsuk_1(C_197, A_195, B_196) | ~m1_subset_1(C_197, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_195), u1_struct_0(B_196)))) | ~v5_pre_topc(C_197, A_195, B_196) | ~v1_funct_2(C_197, u1_struct_0(A_195), u1_struct_0(B_196)) | ~v1_funct_1(C_197) | ~m1_pre_topc(B_196, A_195) | ~v4_tex_2(B_196, A_195) | v2_struct_0(B_196) | ~l1_pre_topc(A_195) | ~v3_tdlat_3(A_195) | ~v2_pre_topc(A_195) | v2_struct_0(A_195))), inference(cnfTransformation, [status(thm)], [f_138])).
% 3.42/1.59  tff(c_476, plain, (![B_196, C_197, A_178]: (k8_relset_1(u1_struct_0('#skF_1'), u1_struct_0(B_196), C_197, k1_tarski(A_178))=k2_pre_topc('#skF_1', k1_tarski(A_178)) | ~m1_subset_1(k1_tarski(A_178), k1_zfmisc_1(u1_struct_0(B_196))) | ~v3_borsuk_1(C_197, '#skF_1', B_196) | ~m1_subset_1(C_197, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_196)))) | ~v5_pre_topc(C_197, '#skF_1', B_196) | ~v1_funct_2(C_197, u1_struct_0('#skF_1'), u1_struct_0(B_196)) | ~v1_funct_1(C_197) | ~m1_pre_topc(B_196, '#skF_1') | ~v4_tex_2(B_196, '#skF_1') | v2_struct_0(B_196) | ~l1_pre_topc('#skF_1') | ~v3_tdlat_3('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1') | ~r2_hidden(A_178, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_410, c_470])).
% 3.42/1.59  tff(c_484, plain, (![B_196, C_197, A_178]: (k8_relset_1(u1_struct_0('#skF_1'), u1_struct_0(B_196), C_197, k1_tarski(A_178))=k2_pre_topc('#skF_1', k1_tarski(A_178)) | ~m1_subset_1(k1_tarski(A_178), k1_zfmisc_1(u1_struct_0(B_196))) | ~v3_borsuk_1(C_197, '#skF_1', B_196) | ~m1_subset_1(C_197, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_196)))) | ~v5_pre_topc(C_197, '#skF_1', B_196) | ~v1_funct_2(C_197, u1_struct_0('#skF_1'), u1_struct_0(B_196)) | ~v1_funct_1(C_197) | ~m1_pre_topc(B_196, '#skF_1') | ~v4_tex_2(B_196, '#skF_1') | v2_struct_0(B_196) | v2_struct_0('#skF_1') | ~r2_hidden(A_178, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_476])).
% 3.42/1.59  tff(c_509, plain, (![B_207, C_208, A_209]: (k8_relset_1(u1_struct_0('#skF_1'), u1_struct_0(B_207), C_208, k1_tarski(A_209))=k2_pre_topc('#skF_1', k1_tarski(A_209)) | ~m1_subset_1(k1_tarski(A_209), k1_zfmisc_1(u1_struct_0(B_207))) | ~v3_borsuk_1(C_208, '#skF_1', B_207) | ~m1_subset_1(C_208, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_207)))) | ~v5_pre_topc(C_208, '#skF_1', B_207) | ~v1_funct_2(C_208, u1_struct_0('#skF_1'), u1_struct_0(B_207)) | ~v1_funct_1(C_208) | ~m1_pre_topc(B_207, '#skF_1') | ~v4_tex_2(B_207, '#skF_1') | v2_struct_0(B_207) | ~r2_hidden(A_209, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_54, c_484])).
% 3.42/1.59  tff(c_683, plain, (![B_249, C_250, A_251]: (k8_relset_1(u1_struct_0('#skF_1'), u1_struct_0(B_249), C_250, k1_tarski(A_251))=k2_pre_topc('#skF_1', k1_tarski(A_251)) | ~v3_borsuk_1(C_250, '#skF_1', B_249) | ~m1_subset_1(C_250, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_249)))) | ~v5_pre_topc(C_250, '#skF_1', B_249) | ~v1_funct_2(C_250, u1_struct_0('#skF_1'), u1_struct_0(B_249)) | ~v1_funct_1(C_250) | ~m1_pre_topc(B_249, '#skF_1') | ~v4_tex_2(B_249, '#skF_1') | v2_struct_0(B_249) | ~r2_hidden(A_251, u1_struct_0('#skF_2')) | ~r2_hidden(A_251, u1_struct_0(B_249)))), inference(resolution, [status(thm)], [c_4, c_509])).
% 3.42/1.59  tff(c_685, plain, (![A_251]: (k8_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', k1_tarski(A_251))=k2_pre_topc('#skF_1', k1_tarski(A_251)) | ~v3_borsuk_1('#skF_3', '#skF_1', '#skF_2') | ~v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | ~v4_tex_2('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~r2_hidden(A_251, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_34, c_683])).
% 3.42/1.59  tff(c_691, plain, (![A_251]: (k8_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', k1_tarski(A_251))=k2_pre_topc('#skF_1', k1_tarski(A_251)) | v2_struct_0('#skF_2') | ~r2_hidden(A_251, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_38, c_36, c_32, c_685])).
% 3.42/1.59  tff(c_694, plain, (![A_252]: (k8_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', k1_tarski(A_252))=k2_pre_topc('#skF_1', k1_tarski(A_252)) | ~r2_hidden(A_252, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_46, c_691])).
% 3.42/1.59  tff(c_372, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_4')=k1_tarski('#skF_4')), inference(splitRight, [status(thm)], [c_110])).
% 3.42/1.59  tff(c_26, plain, ('#skF_5'='#skF_4'), inference(cnfTransformation, [status(thm)], [f_177])).
% 3.42/1.59  tff(c_28, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_177])).
% 3.42/1.59  tff(c_55, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_28])).
% 3.42/1.59  tff(c_109, plain, (k6_domain_1(u1_struct_0('#skF_1'), '#skF_4')=k1_tarski('#skF_4') | v1_xboole_0(u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_55, c_94])).
% 3.42/1.59  tff(c_116, plain, (v1_xboole_0(u1_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_109])).
% 3.42/1.59  tff(c_182, plain, (![A_123, B_124]: (m1_subset_1(k1_connsp_2(A_123, B_124), k1_zfmisc_1(u1_struct_0(A_123))) | ~m1_subset_1(B_124, u1_struct_0(A_123)) | ~l1_pre_topc(A_123) | ~v2_pre_topc(A_123) | v2_struct_0(A_123))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.42/1.59  tff(c_211, plain, (![A_129, A_130, B_131]: (~v1_xboole_0(u1_struct_0(A_129)) | ~r2_hidden(A_130, k1_connsp_2(A_129, B_131)) | ~m1_subset_1(B_131, u1_struct_0(A_129)) | ~l1_pre_topc(A_129) | ~v2_pre_topc(A_129) | v2_struct_0(A_129))), inference(resolution, [status(thm)], [c_182, c_8])).
% 3.42/1.59  tff(c_221, plain, (![A_132, B_133]: (~v1_xboole_0(u1_struct_0(A_132)) | ~m1_subset_1(B_133, u1_struct_0(A_132)) | ~l1_pre_topc(A_132) | ~v2_pre_topc(A_132) | v2_struct_0(A_132))), inference(resolution, [status(thm)], [c_20, c_211])).
% 3.42/1.59  tff(c_224, plain, (~v1_xboole_0(u1_struct_0('#skF_1')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_55, c_221])).
% 3.42/1.59  tff(c_230, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_48, c_116, c_224])).
% 3.42/1.59  tff(c_232, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_230])).
% 3.42/1.59  tff(c_233, plain, (k6_domain_1(u1_struct_0('#skF_1'), '#skF_4')=k1_tarski('#skF_4')), inference(splitRight, [status(thm)], [c_109])).
% 3.42/1.59  tff(c_24, plain, (k8_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', k6_domain_1(u1_struct_0('#skF_2'), '#skF_4'))!=k2_pre_topc('#skF_1', k6_domain_1(u1_struct_0('#skF_1'), '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_177])).
% 3.42/1.59  tff(c_56, plain, (k8_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', k6_domain_1(u1_struct_0('#skF_2'), '#skF_4'))!=k2_pre_topc('#skF_1', k6_domain_1(u1_struct_0('#skF_1'), '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24])).
% 3.42/1.59  tff(c_391, plain, (k8_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', k1_tarski('#skF_4'))!=k2_pre_topc('#skF_1', k1_tarski('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_372, c_233, c_56])).
% 3.42/1.59  tff(c_705, plain, (~r2_hidden('#skF_4', u1_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_694, c_391])).
% 3.42/1.59  tff(c_714, plain, (v1_xboole_0(u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_6, c_705])).
% 3.42/1.59  tff(c_717, plain, (v1_xboole_0(u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_714])).
% 3.42/1.59  tff(c_719, plain, $false, inference(negUnitSimplification, [status(thm)], [c_373, c_717])).
% 3.42/1.59  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.42/1.59  
% 3.42/1.59  Inference rules
% 3.42/1.59  ----------------------
% 3.42/1.59  #Ref     : 0
% 3.42/1.59  #Sup     : 145
% 3.42/1.59  #Fact    : 0
% 3.42/1.59  #Define  : 0
% 3.42/1.59  #Split   : 14
% 3.42/1.59  #Chain   : 0
% 3.42/1.59  #Close   : 0
% 3.42/1.59  
% 3.42/1.59  Ordering : KBO
% 3.42/1.59  
% 3.42/1.59  Simplification rules
% 3.42/1.59  ----------------------
% 3.42/1.59  #Subsume      : 13
% 3.42/1.59  #Demod        : 52
% 3.42/1.59  #Tautology    : 40
% 3.42/1.59  #SimpNegUnit  : 16
% 3.42/1.59  #BackRed      : 0
% 3.42/1.59  
% 3.42/1.59  #Partial instantiations: 0
% 3.42/1.59  #Strategies tried      : 1
% 3.42/1.59  
% 3.42/1.59  Timing (in seconds)
% 3.42/1.59  ----------------------
% 3.42/1.59  Preprocessing        : 0.34
% 3.42/1.59  Parsing              : 0.18
% 3.42/1.59  CNF conversion       : 0.03
% 3.42/1.59  Main loop            : 0.43
% 3.42/1.59  Inferencing          : 0.16
% 3.42/1.59  Reduction            : 0.12
% 3.42/1.59  Demodulation         : 0.08
% 3.42/1.59  BG Simplification    : 0.02
% 3.42/1.59  Subsumption          : 0.10
% 3.42/1.59  Abstraction          : 0.02
% 3.42/1.59  MUC search           : 0.00
% 3.42/1.59  Cooper               : 0.00
% 3.42/1.59  Total                : 0.81
% 3.42/1.59  Index Insertion      : 0.00
% 3.42/1.59  Index Deletion       : 0.00
% 3.42/1.59  Index Matching       : 0.00
% 3.42/1.59  BG Taut test         : 0.00
%------------------------------------------------------------------------------
