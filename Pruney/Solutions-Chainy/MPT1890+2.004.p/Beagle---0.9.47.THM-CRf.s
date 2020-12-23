%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:24 EST 2020

% Result     : Theorem 15.32s
% Output     : CNFRefutation 15.32s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 222 expanded)
%              Number of leaves         :   28 (  94 expanded)
%              Depth                    :   21
%              Number of atoms          :  173 ( 760 expanded)
%              Number of equality atoms :   26 ( 103 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_pre_topc > v2_tex_2 > r2_hidden > m1_subset_1 > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > l1_pre_topc > k9_subset_1 > k6_domain_1 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_108,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & v3_tdlat_3(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( ! [C] :
                  ( m1_subset_1(C,u1_struct_0(A))
                 => ( r2_hidden(C,B)
                   => k9_subset_1(u1_struct_0(A),B,k2_pre_topc(A,k6_domain_1(u1_struct_0(A),C))) = k6_domain_1(u1_struct_0(A),C) ) )
             => v2_tex_2(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_tex_2)).

tff(f_86,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ~ ( r2_hidden(C,B)
                    & ! [D] :
                        ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                       => ~ ( v3_pre_topc(D,A)
                            & k9_subset_1(u1_struct_0(A),B,D) = k6_domain_1(u1_struct_0(A),C) ) ) ) )
           => v2_tex_2(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_tex_2)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => m1_subset_1(k9_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_subset_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k9_subset_1(A,C,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k9_subset_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v4_pre_topc(k2_pre_topc(A,B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_tops_1)).

tff(f_60,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ( v3_tdlat_3(A)
      <=> ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
             => v3_pre_topc(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_tdlat_3)).

tff(c_36,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_24,plain,(
    ~ v2_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_34,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_30,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_28,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_22,plain,(
    ! [A_15,B_23] :
      ( m1_subset_1('#skF_2'(A_15,B_23),u1_struct_0(A_15))
      | v2_tex_2(B_23,A_15)
      | ~ m1_subset_1(B_23,k1_zfmisc_1(u1_struct_0(A_15)))
      | ~ l1_pre_topc(A_15)
      | ~ v2_pre_topc(A_15)
      | v2_struct_0(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_234,plain,(
    ! [A_67,B_68] :
      ( r2_hidden('#skF_2'(A_67,B_68),B_68)
      | v2_tex_2(B_68,A_67)
      | ~ m1_subset_1(B_68,k1_zfmisc_1(u1_struct_0(A_67)))
      | ~ l1_pre_topc(A_67)
      | ~ v2_pre_topc(A_67)
      | v2_struct_0(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_249,plain,
    ( r2_hidden('#skF_2'('#skF_3','#skF_4'),'#skF_4')
    | v2_tex_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_234])).

tff(c_267,plain,
    ( r2_hidden('#skF_2'('#skF_3','#skF_4'),'#skF_4')
    | v2_tex_2('#skF_4','#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_249])).

tff(c_268,plain,(
    r2_hidden('#skF_2'('#skF_3','#skF_4'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_24,c_267])).

tff(c_26,plain,(
    ! [C_33] :
      ( k9_subset_1(u1_struct_0('#skF_3'),'#skF_4',k2_pre_topc('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),C_33))) = k6_domain_1(u1_struct_0('#skF_3'),C_33)
      | ~ r2_hidden(C_33,'#skF_4')
      | ~ m1_subset_1(C_33,u1_struct_0('#skF_3')) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_4,plain,(
    ! [A_4,B_5,C_6] :
      ( m1_subset_1(k9_subset_1(A_4,B_5,C_6),k1_zfmisc_1(A_4))
      | ~ m1_subset_1(C_6,k1_zfmisc_1(A_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_103,plain,(
    ! [A_47,B_48] :
      ( m1_subset_1(k2_pre_topc(A_47,B_48),k1_zfmisc_1(u1_struct_0(A_47)))
      | ~ m1_subset_1(B_48,k1_zfmisc_1(u1_struct_0(A_47)))
      | ~ l1_pre_topc(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( k9_subset_1(A_1,C_3,B_2) = k9_subset_1(A_1,B_2,C_3)
      | ~ m1_subset_1(C_3,k1_zfmisc_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_3024,plain,(
    ! [A_125,B_126,B_127] :
      ( k9_subset_1(u1_struct_0(A_125),k2_pre_topc(A_125,B_126),B_127) = k9_subset_1(u1_struct_0(A_125),B_127,k2_pre_topc(A_125,B_126))
      | ~ m1_subset_1(B_126,k1_zfmisc_1(u1_struct_0(A_125)))
      | ~ l1_pre_topc(A_125) ) ),
    inference(resolution,[status(thm)],[c_103,c_2])).

tff(c_15807,plain,(
    ! [A_265,B_266,C_267,B_268] :
      ( k9_subset_1(u1_struct_0(A_265),k2_pre_topc(A_265,k9_subset_1(u1_struct_0(A_265),B_266,C_267)),B_268) = k9_subset_1(u1_struct_0(A_265),B_268,k2_pre_topc(A_265,k9_subset_1(u1_struct_0(A_265),B_266,C_267)))
      | ~ l1_pre_topc(A_265)
      | ~ m1_subset_1(C_267,k1_zfmisc_1(u1_struct_0(A_265))) ) ),
    inference(resolution,[status(thm)],[c_4,c_3024])).

tff(c_52,plain,(
    ! [A_40,C_41,B_42] :
      ( k9_subset_1(A_40,C_41,B_42) = k9_subset_1(A_40,B_42,C_41)
      | ~ m1_subset_1(C_41,k1_zfmisc_1(A_40)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_58,plain,(
    ! [B_42] : k9_subset_1(u1_struct_0('#skF_3'),B_42,'#skF_4') = k9_subset_1(u1_struct_0('#skF_3'),'#skF_4',B_42) ),
    inference(resolution,[status(thm)],[c_28,c_52])).

tff(c_59,plain,(
    ! [B_43] : k9_subset_1(u1_struct_0('#skF_3'),B_43,'#skF_4') = k9_subset_1(u1_struct_0('#skF_3'),'#skF_4',B_43) ),
    inference(resolution,[status(thm)],[c_28,c_52])).

tff(c_71,plain,(
    ! [B_43] :
      ( m1_subset_1(k9_subset_1(u1_struct_0('#skF_3'),'#skF_4',B_43),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_59,c_4])).

tff(c_81,plain,(
    ! [B_43] : m1_subset_1(k9_subset_1(u1_struct_0('#skF_3'),'#skF_4',B_43),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_71])).

tff(c_3044,plain,(
    ! [B_43,B_127] :
      ( k9_subset_1(u1_struct_0('#skF_3'),k2_pre_topc('#skF_3',k9_subset_1(u1_struct_0('#skF_3'),'#skF_4',B_43)),B_127) = k9_subset_1(u1_struct_0('#skF_3'),B_127,k2_pre_topc('#skF_3',k9_subset_1(u1_struct_0('#skF_3'),'#skF_4',B_43)))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_81,c_3024])).

tff(c_6026,plain,(
    ! [B_182,B_183] : k9_subset_1(u1_struct_0('#skF_3'),k2_pre_topc('#skF_3',k9_subset_1(u1_struct_0('#skF_3'),'#skF_4',B_182)),B_183) = k9_subset_1(u1_struct_0('#skF_3'),B_183,k2_pre_topc('#skF_3',k9_subset_1(u1_struct_0('#skF_3'),'#skF_4',B_182))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_3044])).

tff(c_6443,plain,(
    ! [B_42,B_183] : k9_subset_1(u1_struct_0('#skF_3'),k2_pre_topc('#skF_3',k9_subset_1(u1_struct_0('#skF_3'),B_42,'#skF_4')),B_183) = k9_subset_1(u1_struct_0('#skF_3'),B_183,k2_pre_topc('#skF_3',k9_subset_1(u1_struct_0('#skF_3'),'#skF_4',B_42))) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_6026])).

tff(c_15981,plain,(
    ! [B_268,B_266] :
      ( k9_subset_1(u1_struct_0('#skF_3'),B_268,k2_pre_topc('#skF_3',k9_subset_1(u1_struct_0('#skF_3'),B_266,'#skF_4'))) = k9_subset_1(u1_struct_0('#skF_3'),B_268,k2_pre_topc('#skF_3',k9_subset_1(u1_struct_0('#skF_3'),'#skF_4',B_266)))
      | ~ l1_pre_topc('#skF_3')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_15807,c_6443])).

tff(c_16901,plain,(
    ! [B_268,B_266] : k9_subset_1(u1_struct_0('#skF_3'),B_268,k2_pre_topc('#skF_3',k9_subset_1(u1_struct_0('#skF_3'),B_266,'#skF_4'))) = k9_subset_1(u1_struct_0('#skF_3'),B_268,k2_pre_topc('#skF_3',k9_subset_1(u1_struct_0('#skF_3'),'#skF_4',B_266))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_30,c_15981])).

tff(c_6,plain,(
    ! [A_7,B_8] :
      ( m1_subset_1(k2_pre_topc(A_7,B_8),k1_zfmisc_1(u1_struct_0(A_7)))
      | ~ m1_subset_1(B_8,k1_zfmisc_1(u1_struct_0(A_7)))
      | ~ l1_pre_topc(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_32,plain,(
    v3_tdlat_3('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_107,plain,(
    ! [A_49,B_50] :
      ( v4_pre_topc(k2_pre_topc(A_49,B_50),A_49)
      | ~ m1_subset_1(B_50,k1_zfmisc_1(u1_struct_0(A_49)))
      | ~ l1_pre_topc(A_49)
      | ~ v2_pre_topc(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_115,plain,(
    ! [B_43] :
      ( v4_pre_topc(k2_pre_topc('#skF_3',k9_subset_1(u1_struct_0('#skF_3'),'#skF_4',B_43)),'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_81,c_107])).

tff(c_128,plain,(
    ! [B_43] : v4_pre_topc(k2_pre_topc('#skF_3',k9_subset_1(u1_struct_0('#skF_3'),'#skF_4',B_43)),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_115])).

tff(c_155,plain,(
    ! [B_56,A_57] :
      ( v3_pre_topc(B_56,A_57)
      | ~ v4_pre_topc(B_56,A_57)
      | ~ m1_subset_1(B_56,k1_zfmisc_1(u1_struct_0(A_57)))
      | ~ v3_tdlat_3(A_57)
      | ~ l1_pre_topc(A_57)
      | ~ v2_pre_topc(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_2666,plain,(
    ! [A_114,B_115] :
      ( v3_pre_topc(k2_pre_topc(A_114,B_115),A_114)
      | ~ v4_pre_topc(k2_pre_topc(A_114,B_115),A_114)
      | ~ v3_tdlat_3(A_114)
      | ~ v2_pre_topc(A_114)
      | ~ m1_subset_1(B_115,k1_zfmisc_1(u1_struct_0(A_114)))
      | ~ l1_pre_topc(A_114) ) ),
    inference(resolution,[status(thm)],[c_6,c_155])).

tff(c_2688,plain,(
    ! [B_43] :
      ( v3_pre_topc(k2_pre_topc('#skF_3',k9_subset_1(u1_struct_0('#skF_3'),'#skF_4',B_43)),'#skF_3')
      | ~ v3_tdlat_3('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | ~ m1_subset_1(k9_subset_1(u1_struct_0('#skF_3'),'#skF_4',B_43),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_128,c_2666])).

tff(c_2717,plain,(
    ! [B_43] : v3_pre_topc(k2_pre_topc('#skF_3',k9_subset_1(u1_struct_0('#skF_3'),'#skF_4',B_43)),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_81,c_34,c_32,c_2688])).

tff(c_8524,plain,(
    ! [B_214,B_215] : k9_subset_1(u1_struct_0('#skF_3'),k2_pre_topc('#skF_3',k9_subset_1(u1_struct_0('#skF_3'),'#skF_4',B_214)),B_215) = k9_subset_1(u1_struct_0('#skF_3'),B_215,k2_pre_topc('#skF_3',k9_subset_1(u1_struct_0('#skF_3'),B_214,'#skF_4'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_6026])).

tff(c_34551,plain,(
    ! [B_349] : k9_subset_1(u1_struct_0('#skF_3'),'#skF_4',k2_pre_topc('#skF_3',k9_subset_1(u1_struct_0('#skF_3'),B_349,'#skF_4'))) = k9_subset_1(u1_struct_0('#skF_3'),'#skF_4',k2_pre_topc('#skF_3',k9_subset_1(u1_struct_0('#skF_3'),'#skF_4',B_349))) ),
    inference(superposition,[status(thm),theory(equality)],[c_8524,c_58])).

tff(c_18,plain,(
    ! [A_15,B_23,D_28] :
      ( k9_subset_1(u1_struct_0(A_15),B_23,D_28) != k6_domain_1(u1_struct_0(A_15),'#skF_2'(A_15,B_23))
      | ~ v3_pre_topc(D_28,A_15)
      | ~ m1_subset_1(D_28,k1_zfmisc_1(u1_struct_0(A_15)))
      | v2_tex_2(B_23,A_15)
      | ~ m1_subset_1(B_23,k1_zfmisc_1(u1_struct_0(A_15)))
      | ~ l1_pre_topc(A_15)
      | ~ v2_pre_topc(A_15)
      | v2_struct_0(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_34809,plain,(
    ! [B_349] :
      ( k9_subset_1(u1_struct_0('#skF_3'),'#skF_4',k2_pre_topc('#skF_3',k9_subset_1(u1_struct_0('#skF_3'),B_349,'#skF_4'))) != k6_domain_1(u1_struct_0('#skF_3'),'#skF_2'('#skF_3','#skF_4'))
      | ~ v3_pre_topc(k2_pre_topc('#skF_3',k9_subset_1(u1_struct_0('#skF_3'),'#skF_4',B_349)),'#skF_3')
      | ~ m1_subset_1(k2_pre_topc('#skF_3',k9_subset_1(u1_struct_0('#skF_3'),'#skF_4',B_349)),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_tex_2('#skF_4','#skF_3')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34551,c_18])).

tff(c_35053,plain,(
    ! [B_349] :
      ( k9_subset_1(u1_struct_0('#skF_3'),'#skF_4',k2_pre_topc('#skF_3',k9_subset_1(u1_struct_0('#skF_3'),B_349,'#skF_4'))) != k6_domain_1(u1_struct_0('#skF_3'),'#skF_2'('#skF_3','#skF_4'))
      | ~ m1_subset_1(k2_pre_topc('#skF_3',k9_subset_1(u1_struct_0('#skF_3'),'#skF_4',B_349)),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_tex_2('#skF_4','#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_28,c_2717,c_34809])).

tff(c_40632,plain,(
    ! [B_371] :
      ( k9_subset_1(u1_struct_0('#skF_3'),'#skF_4',k2_pre_topc('#skF_3',k9_subset_1(u1_struct_0('#skF_3'),B_371,'#skF_4'))) != k6_domain_1(u1_struct_0('#skF_3'),'#skF_2'('#skF_3','#skF_4'))
      | ~ m1_subset_1(k2_pre_topc('#skF_3',k9_subset_1(u1_struct_0('#skF_3'),'#skF_4',B_371)),k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_24,c_35053])).

tff(c_40659,plain,(
    ! [B_371] :
      ( k9_subset_1(u1_struct_0('#skF_3'),'#skF_4',k2_pre_topc('#skF_3',k9_subset_1(u1_struct_0('#skF_3'),B_371,'#skF_4'))) != k6_domain_1(u1_struct_0('#skF_3'),'#skF_2'('#skF_3','#skF_4'))
      | ~ m1_subset_1(k9_subset_1(u1_struct_0('#skF_3'),'#skF_4',B_371),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_6,c_40632])).

tff(c_40676,plain,(
    ! [B_372] : k9_subset_1(u1_struct_0('#skF_3'),'#skF_4',k2_pre_topc('#skF_3',k9_subset_1(u1_struct_0('#skF_3'),B_372,'#skF_4'))) != k6_domain_1(u1_struct_0('#skF_3'),'#skF_2'('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_81,c_40659])).

tff(c_40809,plain,(
    ! [B_373] : k9_subset_1(u1_struct_0('#skF_3'),'#skF_4',k2_pre_topc('#skF_3',k9_subset_1(u1_struct_0('#skF_3'),'#skF_4',B_373))) != k6_domain_1(u1_struct_0('#skF_3'),'#skF_2'('#skF_3','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_16901,c_40676])).

tff(c_41177,plain,(
    ! [C_377] :
      ( k9_subset_1(u1_struct_0('#skF_3'),'#skF_4',k2_pre_topc('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),C_377))) != k6_domain_1(u1_struct_0('#skF_3'),'#skF_2'('#skF_3','#skF_4'))
      | ~ r2_hidden(C_377,'#skF_4')
      | ~ m1_subset_1(C_377,u1_struct_0('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_40809])).

tff(c_41180,plain,(
    ! [C_33] :
      ( k6_domain_1(u1_struct_0('#skF_3'),C_33) != k6_domain_1(u1_struct_0('#skF_3'),'#skF_2'('#skF_3','#skF_4'))
      | ~ r2_hidden(C_33,'#skF_4')
      | ~ m1_subset_1(C_33,u1_struct_0('#skF_3'))
      | ~ r2_hidden(C_33,'#skF_4')
      | ~ m1_subset_1(C_33,u1_struct_0('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_41177])).

tff(c_42087,plain,
    ( ~ r2_hidden('#skF_2'('#skF_3','#skF_4'),'#skF_4')
    | ~ m1_subset_1('#skF_2'('#skF_3','#skF_4'),u1_struct_0('#skF_3'))
    | ~ r2_hidden('#skF_2'('#skF_3','#skF_4'),'#skF_4')
    | ~ m1_subset_1('#skF_2'('#skF_3','#skF_4'),u1_struct_0('#skF_3')) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_41180])).

tff(c_42089,plain,(
    ~ m1_subset_1('#skF_2'('#skF_3','#skF_4'),u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_268,c_268,c_42087])).

tff(c_42093,plain,
    ( v2_tex_2('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_42089])).

tff(c_42096,plain,
    ( v2_tex_2('#skF_4','#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_28,c_42093])).

tff(c_42098,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_24,c_42096])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:02:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 15.32/8.13  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 15.32/8.14  
% 15.32/8.14  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 15.32/8.14  %$ v4_pre_topc > v3_pre_topc > v2_tex_2 > r2_hidden > m1_subset_1 > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > l1_pre_topc > k9_subset_1 > k6_domain_1 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 15.32/8.14  
% 15.32/8.14  %Foreground sorts:
% 15.32/8.14  
% 15.32/8.14  
% 15.32/8.14  %Background operators:
% 15.32/8.14  
% 15.32/8.14  
% 15.32/8.14  %Foreground operators:
% 15.32/8.14  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 15.32/8.14  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 15.32/8.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 15.32/8.14  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 15.32/8.14  tff('#skF_1', type, '#skF_1': $i > $i).
% 15.32/8.14  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 15.32/8.14  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 15.32/8.14  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 15.32/8.14  tff('#skF_3', type, '#skF_3': $i).
% 15.32/8.14  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 15.32/8.14  tff(v3_tdlat_3, type, v3_tdlat_3: $i > $o).
% 15.32/8.14  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 15.32/8.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 15.32/8.14  tff('#skF_4', type, '#skF_4': $i).
% 15.32/8.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 15.32/8.14  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 15.32/8.14  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 15.32/8.14  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 15.32/8.14  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 15.32/8.14  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 15.32/8.14  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 15.32/8.14  
% 15.32/8.15  tff(f_108, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_hidden(C, B) => (k9_subset_1(u1_struct_0(A), B, k2_pre_topc(A, k6_domain_1(u1_struct_0(A), C))) = k6_domain_1(u1_struct_0(A), C))))) => v2_tex_2(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t58_tex_2)).
% 15.32/8.15  tff(f_86, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((![C]: (m1_subset_1(C, u1_struct_0(A)) => ~(r2_hidden(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(v3_pre_topc(D, A) & (k9_subset_1(u1_struct_0(A), B, D) = k6_domain_1(u1_struct_0(A), C)))))))) => v2_tex_2(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_tex_2)).
% 15.32/8.15  tff(f_33, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => m1_subset_1(k9_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k9_subset_1)).
% 15.32/8.15  tff(f_39, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 15.32/8.15  tff(f_29, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k9_subset_1(A, C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k9_subset_1)).
% 15.32/8.15  tff(f_47, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v4_pre_topc(k2_pre_topc(A, B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_tops_1)).
% 15.32/8.15  tff(f_60, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (v3_tdlat_3(A) <=> (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => v3_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_tdlat_3)).
% 15.32/8.15  tff(c_36, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_108])).
% 15.32/8.15  tff(c_24, plain, (~v2_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_108])).
% 15.32/8.15  tff(c_34, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_108])).
% 15.32/8.15  tff(c_30, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_108])).
% 15.32/8.15  tff(c_28, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_108])).
% 15.32/8.15  tff(c_22, plain, (![A_15, B_23]: (m1_subset_1('#skF_2'(A_15, B_23), u1_struct_0(A_15)) | v2_tex_2(B_23, A_15) | ~m1_subset_1(B_23, k1_zfmisc_1(u1_struct_0(A_15))) | ~l1_pre_topc(A_15) | ~v2_pre_topc(A_15) | v2_struct_0(A_15))), inference(cnfTransformation, [status(thm)], [f_86])).
% 15.32/8.15  tff(c_234, plain, (![A_67, B_68]: (r2_hidden('#skF_2'(A_67, B_68), B_68) | v2_tex_2(B_68, A_67) | ~m1_subset_1(B_68, k1_zfmisc_1(u1_struct_0(A_67))) | ~l1_pre_topc(A_67) | ~v2_pre_topc(A_67) | v2_struct_0(A_67))), inference(cnfTransformation, [status(thm)], [f_86])).
% 15.32/8.15  tff(c_249, plain, (r2_hidden('#skF_2'('#skF_3', '#skF_4'), '#skF_4') | v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_28, c_234])).
% 15.32/8.15  tff(c_267, plain, (r2_hidden('#skF_2'('#skF_3', '#skF_4'), '#skF_4') | v2_tex_2('#skF_4', '#skF_3') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_30, c_249])).
% 15.32/8.15  tff(c_268, plain, (r2_hidden('#skF_2'('#skF_3', '#skF_4'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_36, c_24, c_267])).
% 15.32/8.15  tff(c_26, plain, (![C_33]: (k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', k2_pre_topc('#skF_3', k6_domain_1(u1_struct_0('#skF_3'), C_33)))=k6_domain_1(u1_struct_0('#skF_3'), C_33) | ~r2_hidden(C_33, '#skF_4') | ~m1_subset_1(C_33, u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_108])).
% 15.32/8.15  tff(c_4, plain, (![A_4, B_5, C_6]: (m1_subset_1(k9_subset_1(A_4, B_5, C_6), k1_zfmisc_1(A_4)) | ~m1_subset_1(C_6, k1_zfmisc_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 15.32/8.15  tff(c_103, plain, (![A_47, B_48]: (m1_subset_1(k2_pre_topc(A_47, B_48), k1_zfmisc_1(u1_struct_0(A_47))) | ~m1_subset_1(B_48, k1_zfmisc_1(u1_struct_0(A_47))) | ~l1_pre_topc(A_47))), inference(cnfTransformation, [status(thm)], [f_39])).
% 15.32/8.15  tff(c_2, plain, (![A_1, C_3, B_2]: (k9_subset_1(A_1, C_3, B_2)=k9_subset_1(A_1, B_2, C_3) | ~m1_subset_1(C_3, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 15.32/8.15  tff(c_3024, plain, (![A_125, B_126, B_127]: (k9_subset_1(u1_struct_0(A_125), k2_pre_topc(A_125, B_126), B_127)=k9_subset_1(u1_struct_0(A_125), B_127, k2_pre_topc(A_125, B_126)) | ~m1_subset_1(B_126, k1_zfmisc_1(u1_struct_0(A_125))) | ~l1_pre_topc(A_125))), inference(resolution, [status(thm)], [c_103, c_2])).
% 15.32/8.15  tff(c_15807, plain, (![A_265, B_266, C_267, B_268]: (k9_subset_1(u1_struct_0(A_265), k2_pre_topc(A_265, k9_subset_1(u1_struct_0(A_265), B_266, C_267)), B_268)=k9_subset_1(u1_struct_0(A_265), B_268, k2_pre_topc(A_265, k9_subset_1(u1_struct_0(A_265), B_266, C_267))) | ~l1_pre_topc(A_265) | ~m1_subset_1(C_267, k1_zfmisc_1(u1_struct_0(A_265))))), inference(resolution, [status(thm)], [c_4, c_3024])).
% 15.32/8.15  tff(c_52, plain, (![A_40, C_41, B_42]: (k9_subset_1(A_40, C_41, B_42)=k9_subset_1(A_40, B_42, C_41) | ~m1_subset_1(C_41, k1_zfmisc_1(A_40)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 15.32/8.15  tff(c_58, plain, (![B_42]: (k9_subset_1(u1_struct_0('#skF_3'), B_42, '#skF_4')=k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', B_42))), inference(resolution, [status(thm)], [c_28, c_52])).
% 15.32/8.15  tff(c_59, plain, (![B_43]: (k9_subset_1(u1_struct_0('#skF_3'), B_43, '#skF_4')=k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', B_43))), inference(resolution, [status(thm)], [c_28, c_52])).
% 15.32/8.15  tff(c_71, plain, (![B_43]: (m1_subset_1(k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', B_43), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(superposition, [status(thm), theory('equality')], [c_59, c_4])).
% 15.32/8.15  tff(c_81, plain, (![B_43]: (m1_subset_1(k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', B_43), k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_71])).
% 15.32/8.15  tff(c_3044, plain, (![B_43, B_127]: (k9_subset_1(u1_struct_0('#skF_3'), k2_pre_topc('#skF_3', k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', B_43)), B_127)=k9_subset_1(u1_struct_0('#skF_3'), B_127, k2_pre_topc('#skF_3', k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', B_43))) | ~l1_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_81, c_3024])).
% 15.32/8.15  tff(c_6026, plain, (![B_182, B_183]: (k9_subset_1(u1_struct_0('#skF_3'), k2_pre_topc('#skF_3', k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', B_182)), B_183)=k9_subset_1(u1_struct_0('#skF_3'), B_183, k2_pre_topc('#skF_3', k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', B_182))))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_3044])).
% 15.32/8.15  tff(c_6443, plain, (![B_42, B_183]: (k9_subset_1(u1_struct_0('#skF_3'), k2_pre_topc('#skF_3', k9_subset_1(u1_struct_0('#skF_3'), B_42, '#skF_4')), B_183)=k9_subset_1(u1_struct_0('#skF_3'), B_183, k2_pre_topc('#skF_3', k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', B_42))))), inference(superposition, [status(thm), theory('equality')], [c_58, c_6026])).
% 15.32/8.15  tff(c_15981, plain, (![B_268, B_266]: (k9_subset_1(u1_struct_0('#skF_3'), B_268, k2_pre_topc('#skF_3', k9_subset_1(u1_struct_0('#skF_3'), B_266, '#skF_4')))=k9_subset_1(u1_struct_0('#skF_3'), B_268, k2_pre_topc('#skF_3', k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', B_266))) | ~l1_pre_topc('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(superposition, [status(thm), theory('equality')], [c_15807, c_6443])).
% 15.32/8.15  tff(c_16901, plain, (![B_268, B_266]: (k9_subset_1(u1_struct_0('#skF_3'), B_268, k2_pre_topc('#skF_3', k9_subset_1(u1_struct_0('#skF_3'), B_266, '#skF_4')))=k9_subset_1(u1_struct_0('#skF_3'), B_268, k2_pre_topc('#skF_3', k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', B_266))))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_30, c_15981])).
% 15.32/8.15  tff(c_6, plain, (![A_7, B_8]: (m1_subset_1(k2_pre_topc(A_7, B_8), k1_zfmisc_1(u1_struct_0(A_7))) | ~m1_subset_1(B_8, k1_zfmisc_1(u1_struct_0(A_7))) | ~l1_pre_topc(A_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 15.32/8.15  tff(c_32, plain, (v3_tdlat_3('#skF_3')), inference(cnfTransformation, [status(thm)], [f_108])).
% 15.32/8.15  tff(c_107, plain, (![A_49, B_50]: (v4_pre_topc(k2_pre_topc(A_49, B_50), A_49) | ~m1_subset_1(B_50, k1_zfmisc_1(u1_struct_0(A_49))) | ~l1_pre_topc(A_49) | ~v2_pre_topc(A_49))), inference(cnfTransformation, [status(thm)], [f_47])).
% 15.32/8.15  tff(c_115, plain, (![B_43]: (v4_pre_topc(k2_pre_topc('#skF_3', k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', B_43)), '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_81, c_107])).
% 15.32/8.15  tff(c_128, plain, (![B_43]: (v4_pre_topc(k2_pre_topc('#skF_3', k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', B_43)), '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_30, c_115])).
% 15.32/8.15  tff(c_155, plain, (![B_56, A_57]: (v3_pre_topc(B_56, A_57) | ~v4_pre_topc(B_56, A_57) | ~m1_subset_1(B_56, k1_zfmisc_1(u1_struct_0(A_57))) | ~v3_tdlat_3(A_57) | ~l1_pre_topc(A_57) | ~v2_pre_topc(A_57))), inference(cnfTransformation, [status(thm)], [f_60])).
% 15.32/8.15  tff(c_2666, plain, (![A_114, B_115]: (v3_pre_topc(k2_pre_topc(A_114, B_115), A_114) | ~v4_pre_topc(k2_pre_topc(A_114, B_115), A_114) | ~v3_tdlat_3(A_114) | ~v2_pre_topc(A_114) | ~m1_subset_1(B_115, k1_zfmisc_1(u1_struct_0(A_114))) | ~l1_pre_topc(A_114))), inference(resolution, [status(thm)], [c_6, c_155])).
% 15.32/8.15  tff(c_2688, plain, (![B_43]: (v3_pre_topc(k2_pre_topc('#skF_3', k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', B_43)), '#skF_3') | ~v3_tdlat_3('#skF_3') | ~v2_pre_topc('#skF_3') | ~m1_subset_1(k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', B_43), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_128, c_2666])).
% 15.32/8.15  tff(c_2717, plain, (![B_43]: (v3_pre_topc(k2_pre_topc('#skF_3', k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', B_43)), '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_81, c_34, c_32, c_2688])).
% 15.32/8.15  tff(c_8524, plain, (![B_214, B_215]: (k9_subset_1(u1_struct_0('#skF_3'), k2_pre_topc('#skF_3', k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', B_214)), B_215)=k9_subset_1(u1_struct_0('#skF_3'), B_215, k2_pre_topc('#skF_3', k9_subset_1(u1_struct_0('#skF_3'), B_214, '#skF_4'))))), inference(superposition, [status(thm), theory('equality')], [c_58, c_6026])).
% 15.32/8.15  tff(c_34551, plain, (![B_349]: (k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', k2_pre_topc('#skF_3', k9_subset_1(u1_struct_0('#skF_3'), B_349, '#skF_4')))=k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', k2_pre_topc('#skF_3', k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', B_349))))), inference(superposition, [status(thm), theory('equality')], [c_8524, c_58])).
% 15.32/8.15  tff(c_18, plain, (![A_15, B_23, D_28]: (k9_subset_1(u1_struct_0(A_15), B_23, D_28)!=k6_domain_1(u1_struct_0(A_15), '#skF_2'(A_15, B_23)) | ~v3_pre_topc(D_28, A_15) | ~m1_subset_1(D_28, k1_zfmisc_1(u1_struct_0(A_15))) | v2_tex_2(B_23, A_15) | ~m1_subset_1(B_23, k1_zfmisc_1(u1_struct_0(A_15))) | ~l1_pre_topc(A_15) | ~v2_pre_topc(A_15) | v2_struct_0(A_15))), inference(cnfTransformation, [status(thm)], [f_86])).
% 15.32/8.15  tff(c_34809, plain, (![B_349]: (k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', k2_pre_topc('#skF_3', k9_subset_1(u1_struct_0('#skF_3'), B_349, '#skF_4')))!=k6_domain_1(u1_struct_0('#skF_3'), '#skF_2'('#skF_3', '#skF_4')) | ~v3_pre_topc(k2_pre_topc('#skF_3', k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', B_349)), '#skF_3') | ~m1_subset_1(k2_pre_topc('#skF_3', k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', B_349)), k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_tex_2('#skF_4', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_34551, c_18])).
% 15.32/8.15  tff(c_35053, plain, (![B_349]: (k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', k2_pre_topc('#skF_3', k9_subset_1(u1_struct_0('#skF_3'), B_349, '#skF_4')))!=k6_domain_1(u1_struct_0('#skF_3'), '#skF_2'('#skF_3', '#skF_4')) | ~m1_subset_1(k2_pre_topc('#skF_3', k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', B_349)), k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_tex_2('#skF_4', '#skF_3') | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_30, c_28, c_2717, c_34809])).
% 15.32/8.15  tff(c_40632, plain, (![B_371]: (k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', k2_pre_topc('#skF_3', k9_subset_1(u1_struct_0('#skF_3'), B_371, '#skF_4')))!=k6_domain_1(u1_struct_0('#skF_3'), '#skF_2'('#skF_3', '#skF_4')) | ~m1_subset_1(k2_pre_topc('#skF_3', k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', B_371)), k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_36, c_24, c_35053])).
% 15.32/8.15  tff(c_40659, plain, (![B_371]: (k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', k2_pre_topc('#skF_3', k9_subset_1(u1_struct_0('#skF_3'), B_371, '#skF_4')))!=k6_domain_1(u1_struct_0('#skF_3'), '#skF_2'('#skF_3', '#skF_4')) | ~m1_subset_1(k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', B_371), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_6, c_40632])).
% 15.32/8.15  tff(c_40676, plain, (![B_372]: (k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', k2_pre_topc('#skF_3', k9_subset_1(u1_struct_0('#skF_3'), B_372, '#skF_4')))!=k6_domain_1(u1_struct_0('#skF_3'), '#skF_2'('#skF_3', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_81, c_40659])).
% 15.32/8.15  tff(c_40809, plain, (![B_373]: (k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', k2_pre_topc('#skF_3', k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', B_373)))!=k6_domain_1(u1_struct_0('#skF_3'), '#skF_2'('#skF_3', '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_16901, c_40676])).
% 15.32/8.15  tff(c_41177, plain, (![C_377]: (k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', k2_pre_topc('#skF_3', k6_domain_1(u1_struct_0('#skF_3'), C_377)))!=k6_domain_1(u1_struct_0('#skF_3'), '#skF_2'('#skF_3', '#skF_4')) | ~r2_hidden(C_377, '#skF_4') | ~m1_subset_1(C_377, u1_struct_0('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_26, c_40809])).
% 15.32/8.15  tff(c_41180, plain, (![C_33]: (k6_domain_1(u1_struct_0('#skF_3'), C_33)!=k6_domain_1(u1_struct_0('#skF_3'), '#skF_2'('#skF_3', '#skF_4')) | ~r2_hidden(C_33, '#skF_4') | ~m1_subset_1(C_33, u1_struct_0('#skF_3')) | ~r2_hidden(C_33, '#skF_4') | ~m1_subset_1(C_33, u1_struct_0('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_26, c_41177])).
% 15.32/8.15  tff(c_42087, plain, (~r2_hidden('#skF_2'('#skF_3', '#skF_4'), '#skF_4') | ~m1_subset_1('#skF_2'('#skF_3', '#skF_4'), u1_struct_0('#skF_3')) | ~r2_hidden('#skF_2'('#skF_3', '#skF_4'), '#skF_4') | ~m1_subset_1('#skF_2'('#skF_3', '#skF_4'), u1_struct_0('#skF_3'))), inference(reflexivity, [status(thm), theory('equality')], [c_41180])).
% 15.32/8.15  tff(c_42089, plain, (~m1_subset_1('#skF_2'('#skF_3', '#skF_4'), u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_268, c_268, c_42087])).
% 15.32/8.15  tff(c_42093, plain, (v2_tex_2('#skF_4', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_22, c_42089])).
% 15.32/8.15  tff(c_42096, plain, (v2_tex_2('#skF_4', '#skF_3') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_30, c_28, c_42093])).
% 15.32/8.15  tff(c_42098, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_24, c_42096])).
% 15.32/8.15  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 15.32/8.15  
% 15.32/8.15  Inference rules
% 15.32/8.15  ----------------------
% 15.32/8.15  #Ref     : 1
% 15.32/8.15  #Sup     : 8782
% 15.32/8.15  #Fact    : 0
% 15.32/8.15  #Define  : 0
% 15.32/8.15  #Split   : 4
% 15.32/8.15  #Chain   : 0
% 15.32/8.15  #Close   : 0
% 15.32/8.15  
% 15.32/8.15  Ordering : KBO
% 15.32/8.15  
% 15.32/8.15  Simplification rules
% 15.32/8.15  ----------------------
% 15.32/8.15  #Subsume      : 2064
% 15.32/8.15  #Demod        : 9519
% 15.32/8.15  #Tautology    : 3312
% 15.32/8.15  #SimpNegUnit  : 298
% 15.32/8.16  #BackRed      : 0
% 15.32/8.16  
% 15.32/8.16  #Partial instantiations: 0
% 15.32/8.16  #Strategies tried      : 1
% 15.32/8.16  
% 15.32/8.16  Timing (in seconds)
% 15.32/8.16  ----------------------
% 15.32/8.16  Preprocessing        : 0.30
% 15.32/8.16  Parsing              : 0.17
% 15.32/8.16  CNF conversion       : 0.02
% 15.32/8.16  Main loop            : 7.07
% 15.32/8.16  Inferencing          : 1.42
% 15.32/8.16  Reduction            : 4.39
% 15.32/8.16  Demodulation         : 3.99
% 15.32/8.16  BG Simplification    : 0.15
% 15.32/8.16  Subsumption          : 0.92
% 15.32/8.16  Abstraction          : 0.31
% 15.32/8.16  MUC search           : 0.00
% 15.32/8.16  Cooper               : 0.00
% 15.32/8.16  Total                : 7.40
% 15.32/8.16  Index Insertion      : 0.00
% 15.32/8.16  Index Deletion       : 0.00
% 15.32/8.16  Index Matching       : 0.00
% 15.32/8.16  BG Taut test         : 0.00
%------------------------------------------------------------------------------
