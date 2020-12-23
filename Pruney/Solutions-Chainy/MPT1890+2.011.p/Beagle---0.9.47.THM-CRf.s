%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:25 EST 2020

% Result     : Theorem 2.75s
% Output     : CNFRefutation 2.75s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 186 expanded)
%              Number of leaves         :   32 (  81 expanded)
%              Depth                    :   17
%              Number of atoms          :  228 ( 719 expanded)
%              Number of equality atoms :   14 (  52 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_pre_topc > v2_tex_2 > r2_hidden > m1_subset_1 > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k9_subset_1 > k6_domain_1 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_3 > #skF_4 > #skF_2

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

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_129,negated_conjecture,(
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

tff(f_107,axiom,(
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

tff(f_45,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_60,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => m1_subset_1(k9_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_subset_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v4_pre_topc(k2_pre_topc(A,B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_tops_1)).

tff(f_53,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_81,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ( v3_tdlat_3(A)
      <=> ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
             => v3_pre_topc(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_tdlat_3)).

tff(c_42,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_30,plain,(
    ~ v2_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_40,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_36,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_34,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_28,plain,(
    ! [A_19,B_27] :
      ( m1_subset_1('#skF_2'(A_19,B_27),u1_struct_0(A_19))
      | v2_tex_2(B_27,A_19)
      | ~ m1_subset_1(B_27,k1_zfmisc_1(u1_struct_0(A_19)))
      | ~ l1_pre_topc(A_19)
      | ~ v2_pre_topc(A_19)
      | v2_struct_0(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_149,plain,(
    ! [A_80,B_81] :
      ( r2_hidden('#skF_2'(A_80,B_81),B_81)
      | v2_tex_2(B_81,A_80)
      | ~ m1_subset_1(B_81,k1_zfmisc_1(u1_struct_0(A_80)))
      | ~ l1_pre_topc(A_80)
      | ~ v2_pre_topc(A_80)
      | v2_struct_0(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_161,plain,
    ( r2_hidden('#skF_2'('#skF_3','#skF_4'),'#skF_4')
    | v2_tex_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_149])).

tff(c_168,plain,
    ( r2_hidden('#skF_2'('#skF_3','#skF_4'),'#skF_4')
    | v2_tex_2('#skF_4','#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_36,c_161])).

tff(c_169,plain,(
    r2_hidden('#skF_2'('#skF_3','#skF_4'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_30,c_168])).

tff(c_8,plain,(
    ! [A_9] :
      ( l1_struct_0(A_9)
      | ~ l1_pre_topc(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_12,plain,(
    ! [A_11,B_12] :
      ( m1_subset_1(k6_domain_1(A_11,B_12),k1_zfmisc_1(A_11))
      | ~ m1_subset_1(B_12,A_11)
      | v1_xboole_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_6,plain,(
    ! [A_7,B_8] :
      ( m1_subset_1(k2_pre_topc(A_7,B_8),k1_zfmisc_1(u1_struct_0(A_7)))
      | ~ m1_subset_1(B_8,k1_zfmisc_1(u1_struct_0(A_7)))
      | ~ l1_pre_topc(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_32,plain,(
    ! [C_37] :
      ( k9_subset_1(u1_struct_0('#skF_3'),'#skF_4',k2_pre_topc('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),C_37))) = k6_domain_1(u1_struct_0('#skF_3'),C_37)
      | ~ r2_hidden(C_37,'#skF_4')
      | ~ m1_subset_1(C_37,u1_struct_0('#skF_3')) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3] :
      ( m1_subset_1(k9_subset_1(A_1,B_2,C_3),k1_zfmisc_1(A_1))
      | ~ m1_subset_1(C_3,k1_zfmisc_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_92,plain,(
    ! [A_63,B_64] :
      ( v4_pre_topc(k2_pre_topc(A_63,B_64),A_63)
      | ~ m1_subset_1(B_64,k1_zfmisc_1(u1_struct_0(A_63)))
      | ~ l1_pre_topc(A_63)
      | ~ v2_pre_topc(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_143,plain,(
    ! [A_77,B_78,C_79] :
      ( v4_pre_topc(k2_pre_topc(A_77,k9_subset_1(u1_struct_0(A_77),B_78,C_79)),A_77)
      | ~ l1_pre_topc(A_77)
      | ~ v2_pre_topc(A_77)
      | ~ m1_subset_1(C_79,k1_zfmisc_1(u1_struct_0(A_77))) ) ),
    inference(resolution,[status(thm)],[c_2,c_92])).

tff(c_146,plain,(
    ! [C_37] :
      ( v4_pre_topc(k2_pre_topc('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),C_37)),'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | ~ m1_subset_1(k2_pre_topc('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),C_37)),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ r2_hidden(C_37,'#skF_4')
      | ~ m1_subset_1(C_37,u1_struct_0('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_143])).

tff(c_196,plain,(
    ! [C_90] :
      ( v4_pre_topc(k2_pre_topc('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),C_90)),'#skF_3')
      | ~ m1_subset_1(k2_pre_topc('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),C_90)),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ r2_hidden(C_90,'#skF_4')
      | ~ m1_subset_1(C_90,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_36,c_146])).

tff(c_199,plain,(
    ! [C_90] :
      ( v4_pre_topc(k2_pre_topc('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),C_90)),'#skF_3')
      | ~ r2_hidden(C_90,'#skF_4')
      | ~ m1_subset_1(C_90,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(k6_domain_1(u1_struct_0('#skF_3'),C_90),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_6,c_196])).

tff(c_203,plain,(
    ! [C_91] :
      ( v4_pre_topc(k2_pre_topc('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),C_91)),'#skF_3')
      | ~ r2_hidden(C_91,'#skF_4')
      | ~ m1_subset_1(C_91,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(k6_domain_1(u1_struct_0('#skF_3'),C_91),k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_199])).

tff(c_208,plain,(
    ! [B_12] :
      ( v4_pre_topc(k2_pre_topc('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),B_12)),'#skF_3')
      | ~ r2_hidden(B_12,'#skF_4')
      | ~ m1_subset_1(B_12,u1_struct_0('#skF_3'))
      | v1_xboole_0(u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_12,c_203])).

tff(c_209,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_208])).

tff(c_10,plain,(
    ! [A_10] :
      ( ~ v1_xboole_0(u1_struct_0(A_10))
      | ~ l1_struct_0(A_10)
      | v2_struct_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_212,plain,
    ( ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_209,c_10])).

tff(c_215,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_212])).

tff(c_218,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_8,c_215])).

tff(c_222,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_218])).

tff(c_224,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_208])).

tff(c_38,plain,(
    v3_tdlat_3('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_108,plain,(
    ! [A_63,B_12] :
      ( v4_pre_topc(k2_pre_topc(A_63,k6_domain_1(u1_struct_0(A_63),B_12)),A_63)
      | ~ l1_pre_topc(A_63)
      | ~ v2_pre_topc(A_63)
      | ~ m1_subset_1(B_12,u1_struct_0(A_63))
      | v1_xboole_0(u1_struct_0(A_63)) ) ),
    inference(resolution,[status(thm)],[c_12,c_92])).

tff(c_115,plain,(
    ! [B_70,A_71] :
      ( v3_pre_topc(B_70,A_71)
      | ~ v4_pre_topc(B_70,A_71)
      | ~ m1_subset_1(B_70,k1_zfmisc_1(u1_struct_0(A_71)))
      | ~ v3_tdlat_3(A_71)
      | ~ l1_pre_topc(A_71)
      | ~ v2_pre_topc(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_178,plain,(
    ! [A_88,B_89] :
      ( v3_pre_topc(k2_pre_topc(A_88,B_89),A_88)
      | ~ v4_pre_topc(k2_pre_topc(A_88,B_89),A_88)
      | ~ v3_tdlat_3(A_88)
      | ~ v2_pre_topc(A_88)
      | ~ m1_subset_1(B_89,k1_zfmisc_1(u1_struct_0(A_88)))
      | ~ l1_pre_topc(A_88) ) ),
    inference(resolution,[status(thm)],[c_6,c_115])).

tff(c_283,plain,(
    ! [A_116,B_117] :
      ( v3_pre_topc(k2_pre_topc(A_116,k6_domain_1(u1_struct_0(A_116),B_117)),A_116)
      | ~ v3_tdlat_3(A_116)
      | ~ m1_subset_1(k6_domain_1(u1_struct_0(A_116),B_117),k1_zfmisc_1(u1_struct_0(A_116)))
      | ~ l1_pre_topc(A_116)
      | ~ v2_pre_topc(A_116)
      | ~ m1_subset_1(B_117,u1_struct_0(A_116))
      | v1_xboole_0(u1_struct_0(A_116)) ) ),
    inference(resolution,[status(thm)],[c_108,c_178])).

tff(c_287,plain,(
    ! [A_116,B_12] :
      ( v3_pre_topc(k2_pre_topc(A_116,k6_domain_1(u1_struct_0(A_116),B_12)),A_116)
      | ~ v3_tdlat_3(A_116)
      | ~ l1_pre_topc(A_116)
      | ~ v2_pre_topc(A_116)
      | ~ m1_subset_1(B_12,u1_struct_0(A_116))
      | v1_xboole_0(u1_struct_0(A_116)) ) ),
    inference(resolution,[status(thm)],[c_12,c_283])).

tff(c_225,plain,(
    ! [A_92,B_93,D_94] :
      ( k9_subset_1(u1_struct_0(A_92),B_93,D_94) != k6_domain_1(u1_struct_0(A_92),'#skF_2'(A_92,B_93))
      | ~ v3_pre_topc(D_94,A_92)
      | ~ m1_subset_1(D_94,k1_zfmisc_1(u1_struct_0(A_92)))
      | v2_tex_2(B_93,A_92)
      | ~ m1_subset_1(B_93,k1_zfmisc_1(u1_struct_0(A_92)))
      | ~ l1_pre_topc(A_92)
      | ~ v2_pre_topc(A_92)
      | v2_struct_0(A_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_227,plain,(
    ! [C_37] :
      ( k6_domain_1(u1_struct_0('#skF_3'),C_37) != k6_domain_1(u1_struct_0('#skF_3'),'#skF_2'('#skF_3','#skF_4'))
      | ~ v3_pre_topc(k2_pre_topc('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),C_37)),'#skF_3')
      | ~ m1_subset_1(k2_pre_topc('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),C_37)),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_tex_2('#skF_4','#skF_3')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ r2_hidden(C_37,'#skF_4')
      | ~ m1_subset_1(C_37,u1_struct_0('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_225])).

tff(c_229,plain,(
    ! [C_37] :
      ( k6_domain_1(u1_struct_0('#skF_3'),C_37) != k6_domain_1(u1_struct_0('#skF_3'),'#skF_2'('#skF_3','#skF_4'))
      | ~ v3_pre_topc(k2_pre_topc('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),C_37)),'#skF_3')
      | ~ m1_subset_1(k2_pre_topc('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),C_37)),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_tex_2('#skF_4','#skF_3')
      | v2_struct_0('#skF_3')
      | ~ r2_hidden(C_37,'#skF_4')
      | ~ m1_subset_1(C_37,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_36,c_34,c_227])).

tff(c_246,plain,(
    ! [C_98] :
      ( k6_domain_1(u1_struct_0('#skF_3'),C_98) != k6_domain_1(u1_struct_0('#skF_3'),'#skF_2'('#skF_3','#skF_4'))
      | ~ v3_pre_topc(k2_pre_topc('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),C_98)),'#skF_3')
      | ~ m1_subset_1(k2_pre_topc('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),C_98)),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ r2_hidden(C_98,'#skF_4')
      | ~ m1_subset_1(C_98,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_30,c_229])).

tff(c_249,plain,(
    ! [C_98] :
      ( k6_domain_1(u1_struct_0('#skF_3'),C_98) != k6_domain_1(u1_struct_0('#skF_3'),'#skF_2'('#skF_3','#skF_4'))
      | ~ v3_pre_topc(k2_pre_topc('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),C_98)),'#skF_3')
      | ~ r2_hidden(C_98,'#skF_4')
      | ~ m1_subset_1(C_98,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(k6_domain_1(u1_struct_0('#skF_3'),C_98),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_6,c_246])).

tff(c_336,plain,(
    ! [C_134] :
      ( k6_domain_1(u1_struct_0('#skF_3'),C_134) != k6_domain_1(u1_struct_0('#skF_3'),'#skF_2'('#skF_3','#skF_4'))
      | ~ v3_pre_topc(k2_pre_topc('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),C_134)),'#skF_3')
      | ~ r2_hidden(C_134,'#skF_4')
      | ~ m1_subset_1(C_134,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(k6_domain_1(u1_struct_0('#skF_3'),C_134),k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_249])).

tff(c_340,plain,(
    ! [B_12] :
      ( k6_domain_1(u1_struct_0('#skF_3'),B_12) != k6_domain_1(u1_struct_0('#skF_3'),'#skF_2'('#skF_3','#skF_4'))
      | ~ v3_pre_topc(k2_pre_topc('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),B_12)),'#skF_3')
      | ~ r2_hidden(B_12,'#skF_4')
      | ~ m1_subset_1(B_12,u1_struct_0('#skF_3'))
      | v1_xboole_0(u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_12,c_336])).

tff(c_344,plain,(
    ! [B_135] :
      ( k6_domain_1(u1_struct_0('#skF_3'),B_135) != k6_domain_1(u1_struct_0('#skF_3'),'#skF_2'('#skF_3','#skF_4'))
      | ~ v3_pre_topc(k2_pre_topc('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),B_135)),'#skF_3')
      | ~ r2_hidden(B_135,'#skF_4')
      | ~ m1_subset_1(B_135,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_224,c_340])).

tff(c_348,plain,(
    ! [B_12] :
      ( k6_domain_1(u1_struct_0('#skF_3'),B_12) != k6_domain_1(u1_struct_0('#skF_3'),'#skF_2'('#skF_3','#skF_4'))
      | ~ r2_hidden(B_12,'#skF_4')
      | ~ v3_tdlat_3('#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | ~ m1_subset_1(B_12,u1_struct_0('#skF_3'))
      | v1_xboole_0(u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_287,c_344])).

tff(c_354,plain,(
    ! [B_12] :
      ( k6_domain_1(u1_struct_0('#skF_3'),B_12) != k6_domain_1(u1_struct_0('#skF_3'),'#skF_2'('#skF_3','#skF_4'))
      | ~ r2_hidden(B_12,'#skF_4')
      | ~ m1_subset_1(B_12,u1_struct_0('#skF_3'))
      | v1_xboole_0(u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_36,c_38,c_348])).

tff(c_355,plain,(
    ! [B_12] :
      ( k6_domain_1(u1_struct_0('#skF_3'),B_12) != k6_domain_1(u1_struct_0('#skF_3'),'#skF_2'('#skF_3','#skF_4'))
      | ~ r2_hidden(B_12,'#skF_4')
      | ~ m1_subset_1(B_12,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_224,c_354])).

tff(c_359,plain,
    ( ~ r2_hidden('#skF_2'('#skF_3','#skF_4'),'#skF_4')
    | ~ m1_subset_1('#skF_2'('#skF_3','#skF_4'),u1_struct_0('#skF_3')) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_355])).

tff(c_361,plain,(
    ~ m1_subset_1('#skF_2'('#skF_3','#skF_4'),u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_169,c_359])).

tff(c_369,plain,
    ( v2_tex_2('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_361])).

tff(c_375,plain,
    ( v2_tex_2('#skF_4','#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_36,c_34,c_369])).

tff(c_377,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_30,c_375])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:09:14 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.75/1.42  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.75/1.43  
% 2.75/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.75/1.43  %$ v4_pre_topc > v3_pre_topc > v2_tex_2 > r2_hidden > m1_subset_1 > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k9_subset_1 > k6_domain_1 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 2.75/1.43  
% 2.75/1.43  %Foreground sorts:
% 2.75/1.43  
% 2.75/1.43  
% 2.75/1.43  %Background operators:
% 2.75/1.43  
% 2.75/1.43  
% 2.75/1.43  %Foreground operators:
% 2.75/1.43  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.75/1.43  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 2.75/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.75/1.43  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.75/1.43  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.75/1.43  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.75/1.43  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.75/1.43  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 2.75/1.43  tff('#skF_3', type, '#skF_3': $i).
% 2.75/1.43  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.75/1.43  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.75/1.43  tff(v3_tdlat_3, type, v3_tdlat_3: $i > $o).
% 2.75/1.43  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 2.75/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.75/1.43  tff('#skF_4', type, '#skF_4': $i).
% 2.75/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.75/1.43  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.75/1.43  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.75/1.43  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.75/1.43  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.75/1.43  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 2.75/1.43  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 2.75/1.43  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.75/1.43  
% 2.75/1.45  tff(f_129, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_hidden(C, B) => (k9_subset_1(u1_struct_0(A), B, k2_pre_topc(A, k6_domain_1(u1_struct_0(A), C))) = k6_domain_1(u1_struct_0(A), C))))) => v2_tex_2(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t58_tex_2)).
% 2.75/1.45  tff(f_107, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((![C]: (m1_subset_1(C, u1_struct_0(A)) => ~(r2_hidden(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(v3_pre_topc(D, A) & (k9_subset_1(u1_struct_0(A), B, D) = k6_domain_1(u1_struct_0(A), C)))))))) => v2_tex_2(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_tex_2)).
% 2.75/1.45  tff(f_45, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.75/1.45  tff(f_60, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 2.75/1.45  tff(f_41, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 2.75/1.45  tff(f_29, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => m1_subset_1(k9_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k9_subset_1)).
% 2.75/1.45  tff(f_68, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v4_pre_topc(k2_pre_topc(A, B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_tops_1)).
% 2.75/1.45  tff(f_53, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 2.75/1.45  tff(f_81, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (v3_tdlat_3(A) <=> (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => v3_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_tdlat_3)).
% 2.75/1.45  tff(c_42, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_129])).
% 2.75/1.45  tff(c_30, plain, (~v2_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_129])).
% 2.75/1.45  tff(c_40, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_129])).
% 2.75/1.45  tff(c_36, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_129])).
% 2.75/1.45  tff(c_34, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_129])).
% 2.75/1.45  tff(c_28, plain, (![A_19, B_27]: (m1_subset_1('#skF_2'(A_19, B_27), u1_struct_0(A_19)) | v2_tex_2(B_27, A_19) | ~m1_subset_1(B_27, k1_zfmisc_1(u1_struct_0(A_19))) | ~l1_pre_topc(A_19) | ~v2_pre_topc(A_19) | v2_struct_0(A_19))), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.75/1.45  tff(c_149, plain, (![A_80, B_81]: (r2_hidden('#skF_2'(A_80, B_81), B_81) | v2_tex_2(B_81, A_80) | ~m1_subset_1(B_81, k1_zfmisc_1(u1_struct_0(A_80))) | ~l1_pre_topc(A_80) | ~v2_pre_topc(A_80) | v2_struct_0(A_80))), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.75/1.45  tff(c_161, plain, (r2_hidden('#skF_2'('#skF_3', '#skF_4'), '#skF_4') | v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_34, c_149])).
% 2.75/1.45  tff(c_168, plain, (r2_hidden('#skF_2'('#skF_3', '#skF_4'), '#skF_4') | v2_tex_2('#skF_4', '#skF_3') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_36, c_161])).
% 2.75/1.45  tff(c_169, plain, (r2_hidden('#skF_2'('#skF_3', '#skF_4'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_42, c_30, c_168])).
% 2.75/1.45  tff(c_8, plain, (![A_9]: (l1_struct_0(A_9) | ~l1_pre_topc(A_9))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.75/1.45  tff(c_12, plain, (![A_11, B_12]: (m1_subset_1(k6_domain_1(A_11, B_12), k1_zfmisc_1(A_11)) | ~m1_subset_1(B_12, A_11) | v1_xboole_0(A_11))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.75/1.45  tff(c_6, plain, (![A_7, B_8]: (m1_subset_1(k2_pre_topc(A_7, B_8), k1_zfmisc_1(u1_struct_0(A_7))) | ~m1_subset_1(B_8, k1_zfmisc_1(u1_struct_0(A_7))) | ~l1_pre_topc(A_7))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.75/1.45  tff(c_32, plain, (![C_37]: (k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', k2_pre_topc('#skF_3', k6_domain_1(u1_struct_0('#skF_3'), C_37)))=k6_domain_1(u1_struct_0('#skF_3'), C_37) | ~r2_hidden(C_37, '#skF_4') | ~m1_subset_1(C_37, u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_129])).
% 2.75/1.45  tff(c_2, plain, (![A_1, B_2, C_3]: (m1_subset_1(k9_subset_1(A_1, B_2, C_3), k1_zfmisc_1(A_1)) | ~m1_subset_1(C_3, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.75/1.45  tff(c_92, plain, (![A_63, B_64]: (v4_pre_topc(k2_pre_topc(A_63, B_64), A_63) | ~m1_subset_1(B_64, k1_zfmisc_1(u1_struct_0(A_63))) | ~l1_pre_topc(A_63) | ~v2_pre_topc(A_63))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.75/1.45  tff(c_143, plain, (![A_77, B_78, C_79]: (v4_pre_topc(k2_pre_topc(A_77, k9_subset_1(u1_struct_0(A_77), B_78, C_79)), A_77) | ~l1_pre_topc(A_77) | ~v2_pre_topc(A_77) | ~m1_subset_1(C_79, k1_zfmisc_1(u1_struct_0(A_77))))), inference(resolution, [status(thm)], [c_2, c_92])).
% 2.75/1.45  tff(c_146, plain, (![C_37]: (v4_pre_topc(k2_pre_topc('#skF_3', k6_domain_1(u1_struct_0('#skF_3'), C_37)), '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | ~m1_subset_1(k2_pre_topc('#skF_3', k6_domain_1(u1_struct_0('#skF_3'), C_37)), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~r2_hidden(C_37, '#skF_4') | ~m1_subset_1(C_37, u1_struct_0('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_32, c_143])).
% 2.75/1.45  tff(c_196, plain, (![C_90]: (v4_pre_topc(k2_pre_topc('#skF_3', k6_domain_1(u1_struct_0('#skF_3'), C_90)), '#skF_3') | ~m1_subset_1(k2_pre_topc('#skF_3', k6_domain_1(u1_struct_0('#skF_3'), C_90)), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~r2_hidden(C_90, '#skF_4') | ~m1_subset_1(C_90, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_36, c_146])).
% 2.75/1.45  tff(c_199, plain, (![C_90]: (v4_pre_topc(k2_pre_topc('#skF_3', k6_domain_1(u1_struct_0('#skF_3'), C_90)), '#skF_3') | ~r2_hidden(C_90, '#skF_4') | ~m1_subset_1(C_90, u1_struct_0('#skF_3')) | ~m1_subset_1(k6_domain_1(u1_struct_0('#skF_3'), C_90), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_6, c_196])).
% 2.75/1.45  tff(c_203, plain, (![C_91]: (v4_pre_topc(k2_pre_topc('#skF_3', k6_domain_1(u1_struct_0('#skF_3'), C_91)), '#skF_3') | ~r2_hidden(C_91, '#skF_4') | ~m1_subset_1(C_91, u1_struct_0('#skF_3')) | ~m1_subset_1(k6_domain_1(u1_struct_0('#skF_3'), C_91), k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_199])).
% 2.75/1.45  tff(c_208, plain, (![B_12]: (v4_pre_topc(k2_pre_topc('#skF_3', k6_domain_1(u1_struct_0('#skF_3'), B_12)), '#skF_3') | ~r2_hidden(B_12, '#skF_4') | ~m1_subset_1(B_12, u1_struct_0('#skF_3')) | v1_xboole_0(u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_12, c_203])).
% 2.75/1.45  tff(c_209, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_208])).
% 2.75/1.45  tff(c_10, plain, (![A_10]: (~v1_xboole_0(u1_struct_0(A_10)) | ~l1_struct_0(A_10) | v2_struct_0(A_10))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.75/1.45  tff(c_212, plain, (~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_209, c_10])).
% 2.75/1.45  tff(c_215, plain, (~l1_struct_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_42, c_212])).
% 2.75/1.45  tff(c_218, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_8, c_215])).
% 2.75/1.45  tff(c_222, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_218])).
% 2.75/1.45  tff(c_224, plain, (~v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_208])).
% 2.75/1.45  tff(c_38, plain, (v3_tdlat_3('#skF_3')), inference(cnfTransformation, [status(thm)], [f_129])).
% 2.75/1.45  tff(c_108, plain, (![A_63, B_12]: (v4_pre_topc(k2_pre_topc(A_63, k6_domain_1(u1_struct_0(A_63), B_12)), A_63) | ~l1_pre_topc(A_63) | ~v2_pre_topc(A_63) | ~m1_subset_1(B_12, u1_struct_0(A_63)) | v1_xboole_0(u1_struct_0(A_63)))), inference(resolution, [status(thm)], [c_12, c_92])).
% 2.75/1.45  tff(c_115, plain, (![B_70, A_71]: (v3_pre_topc(B_70, A_71) | ~v4_pre_topc(B_70, A_71) | ~m1_subset_1(B_70, k1_zfmisc_1(u1_struct_0(A_71))) | ~v3_tdlat_3(A_71) | ~l1_pre_topc(A_71) | ~v2_pre_topc(A_71))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.75/1.45  tff(c_178, plain, (![A_88, B_89]: (v3_pre_topc(k2_pre_topc(A_88, B_89), A_88) | ~v4_pre_topc(k2_pre_topc(A_88, B_89), A_88) | ~v3_tdlat_3(A_88) | ~v2_pre_topc(A_88) | ~m1_subset_1(B_89, k1_zfmisc_1(u1_struct_0(A_88))) | ~l1_pre_topc(A_88))), inference(resolution, [status(thm)], [c_6, c_115])).
% 2.75/1.45  tff(c_283, plain, (![A_116, B_117]: (v3_pre_topc(k2_pre_topc(A_116, k6_domain_1(u1_struct_0(A_116), B_117)), A_116) | ~v3_tdlat_3(A_116) | ~m1_subset_1(k6_domain_1(u1_struct_0(A_116), B_117), k1_zfmisc_1(u1_struct_0(A_116))) | ~l1_pre_topc(A_116) | ~v2_pre_topc(A_116) | ~m1_subset_1(B_117, u1_struct_0(A_116)) | v1_xboole_0(u1_struct_0(A_116)))), inference(resolution, [status(thm)], [c_108, c_178])).
% 2.75/1.45  tff(c_287, plain, (![A_116, B_12]: (v3_pre_topc(k2_pre_topc(A_116, k6_domain_1(u1_struct_0(A_116), B_12)), A_116) | ~v3_tdlat_3(A_116) | ~l1_pre_topc(A_116) | ~v2_pre_topc(A_116) | ~m1_subset_1(B_12, u1_struct_0(A_116)) | v1_xboole_0(u1_struct_0(A_116)))), inference(resolution, [status(thm)], [c_12, c_283])).
% 2.75/1.45  tff(c_225, plain, (![A_92, B_93, D_94]: (k9_subset_1(u1_struct_0(A_92), B_93, D_94)!=k6_domain_1(u1_struct_0(A_92), '#skF_2'(A_92, B_93)) | ~v3_pre_topc(D_94, A_92) | ~m1_subset_1(D_94, k1_zfmisc_1(u1_struct_0(A_92))) | v2_tex_2(B_93, A_92) | ~m1_subset_1(B_93, k1_zfmisc_1(u1_struct_0(A_92))) | ~l1_pre_topc(A_92) | ~v2_pre_topc(A_92) | v2_struct_0(A_92))), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.75/1.45  tff(c_227, plain, (![C_37]: (k6_domain_1(u1_struct_0('#skF_3'), C_37)!=k6_domain_1(u1_struct_0('#skF_3'), '#skF_2'('#skF_3', '#skF_4')) | ~v3_pre_topc(k2_pre_topc('#skF_3', k6_domain_1(u1_struct_0('#skF_3'), C_37)), '#skF_3') | ~m1_subset_1(k2_pre_topc('#skF_3', k6_domain_1(u1_struct_0('#skF_3'), C_37)), k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_tex_2('#skF_4', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~r2_hidden(C_37, '#skF_4') | ~m1_subset_1(C_37, u1_struct_0('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_32, c_225])).
% 2.75/1.45  tff(c_229, plain, (![C_37]: (k6_domain_1(u1_struct_0('#skF_3'), C_37)!=k6_domain_1(u1_struct_0('#skF_3'), '#skF_2'('#skF_3', '#skF_4')) | ~v3_pre_topc(k2_pre_topc('#skF_3', k6_domain_1(u1_struct_0('#skF_3'), C_37)), '#skF_3') | ~m1_subset_1(k2_pre_topc('#skF_3', k6_domain_1(u1_struct_0('#skF_3'), C_37)), k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_tex_2('#skF_4', '#skF_3') | v2_struct_0('#skF_3') | ~r2_hidden(C_37, '#skF_4') | ~m1_subset_1(C_37, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_36, c_34, c_227])).
% 2.75/1.45  tff(c_246, plain, (![C_98]: (k6_domain_1(u1_struct_0('#skF_3'), C_98)!=k6_domain_1(u1_struct_0('#skF_3'), '#skF_2'('#skF_3', '#skF_4')) | ~v3_pre_topc(k2_pre_topc('#skF_3', k6_domain_1(u1_struct_0('#skF_3'), C_98)), '#skF_3') | ~m1_subset_1(k2_pre_topc('#skF_3', k6_domain_1(u1_struct_0('#skF_3'), C_98)), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~r2_hidden(C_98, '#skF_4') | ~m1_subset_1(C_98, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_42, c_30, c_229])).
% 2.75/1.45  tff(c_249, plain, (![C_98]: (k6_domain_1(u1_struct_0('#skF_3'), C_98)!=k6_domain_1(u1_struct_0('#skF_3'), '#skF_2'('#skF_3', '#skF_4')) | ~v3_pre_topc(k2_pre_topc('#skF_3', k6_domain_1(u1_struct_0('#skF_3'), C_98)), '#skF_3') | ~r2_hidden(C_98, '#skF_4') | ~m1_subset_1(C_98, u1_struct_0('#skF_3')) | ~m1_subset_1(k6_domain_1(u1_struct_0('#skF_3'), C_98), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_6, c_246])).
% 2.75/1.45  tff(c_336, plain, (![C_134]: (k6_domain_1(u1_struct_0('#skF_3'), C_134)!=k6_domain_1(u1_struct_0('#skF_3'), '#skF_2'('#skF_3', '#skF_4')) | ~v3_pre_topc(k2_pre_topc('#skF_3', k6_domain_1(u1_struct_0('#skF_3'), C_134)), '#skF_3') | ~r2_hidden(C_134, '#skF_4') | ~m1_subset_1(C_134, u1_struct_0('#skF_3')) | ~m1_subset_1(k6_domain_1(u1_struct_0('#skF_3'), C_134), k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_249])).
% 2.75/1.45  tff(c_340, plain, (![B_12]: (k6_domain_1(u1_struct_0('#skF_3'), B_12)!=k6_domain_1(u1_struct_0('#skF_3'), '#skF_2'('#skF_3', '#skF_4')) | ~v3_pre_topc(k2_pre_topc('#skF_3', k6_domain_1(u1_struct_0('#skF_3'), B_12)), '#skF_3') | ~r2_hidden(B_12, '#skF_4') | ~m1_subset_1(B_12, u1_struct_0('#skF_3')) | v1_xboole_0(u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_12, c_336])).
% 2.75/1.45  tff(c_344, plain, (![B_135]: (k6_domain_1(u1_struct_0('#skF_3'), B_135)!=k6_domain_1(u1_struct_0('#skF_3'), '#skF_2'('#skF_3', '#skF_4')) | ~v3_pre_topc(k2_pre_topc('#skF_3', k6_domain_1(u1_struct_0('#skF_3'), B_135)), '#skF_3') | ~r2_hidden(B_135, '#skF_4') | ~m1_subset_1(B_135, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_224, c_340])).
% 2.75/1.45  tff(c_348, plain, (![B_12]: (k6_domain_1(u1_struct_0('#skF_3'), B_12)!=k6_domain_1(u1_struct_0('#skF_3'), '#skF_2'('#skF_3', '#skF_4')) | ~r2_hidden(B_12, '#skF_4') | ~v3_tdlat_3('#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | ~m1_subset_1(B_12, u1_struct_0('#skF_3')) | v1_xboole_0(u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_287, c_344])).
% 2.75/1.45  tff(c_354, plain, (![B_12]: (k6_domain_1(u1_struct_0('#skF_3'), B_12)!=k6_domain_1(u1_struct_0('#skF_3'), '#skF_2'('#skF_3', '#skF_4')) | ~r2_hidden(B_12, '#skF_4') | ~m1_subset_1(B_12, u1_struct_0('#skF_3')) | v1_xboole_0(u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_36, c_38, c_348])).
% 2.75/1.45  tff(c_355, plain, (![B_12]: (k6_domain_1(u1_struct_0('#skF_3'), B_12)!=k6_domain_1(u1_struct_0('#skF_3'), '#skF_2'('#skF_3', '#skF_4')) | ~r2_hidden(B_12, '#skF_4') | ~m1_subset_1(B_12, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_224, c_354])).
% 2.75/1.45  tff(c_359, plain, (~r2_hidden('#skF_2'('#skF_3', '#skF_4'), '#skF_4') | ~m1_subset_1('#skF_2'('#skF_3', '#skF_4'), u1_struct_0('#skF_3'))), inference(reflexivity, [status(thm), theory('equality')], [c_355])).
% 2.75/1.45  tff(c_361, plain, (~m1_subset_1('#skF_2'('#skF_3', '#skF_4'), u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_169, c_359])).
% 2.75/1.45  tff(c_369, plain, (v2_tex_2('#skF_4', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_28, c_361])).
% 2.75/1.45  tff(c_375, plain, (v2_tex_2('#skF_4', '#skF_3') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_36, c_34, c_369])).
% 2.75/1.45  tff(c_377, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_30, c_375])).
% 2.75/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.75/1.45  
% 2.75/1.45  Inference rules
% 2.75/1.45  ----------------------
% 2.75/1.45  #Ref     : 1
% 2.75/1.45  #Sup     : 60
% 2.75/1.45  #Fact    : 0
% 2.75/1.45  #Define  : 0
% 2.75/1.45  #Split   : 2
% 2.75/1.45  #Chain   : 0
% 2.75/1.45  #Close   : 0
% 2.75/1.45  
% 2.75/1.45  Ordering : KBO
% 2.75/1.45  
% 2.75/1.45  Simplification rules
% 2.75/1.45  ----------------------
% 2.75/1.45  #Subsume      : 11
% 2.75/1.45  #Demod        : 48
% 2.75/1.45  #Tautology    : 5
% 2.75/1.45  #SimpNegUnit  : 11
% 2.75/1.45  #BackRed      : 0
% 2.75/1.45  
% 2.75/1.45  #Partial instantiations: 0
% 2.75/1.45  #Strategies tried      : 1
% 2.75/1.45  
% 2.75/1.45  Timing (in seconds)
% 2.75/1.45  ----------------------
% 2.75/1.45  Preprocessing        : 0.32
% 2.75/1.45  Parsing              : 0.18
% 2.75/1.45  CNF conversion       : 0.02
% 2.75/1.45  Main loop            : 0.35
% 2.75/1.45  Inferencing          : 0.15
% 2.75/1.45  Reduction            : 0.09
% 2.75/1.45  Demodulation         : 0.06
% 2.75/1.45  BG Simplification    : 0.02
% 2.75/1.45  Subsumption          : 0.06
% 2.75/1.45  Abstraction          : 0.01
% 2.75/1.45  MUC search           : 0.00
% 2.75/1.45  Cooper               : 0.00
% 2.75/1.45  Total                : 0.71
% 2.75/1.45  Index Insertion      : 0.00
% 2.75/1.46  Index Deletion       : 0.00
% 2.75/1.46  Index Matching       : 0.00
% 2.75/1.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
