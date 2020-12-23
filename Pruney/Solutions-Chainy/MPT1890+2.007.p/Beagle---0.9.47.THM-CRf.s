%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:24 EST 2020

% Result     : Theorem 8.71s
% Output     : CNFRefutation 8.71s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 187 expanded)
%              Number of leaves         :   32 (  82 expanded)
%              Depth                    :   13
%              Number of atoms          :  206 ( 647 expanded)
%              Number of equality atoms :   14 (  48 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k6_domain_1 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_117,negated_conjecture,(
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

tff(f_46,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_95,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & v3_tdlat_3(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ~ ( r2_hidden(C,B)
                    & ! [D] :
                        ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                       => ~ ( v4_pre_topc(D,A)
                            & k9_subset_1(u1_struct_0(A),B,D) = k6_domain_1(u1_struct_0(A),C) ) ) ) )
           => v2_tex_2(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_tex_2)).

tff(f_42,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_59,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v4_pre_topc(k2_pre_topc(A,B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_tops_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(c_80,plain,(
    ! [A_52,B_53] :
      ( r2_hidden('#skF_2'(A_52,B_53),A_52)
      | r1_tarski(A_52,B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( ~ r2_hidden('#skF_2'(A_5,B_6),B_6)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_91,plain,(
    ! [A_52] : r1_tarski(A_52,A_52) ),
    inference(resolution,[status(thm)],[c_80,c_8])).

tff(c_34,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_64,plain,(
    ! [A_46,B_47] :
      ( r1_tarski(A_46,B_47)
      | ~ m1_subset_1(A_46,k1_zfmisc_1(B_47)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_73,plain,(
    r1_tarski('#skF_5',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_34,c_64])).

tff(c_42,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_30,plain,(
    ~ v2_tex_2('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_40,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_38,plain,(
    v3_tdlat_3('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_36,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_259,plain,(
    ! [A_95,B_96] :
      ( r2_hidden('#skF_3'(A_95,B_96),B_96)
      | v2_tex_2(B_96,A_95)
      | ~ m1_subset_1(B_96,k1_zfmisc_1(u1_struct_0(A_95)))
      | ~ l1_pre_topc(A_95)
      | ~ v3_tdlat_3(A_95)
      | ~ v2_pre_topc(A_95)
      | v2_struct_0(A_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_281,plain,
    ( r2_hidden('#skF_3'('#skF_4','#skF_5'),'#skF_5')
    | v2_tex_2('#skF_5','#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v3_tdlat_3('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_34,c_259])).

tff(c_291,plain,
    ( r2_hidden('#skF_3'('#skF_4','#skF_5'),'#skF_5')
    | v2_tex_2('#skF_5','#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_36,c_281])).

tff(c_292,plain,(
    r2_hidden('#skF_3'('#skF_4','#skF_5'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_30,c_291])).

tff(c_6,plain,(
    ! [C_9,B_6,A_5] :
      ( r2_hidden(C_9,B_6)
      | ~ r2_hidden(C_9,A_5)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_304,plain,(
    ! [B_97] :
      ( r2_hidden('#skF_3'('#skF_4','#skF_5'),B_97)
      | ~ r1_tarski('#skF_5',B_97) ) ),
    inference(resolution,[status(thm)],[c_292,c_6])).

tff(c_355,plain,(
    ! [B_103,B_104] :
      ( r2_hidden('#skF_3'('#skF_4','#skF_5'),B_103)
      | ~ r1_tarski(B_104,B_103)
      | ~ r1_tarski('#skF_5',B_104) ) ),
    inference(resolution,[status(thm)],[c_304,c_6])).

tff(c_373,plain,
    ( r2_hidden('#skF_3'('#skF_4','#skF_5'),u1_struct_0('#skF_4'))
    | ~ r1_tarski('#skF_5','#skF_5') ),
    inference(resolution,[status(thm)],[c_73,c_355])).

tff(c_384,plain,(
    r2_hidden('#skF_3'('#skF_4','#skF_5'),u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_373])).

tff(c_12,plain,(
    ! [A_10,B_11] :
      ( m1_subset_1(A_10,B_11)
      | ~ r2_hidden(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_394,plain,(
    m1_subset_1('#skF_3'('#skF_4','#skF_5'),u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_384,c_12])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_102,plain,(
    ! [C_59,B_60,A_61] :
      ( r2_hidden(C_59,B_60)
      | ~ r2_hidden(C_59,A_61)
      | ~ r1_tarski(A_61,B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_110,plain,(
    ! [A_63,B_64] :
      ( r2_hidden('#skF_1'(A_63),B_64)
      | ~ r1_tarski(A_63,B_64)
      | v1_xboole_0(A_63) ) ),
    inference(resolution,[status(thm)],[c_4,c_102])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_122,plain,(
    ! [B_65,A_66] :
      ( ~ v1_xboole_0(B_65)
      | ~ r1_tarski(A_66,B_65)
      | v1_xboole_0(A_66) ) ),
    inference(resolution,[status(thm)],[c_110,c_2])).

tff(c_138,plain,
    ( ~ v1_xboole_0(u1_struct_0('#skF_4'))
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_73,c_122])).

tff(c_139,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_138])).

tff(c_20,plain,(
    ! [A_16,B_17] :
      ( m1_subset_1(k6_domain_1(A_16,B_17),k1_zfmisc_1(A_16))
      | ~ m1_subset_1(B_17,A_16)
      | v1_xboole_0(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_219,plain,(
    ! [A_88,B_89] :
      ( v4_pre_topc(k2_pre_topc(A_88,B_89),A_88)
      | ~ m1_subset_1(B_89,k1_zfmisc_1(u1_struct_0(A_88)))
      | ~ l1_pre_topc(A_88)
      | ~ v2_pre_topc(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_241,plain,(
    ! [A_88,B_17] :
      ( v4_pre_topc(k2_pre_topc(A_88,k6_domain_1(u1_struct_0(A_88),B_17)),A_88)
      | ~ l1_pre_topc(A_88)
      | ~ v2_pre_topc(A_88)
      | ~ m1_subset_1(B_17,u1_struct_0(A_88))
      | v1_xboole_0(u1_struct_0(A_88)) ) ),
    inference(resolution,[status(thm)],[c_20,c_219])).

tff(c_18,plain,(
    ! [A_14,B_15] :
      ( m1_subset_1(k2_pre_topc(A_14,B_15),k1_zfmisc_1(u1_struct_0(A_14)))
      | ~ m1_subset_1(B_15,k1_zfmisc_1(u1_struct_0(A_14)))
      | ~ l1_pre_topc(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_32,plain,(
    ! [C_38] :
      ( k9_subset_1(u1_struct_0('#skF_4'),'#skF_5',k2_pre_topc('#skF_4',k6_domain_1(u1_struct_0('#skF_4'),C_38))) = k6_domain_1(u1_struct_0('#skF_4'),C_38)
      | ~ r2_hidden(C_38,'#skF_5')
      | ~ m1_subset_1(C_38,u1_struct_0('#skF_4')) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_424,plain,(
    ! [A_108,B_109,D_110] :
      ( k9_subset_1(u1_struct_0(A_108),B_109,D_110) != k6_domain_1(u1_struct_0(A_108),'#skF_3'(A_108,B_109))
      | ~ v4_pre_topc(D_110,A_108)
      | ~ m1_subset_1(D_110,k1_zfmisc_1(u1_struct_0(A_108)))
      | v2_tex_2(B_109,A_108)
      | ~ m1_subset_1(B_109,k1_zfmisc_1(u1_struct_0(A_108)))
      | ~ l1_pre_topc(A_108)
      | ~ v3_tdlat_3(A_108)
      | ~ v2_pre_topc(A_108)
      | v2_struct_0(A_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_426,plain,(
    ! [C_38] :
      ( k6_domain_1(u1_struct_0('#skF_4'),C_38) != k6_domain_1(u1_struct_0('#skF_4'),'#skF_3'('#skF_4','#skF_5'))
      | ~ v4_pre_topc(k2_pre_topc('#skF_4',k6_domain_1(u1_struct_0('#skF_4'),C_38)),'#skF_4')
      | ~ m1_subset_1(k2_pre_topc('#skF_4',k6_domain_1(u1_struct_0('#skF_4'),C_38)),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_tex_2('#skF_5','#skF_4')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4')
      | ~ v3_tdlat_3('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ r2_hidden(C_38,'#skF_5')
      | ~ m1_subset_1(C_38,u1_struct_0('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_424])).

tff(c_428,plain,(
    ! [C_38] :
      ( k6_domain_1(u1_struct_0('#skF_4'),C_38) != k6_domain_1(u1_struct_0('#skF_4'),'#skF_3'('#skF_4','#skF_5'))
      | ~ v4_pre_topc(k2_pre_topc('#skF_4',k6_domain_1(u1_struct_0('#skF_4'),C_38)),'#skF_4')
      | ~ m1_subset_1(k2_pre_topc('#skF_4',k6_domain_1(u1_struct_0('#skF_4'),C_38)),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_tex_2('#skF_5','#skF_4')
      | v2_struct_0('#skF_4')
      | ~ r2_hidden(C_38,'#skF_5')
      | ~ m1_subset_1(C_38,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_36,c_34,c_426])).

tff(c_483,plain,(
    ! [C_114] :
      ( k6_domain_1(u1_struct_0('#skF_4'),C_114) != k6_domain_1(u1_struct_0('#skF_4'),'#skF_3'('#skF_4','#skF_5'))
      | ~ v4_pre_topc(k2_pre_topc('#skF_4',k6_domain_1(u1_struct_0('#skF_4'),C_114)),'#skF_4')
      | ~ m1_subset_1(k2_pre_topc('#skF_4',k6_domain_1(u1_struct_0('#skF_4'),C_114)),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r2_hidden(C_114,'#skF_5')
      | ~ m1_subset_1(C_114,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_30,c_428])).

tff(c_486,plain,(
    ! [C_114] :
      ( k6_domain_1(u1_struct_0('#skF_4'),C_114) != k6_domain_1(u1_struct_0('#skF_4'),'#skF_3'('#skF_4','#skF_5'))
      | ~ v4_pre_topc(k2_pre_topc('#skF_4',k6_domain_1(u1_struct_0('#skF_4'),C_114)),'#skF_4')
      | ~ r2_hidden(C_114,'#skF_5')
      | ~ m1_subset_1(C_114,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(k6_domain_1(u1_struct_0('#skF_4'),C_114),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_18,c_483])).

tff(c_1243,plain,(
    ! [C_186] :
      ( k6_domain_1(u1_struct_0('#skF_4'),C_186) != k6_domain_1(u1_struct_0('#skF_4'),'#skF_3'('#skF_4','#skF_5'))
      | ~ v4_pre_topc(k2_pre_topc('#skF_4',k6_domain_1(u1_struct_0('#skF_4'),C_186)),'#skF_4')
      | ~ r2_hidden(C_186,'#skF_5')
      | ~ m1_subset_1(C_186,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(k6_domain_1(u1_struct_0('#skF_4'),C_186),k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_486])).

tff(c_1247,plain,(
    ! [B_17] :
      ( k6_domain_1(u1_struct_0('#skF_4'),B_17) != k6_domain_1(u1_struct_0('#skF_4'),'#skF_3'('#skF_4','#skF_5'))
      | ~ v4_pre_topc(k2_pre_topc('#skF_4',k6_domain_1(u1_struct_0('#skF_4'),B_17)),'#skF_4')
      | ~ r2_hidden(B_17,'#skF_5')
      | ~ m1_subset_1(B_17,u1_struct_0('#skF_4'))
      | v1_xboole_0(u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_20,c_1243])).

tff(c_10664,plain,(
    ! [B_570] :
      ( k6_domain_1(u1_struct_0('#skF_4'),B_570) != k6_domain_1(u1_struct_0('#skF_4'),'#skF_3'('#skF_4','#skF_5'))
      | ~ v4_pre_topc(k2_pre_topc('#skF_4',k6_domain_1(u1_struct_0('#skF_4'),B_570)),'#skF_4')
      | ~ r2_hidden(B_570,'#skF_5')
      | ~ m1_subset_1(B_570,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_139,c_1247])).

tff(c_10668,plain,(
    ! [B_17] :
      ( k6_domain_1(u1_struct_0('#skF_4'),B_17) != k6_domain_1(u1_struct_0('#skF_4'),'#skF_3'('#skF_4','#skF_5'))
      | ~ r2_hidden(B_17,'#skF_5')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | ~ m1_subset_1(B_17,u1_struct_0('#skF_4'))
      | v1_xboole_0(u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_241,c_10664])).

tff(c_10674,plain,(
    ! [B_17] :
      ( k6_domain_1(u1_struct_0('#skF_4'),B_17) != k6_domain_1(u1_struct_0('#skF_4'),'#skF_3'('#skF_4','#skF_5'))
      | ~ r2_hidden(B_17,'#skF_5')
      | ~ m1_subset_1(B_17,u1_struct_0('#skF_4'))
      | v1_xboole_0(u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_36,c_10668])).

tff(c_10675,plain,(
    ! [B_17] :
      ( k6_domain_1(u1_struct_0('#skF_4'),B_17) != k6_domain_1(u1_struct_0('#skF_4'),'#skF_3'('#skF_4','#skF_5'))
      | ~ r2_hidden(B_17,'#skF_5')
      | ~ m1_subset_1(B_17,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_139,c_10674])).

tff(c_10681,plain,
    ( ~ r2_hidden('#skF_3'('#skF_4','#skF_5'),'#skF_5')
    | ~ m1_subset_1('#skF_3'('#skF_4','#skF_5'),u1_struct_0('#skF_4')) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_10675])).

tff(c_10684,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_394,c_292,c_10681])).

tff(c_10685,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_138])).

tff(c_10861,plain,(
    ! [A_602,B_603] :
      ( r2_hidden('#skF_3'(A_602,B_603),B_603)
      | v2_tex_2(B_603,A_602)
      | ~ m1_subset_1(B_603,k1_zfmisc_1(u1_struct_0(A_602)))
      | ~ l1_pre_topc(A_602)
      | ~ v3_tdlat_3(A_602)
      | ~ v2_pre_topc(A_602)
      | v2_struct_0(A_602) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_10883,plain,
    ( r2_hidden('#skF_3'('#skF_4','#skF_5'),'#skF_5')
    | v2_tex_2('#skF_5','#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v3_tdlat_3('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_34,c_10861])).

tff(c_10893,plain,
    ( r2_hidden('#skF_3'('#skF_4','#skF_5'),'#skF_5')
    | v2_tex_2('#skF_5','#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_36,c_10883])).

tff(c_10894,plain,(
    r2_hidden('#skF_3'('#skF_4','#skF_5'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_30,c_10893])).

tff(c_10902,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_10894,c_2])).

tff(c_10910,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10685,c_10902])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:55:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.71/3.49  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.71/3.50  
% 8.71/3.50  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.71/3.50  %$ v4_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k6_domain_1 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2
% 8.71/3.50  
% 8.71/3.50  %Foreground sorts:
% 8.71/3.50  
% 8.71/3.50  
% 8.71/3.50  %Background operators:
% 8.71/3.50  
% 8.71/3.50  
% 8.71/3.50  %Foreground operators:
% 8.71/3.50  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 8.71/3.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.71/3.50  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.71/3.50  tff('#skF_1', type, '#skF_1': $i > $i).
% 8.71/3.50  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 8.71/3.50  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 8.71/3.50  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 8.71/3.50  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.71/3.50  tff('#skF_5', type, '#skF_5': $i).
% 8.71/3.50  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 8.71/3.50  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.71/3.50  tff(v3_tdlat_3, type, v3_tdlat_3: $i > $o).
% 8.71/3.50  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 8.71/3.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.71/3.50  tff('#skF_4', type, '#skF_4': $i).
% 8.71/3.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.71/3.50  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 8.71/3.50  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 8.71/3.50  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 8.71/3.50  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 8.71/3.50  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 8.71/3.50  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 8.71/3.50  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.71/3.50  
% 8.71/3.52  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 8.71/3.52  tff(f_117, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_hidden(C, B) => (k9_subset_1(u1_struct_0(A), B, k2_pre_topc(A, k6_domain_1(u1_struct_0(A), C))) = k6_domain_1(u1_struct_0(A), C))))) => v2_tex_2(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t58_tex_2)).
% 8.71/3.52  tff(f_46, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 8.71/3.52  tff(f_95, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((![C]: (m1_subset_1(C, u1_struct_0(A)) => ~(r2_hidden(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(v4_pre_topc(D, A) & (k9_subset_1(u1_struct_0(A), B, D) = k6_domain_1(u1_struct_0(A), C)))))))) => v2_tex_2(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t57_tex_2)).
% 8.71/3.52  tff(f_42, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 8.71/3.52  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 8.71/3.52  tff(f_59, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 8.71/3.52  tff(f_67, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v4_pre_topc(k2_pre_topc(A, B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_tops_1)).
% 8.71/3.52  tff(f_52, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 8.71/3.52  tff(c_80, plain, (![A_52, B_53]: (r2_hidden('#skF_2'(A_52, B_53), A_52) | r1_tarski(A_52, B_53))), inference(cnfTransformation, [status(thm)], [f_38])).
% 8.71/3.52  tff(c_8, plain, (![A_5, B_6]: (~r2_hidden('#skF_2'(A_5, B_6), B_6) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 8.71/3.52  tff(c_91, plain, (![A_52]: (r1_tarski(A_52, A_52))), inference(resolution, [status(thm)], [c_80, c_8])).
% 8.71/3.52  tff(c_34, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_117])).
% 8.71/3.52  tff(c_64, plain, (![A_46, B_47]: (r1_tarski(A_46, B_47) | ~m1_subset_1(A_46, k1_zfmisc_1(B_47)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 8.71/3.52  tff(c_73, plain, (r1_tarski('#skF_5', u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_34, c_64])).
% 8.71/3.52  tff(c_42, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_117])).
% 8.71/3.52  tff(c_30, plain, (~v2_tex_2('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_117])).
% 8.71/3.52  tff(c_40, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_117])).
% 8.71/3.52  tff(c_38, plain, (v3_tdlat_3('#skF_4')), inference(cnfTransformation, [status(thm)], [f_117])).
% 8.71/3.52  tff(c_36, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_117])).
% 8.71/3.52  tff(c_259, plain, (![A_95, B_96]: (r2_hidden('#skF_3'(A_95, B_96), B_96) | v2_tex_2(B_96, A_95) | ~m1_subset_1(B_96, k1_zfmisc_1(u1_struct_0(A_95))) | ~l1_pre_topc(A_95) | ~v3_tdlat_3(A_95) | ~v2_pre_topc(A_95) | v2_struct_0(A_95))), inference(cnfTransformation, [status(thm)], [f_95])).
% 8.71/3.52  tff(c_281, plain, (r2_hidden('#skF_3'('#skF_4', '#skF_5'), '#skF_5') | v2_tex_2('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_4') | ~v3_tdlat_3('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_34, c_259])).
% 8.71/3.52  tff(c_291, plain, (r2_hidden('#skF_3'('#skF_4', '#skF_5'), '#skF_5') | v2_tex_2('#skF_5', '#skF_4') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_36, c_281])).
% 8.71/3.52  tff(c_292, plain, (r2_hidden('#skF_3'('#skF_4', '#skF_5'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_42, c_30, c_291])).
% 8.71/3.52  tff(c_6, plain, (![C_9, B_6, A_5]: (r2_hidden(C_9, B_6) | ~r2_hidden(C_9, A_5) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 8.71/3.52  tff(c_304, plain, (![B_97]: (r2_hidden('#skF_3'('#skF_4', '#skF_5'), B_97) | ~r1_tarski('#skF_5', B_97))), inference(resolution, [status(thm)], [c_292, c_6])).
% 8.71/3.52  tff(c_355, plain, (![B_103, B_104]: (r2_hidden('#skF_3'('#skF_4', '#skF_5'), B_103) | ~r1_tarski(B_104, B_103) | ~r1_tarski('#skF_5', B_104))), inference(resolution, [status(thm)], [c_304, c_6])).
% 8.71/3.52  tff(c_373, plain, (r2_hidden('#skF_3'('#skF_4', '#skF_5'), u1_struct_0('#skF_4')) | ~r1_tarski('#skF_5', '#skF_5')), inference(resolution, [status(thm)], [c_73, c_355])).
% 8.71/3.52  tff(c_384, plain, (r2_hidden('#skF_3'('#skF_4', '#skF_5'), u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_91, c_373])).
% 8.71/3.52  tff(c_12, plain, (![A_10, B_11]: (m1_subset_1(A_10, B_11) | ~r2_hidden(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_42])).
% 8.71/3.52  tff(c_394, plain, (m1_subset_1('#skF_3'('#skF_4', '#skF_5'), u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_384, c_12])).
% 8.71/3.52  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.71/3.52  tff(c_102, plain, (![C_59, B_60, A_61]: (r2_hidden(C_59, B_60) | ~r2_hidden(C_59, A_61) | ~r1_tarski(A_61, B_60))), inference(cnfTransformation, [status(thm)], [f_38])).
% 8.71/3.52  tff(c_110, plain, (![A_63, B_64]: (r2_hidden('#skF_1'(A_63), B_64) | ~r1_tarski(A_63, B_64) | v1_xboole_0(A_63))), inference(resolution, [status(thm)], [c_4, c_102])).
% 8.71/3.52  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.71/3.52  tff(c_122, plain, (![B_65, A_66]: (~v1_xboole_0(B_65) | ~r1_tarski(A_66, B_65) | v1_xboole_0(A_66))), inference(resolution, [status(thm)], [c_110, c_2])).
% 8.71/3.52  tff(c_138, plain, (~v1_xboole_0(u1_struct_0('#skF_4')) | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_73, c_122])).
% 8.71/3.52  tff(c_139, plain, (~v1_xboole_0(u1_struct_0('#skF_4'))), inference(splitLeft, [status(thm)], [c_138])).
% 8.71/3.52  tff(c_20, plain, (![A_16, B_17]: (m1_subset_1(k6_domain_1(A_16, B_17), k1_zfmisc_1(A_16)) | ~m1_subset_1(B_17, A_16) | v1_xboole_0(A_16))), inference(cnfTransformation, [status(thm)], [f_59])).
% 8.71/3.52  tff(c_219, plain, (![A_88, B_89]: (v4_pre_topc(k2_pre_topc(A_88, B_89), A_88) | ~m1_subset_1(B_89, k1_zfmisc_1(u1_struct_0(A_88))) | ~l1_pre_topc(A_88) | ~v2_pre_topc(A_88))), inference(cnfTransformation, [status(thm)], [f_67])).
% 8.71/3.52  tff(c_241, plain, (![A_88, B_17]: (v4_pre_topc(k2_pre_topc(A_88, k6_domain_1(u1_struct_0(A_88), B_17)), A_88) | ~l1_pre_topc(A_88) | ~v2_pre_topc(A_88) | ~m1_subset_1(B_17, u1_struct_0(A_88)) | v1_xboole_0(u1_struct_0(A_88)))), inference(resolution, [status(thm)], [c_20, c_219])).
% 8.71/3.52  tff(c_18, plain, (![A_14, B_15]: (m1_subset_1(k2_pre_topc(A_14, B_15), k1_zfmisc_1(u1_struct_0(A_14))) | ~m1_subset_1(B_15, k1_zfmisc_1(u1_struct_0(A_14))) | ~l1_pre_topc(A_14))), inference(cnfTransformation, [status(thm)], [f_52])).
% 8.71/3.52  tff(c_32, plain, (![C_38]: (k9_subset_1(u1_struct_0('#skF_4'), '#skF_5', k2_pre_topc('#skF_4', k6_domain_1(u1_struct_0('#skF_4'), C_38)))=k6_domain_1(u1_struct_0('#skF_4'), C_38) | ~r2_hidden(C_38, '#skF_5') | ~m1_subset_1(C_38, u1_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_117])).
% 8.71/3.52  tff(c_424, plain, (![A_108, B_109, D_110]: (k9_subset_1(u1_struct_0(A_108), B_109, D_110)!=k6_domain_1(u1_struct_0(A_108), '#skF_3'(A_108, B_109)) | ~v4_pre_topc(D_110, A_108) | ~m1_subset_1(D_110, k1_zfmisc_1(u1_struct_0(A_108))) | v2_tex_2(B_109, A_108) | ~m1_subset_1(B_109, k1_zfmisc_1(u1_struct_0(A_108))) | ~l1_pre_topc(A_108) | ~v3_tdlat_3(A_108) | ~v2_pre_topc(A_108) | v2_struct_0(A_108))), inference(cnfTransformation, [status(thm)], [f_95])).
% 8.71/3.52  tff(c_426, plain, (![C_38]: (k6_domain_1(u1_struct_0('#skF_4'), C_38)!=k6_domain_1(u1_struct_0('#skF_4'), '#skF_3'('#skF_4', '#skF_5')) | ~v4_pre_topc(k2_pre_topc('#skF_4', k6_domain_1(u1_struct_0('#skF_4'), C_38)), '#skF_4') | ~m1_subset_1(k2_pre_topc('#skF_4', k6_domain_1(u1_struct_0('#skF_4'), C_38)), k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_tex_2('#skF_5', '#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4') | ~v3_tdlat_3('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~r2_hidden(C_38, '#skF_5') | ~m1_subset_1(C_38, u1_struct_0('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_32, c_424])).
% 8.71/3.52  tff(c_428, plain, (![C_38]: (k6_domain_1(u1_struct_0('#skF_4'), C_38)!=k6_domain_1(u1_struct_0('#skF_4'), '#skF_3'('#skF_4', '#skF_5')) | ~v4_pre_topc(k2_pre_topc('#skF_4', k6_domain_1(u1_struct_0('#skF_4'), C_38)), '#skF_4') | ~m1_subset_1(k2_pre_topc('#skF_4', k6_domain_1(u1_struct_0('#skF_4'), C_38)), k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_tex_2('#skF_5', '#skF_4') | v2_struct_0('#skF_4') | ~r2_hidden(C_38, '#skF_5') | ~m1_subset_1(C_38, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_36, c_34, c_426])).
% 8.71/3.52  tff(c_483, plain, (![C_114]: (k6_domain_1(u1_struct_0('#skF_4'), C_114)!=k6_domain_1(u1_struct_0('#skF_4'), '#skF_3'('#skF_4', '#skF_5')) | ~v4_pre_topc(k2_pre_topc('#skF_4', k6_domain_1(u1_struct_0('#skF_4'), C_114)), '#skF_4') | ~m1_subset_1(k2_pre_topc('#skF_4', k6_domain_1(u1_struct_0('#skF_4'), C_114)), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r2_hidden(C_114, '#skF_5') | ~m1_subset_1(C_114, u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_42, c_30, c_428])).
% 8.71/3.52  tff(c_486, plain, (![C_114]: (k6_domain_1(u1_struct_0('#skF_4'), C_114)!=k6_domain_1(u1_struct_0('#skF_4'), '#skF_3'('#skF_4', '#skF_5')) | ~v4_pre_topc(k2_pre_topc('#skF_4', k6_domain_1(u1_struct_0('#skF_4'), C_114)), '#skF_4') | ~r2_hidden(C_114, '#skF_5') | ~m1_subset_1(C_114, u1_struct_0('#skF_4')) | ~m1_subset_1(k6_domain_1(u1_struct_0('#skF_4'), C_114), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4'))), inference(resolution, [status(thm)], [c_18, c_483])).
% 8.71/3.52  tff(c_1243, plain, (![C_186]: (k6_domain_1(u1_struct_0('#skF_4'), C_186)!=k6_domain_1(u1_struct_0('#skF_4'), '#skF_3'('#skF_4', '#skF_5')) | ~v4_pre_topc(k2_pre_topc('#skF_4', k6_domain_1(u1_struct_0('#skF_4'), C_186)), '#skF_4') | ~r2_hidden(C_186, '#skF_5') | ~m1_subset_1(C_186, u1_struct_0('#skF_4')) | ~m1_subset_1(k6_domain_1(u1_struct_0('#skF_4'), C_186), k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_486])).
% 8.71/3.52  tff(c_1247, plain, (![B_17]: (k6_domain_1(u1_struct_0('#skF_4'), B_17)!=k6_domain_1(u1_struct_0('#skF_4'), '#skF_3'('#skF_4', '#skF_5')) | ~v4_pre_topc(k2_pre_topc('#skF_4', k6_domain_1(u1_struct_0('#skF_4'), B_17)), '#skF_4') | ~r2_hidden(B_17, '#skF_5') | ~m1_subset_1(B_17, u1_struct_0('#skF_4')) | v1_xboole_0(u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_20, c_1243])).
% 8.71/3.52  tff(c_10664, plain, (![B_570]: (k6_domain_1(u1_struct_0('#skF_4'), B_570)!=k6_domain_1(u1_struct_0('#skF_4'), '#skF_3'('#skF_4', '#skF_5')) | ~v4_pre_topc(k2_pre_topc('#skF_4', k6_domain_1(u1_struct_0('#skF_4'), B_570)), '#skF_4') | ~r2_hidden(B_570, '#skF_5') | ~m1_subset_1(B_570, u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_139, c_1247])).
% 8.71/3.52  tff(c_10668, plain, (![B_17]: (k6_domain_1(u1_struct_0('#skF_4'), B_17)!=k6_domain_1(u1_struct_0('#skF_4'), '#skF_3'('#skF_4', '#skF_5')) | ~r2_hidden(B_17, '#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | ~m1_subset_1(B_17, u1_struct_0('#skF_4')) | v1_xboole_0(u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_241, c_10664])).
% 8.71/3.52  tff(c_10674, plain, (![B_17]: (k6_domain_1(u1_struct_0('#skF_4'), B_17)!=k6_domain_1(u1_struct_0('#skF_4'), '#skF_3'('#skF_4', '#skF_5')) | ~r2_hidden(B_17, '#skF_5') | ~m1_subset_1(B_17, u1_struct_0('#skF_4')) | v1_xboole_0(u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_36, c_10668])).
% 8.71/3.52  tff(c_10675, plain, (![B_17]: (k6_domain_1(u1_struct_0('#skF_4'), B_17)!=k6_domain_1(u1_struct_0('#skF_4'), '#skF_3'('#skF_4', '#skF_5')) | ~r2_hidden(B_17, '#skF_5') | ~m1_subset_1(B_17, u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_139, c_10674])).
% 8.71/3.52  tff(c_10681, plain, (~r2_hidden('#skF_3'('#skF_4', '#skF_5'), '#skF_5') | ~m1_subset_1('#skF_3'('#skF_4', '#skF_5'), u1_struct_0('#skF_4'))), inference(reflexivity, [status(thm), theory('equality')], [c_10675])).
% 8.71/3.52  tff(c_10684, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_394, c_292, c_10681])).
% 8.71/3.52  tff(c_10685, plain, (v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_138])).
% 8.71/3.52  tff(c_10861, plain, (![A_602, B_603]: (r2_hidden('#skF_3'(A_602, B_603), B_603) | v2_tex_2(B_603, A_602) | ~m1_subset_1(B_603, k1_zfmisc_1(u1_struct_0(A_602))) | ~l1_pre_topc(A_602) | ~v3_tdlat_3(A_602) | ~v2_pre_topc(A_602) | v2_struct_0(A_602))), inference(cnfTransformation, [status(thm)], [f_95])).
% 8.71/3.52  tff(c_10883, plain, (r2_hidden('#skF_3'('#skF_4', '#skF_5'), '#skF_5') | v2_tex_2('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_4') | ~v3_tdlat_3('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_34, c_10861])).
% 8.71/3.52  tff(c_10893, plain, (r2_hidden('#skF_3'('#skF_4', '#skF_5'), '#skF_5') | v2_tex_2('#skF_5', '#skF_4') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_36, c_10883])).
% 8.71/3.52  tff(c_10894, plain, (r2_hidden('#skF_3'('#skF_4', '#skF_5'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_42, c_30, c_10893])).
% 8.71/3.52  tff(c_10902, plain, (~v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_10894, c_2])).
% 8.71/3.52  tff(c_10910, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10685, c_10902])).
% 8.71/3.52  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.71/3.52  
% 8.71/3.52  Inference rules
% 8.71/3.52  ----------------------
% 8.71/3.52  #Ref     : 1
% 8.71/3.52  #Sup     : 2614
% 8.71/3.52  #Fact    : 0
% 8.71/3.52  #Define  : 0
% 8.71/3.52  #Split   : 17
% 8.71/3.52  #Chain   : 0
% 8.71/3.52  #Close   : 0
% 8.71/3.52  
% 8.71/3.52  Ordering : KBO
% 8.71/3.52  
% 8.71/3.52  Simplification rules
% 8.71/3.52  ----------------------
% 8.71/3.52  #Subsume      : 845
% 8.71/3.52  #Demod        : 205
% 8.71/3.52  #Tautology    : 137
% 8.71/3.52  #SimpNegUnit  : 21
% 8.71/3.52  #BackRed      : 0
% 8.71/3.52  
% 8.71/3.52  #Partial instantiations: 0
% 8.71/3.52  #Strategies tried      : 1
% 8.71/3.52  
% 8.71/3.52  Timing (in seconds)
% 8.71/3.52  ----------------------
% 8.71/3.52  Preprocessing        : 0.30
% 8.71/3.52  Parsing              : 0.17
% 8.71/3.52  CNF conversion       : 0.02
% 8.71/3.52  Main loop            : 2.41
% 8.71/3.52  Inferencing          : 0.60
% 8.71/3.52  Reduction            : 0.55
% 8.71/3.52  Demodulation         : 0.35
% 8.71/3.52  BG Simplification    : 0.06
% 8.71/3.52  Subsumption          : 1.03
% 8.71/3.52  Abstraction          : 0.08
% 8.71/3.52  MUC search           : 0.00
% 8.71/3.52  Cooper               : 0.00
% 8.71/3.52  Total                : 2.75
% 8.71/3.52  Index Insertion      : 0.00
% 8.71/3.52  Index Deletion       : 0.00
% 8.71/3.52  Index Matching       : 0.00
% 8.71/3.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
