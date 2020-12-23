%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:23 EST 2020

% Result     : Theorem 27.78s
% Output     : CNFRefutation 27.92s
% Verified   : 
% Statistics : Number of formulae       :  191 (2121 expanded)
%              Number of leaves         :   40 ( 726 expanded)
%              Depth                    :   23
%              Number of atoms          :  459 (6851 expanded)
%              Number of equality atoms :   57 ( 847 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k6_domain_1 > k3_xboole_0 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_3 > #skF_5 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

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

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_149,negated_conjecture,(
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

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_54,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_127,axiom,(
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

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_50,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(k1_tarski(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).

tff(f_88,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v4_pre_topc(k2_pre_topc(A,B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_tops_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_80,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k9_subset_1(A,C,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k9_subset_1)).

tff(f_101,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ( v3_tdlat_3(A)
      <=> ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
             => v3_pre_topc(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_tdlat_3)).

tff(c_48,plain,(
    ~ v2_tex_2('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_12,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_52,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_63,plain,(
    ! [A_54,B_55] :
      ( r1_tarski(A_54,B_55)
      | ~ m1_subset_1(A_54,k1_zfmisc_1(B_55)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_67,plain,(
    r1_tarski('#skF_5',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_52,c_63])).

tff(c_60,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_58,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_54,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_1100,plain,(
    ! [A_195,B_196] :
      ( r2_hidden('#skF_3'(A_195,B_196),B_196)
      | v2_tex_2(B_196,A_195)
      | ~ m1_subset_1(B_196,k1_zfmisc_1(u1_struct_0(A_195)))
      | ~ l1_pre_topc(A_195)
      | ~ v2_pre_topc(A_195)
      | v2_struct_0(A_195) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_1118,plain,
    ( r2_hidden('#skF_3'('#skF_4','#skF_5'),'#skF_5')
    | v2_tex_2('#skF_5','#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_1100])).

tff(c_1127,plain,
    ( r2_hidden('#skF_3'('#skF_4','#skF_5'),'#skF_5')
    | v2_tex_2('#skF_5','#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_54,c_1118])).

tff(c_1128,plain,(
    r2_hidden('#skF_3'('#skF_4','#skF_5'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_48,c_1127])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1163,plain,(
    ! [B_198] :
      ( r2_hidden('#skF_3'('#skF_4','#skF_5'),B_198)
      | ~ r1_tarski('#skF_5',B_198) ) ),
    inference(resolution,[status(thm)],[c_1128,c_2])).

tff(c_1321,plain,(
    ! [B_208,B_209] :
      ( r2_hidden('#skF_3'('#skF_4','#skF_5'),B_208)
      | ~ r1_tarski(B_209,B_208)
      | ~ r1_tarski('#skF_5',B_209) ) ),
    inference(resolution,[status(thm)],[c_1163,c_2])).

tff(c_1335,plain,
    ( r2_hidden('#skF_3'('#skF_4','#skF_5'),u1_struct_0('#skF_4'))
    | ~ r1_tarski('#skF_5','#skF_5') ),
    inference(resolution,[status(thm)],[c_67,c_1321])).

tff(c_1346,plain,(
    r2_hidden('#skF_3'('#skF_4','#skF_5'),u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_1335])).

tff(c_18,plain,(
    ! [A_14,B_15] :
      ( m1_subset_1(k1_tarski(A_14),k1_zfmisc_1(B_15))
      | ~ r2_hidden(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_573,plain,(
    ! [A_153,B_154] :
      ( v4_pre_topc(k2_pre_topc(A_153,B_154),A_153)
      | ~ m1_subset_1(B_154,k1_zfmisc_1(u1_struct_0(A_153)))
      | ~ l1_pre_topc(A_153)
      | ~ v2_pre_topc(A_153) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_589,plain,(
    ! [A_153,A_14] :
      ( v4_pre_topc(k2_pre_topc(A_153,k1_tarski(A_14)),A_153)
      | ~ l1_pre_topc(A_153)
      | ~ v2_pre_topc(A_153)
      | ~ r2_hidden(A_14,u1_struct_0(A_153)) ) ),
    inference(resolution,[status(thm)],[c_18,c_573])).

tff(c_28,plain,(
    ! [A_24,B_25] :
      ( m1_subset_1(k2_pre_topc(A_24,B_25),k1_zfmisc_1(u1_struct_0(A_24)))
      | ~ m1_subset_1(B_25,k1_zfmisc_1(u1_struct_0(A_24)))
      | ~ l1_pre_topc(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_114,plain,(
    ! [C_72,B_73,A_74] :
      ( ~ v1_xboole_0(C_72)
      | ~ m1_subset_1(B_73,k1_zfmisc_1(C_72))
      | ~ r2_hidden(A_74,B_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_123,plain,(
    ! [A_74] :
      ( ~ v1_xboole_0(u1_struct_0('#skF_4'))
      | ~ r2_hidden(A_74,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_52,c_114])).

tff(c_124,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_123])).

tff(c_22,plain,(
    ! [A_16,B_17] :
      ( m1_subset_1(A_16,k1_zfmisc_1(B_17))
      | ~ r1_tarski(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_150,plain,(
    ! [A_83,C_84,B_85] :
      ( m1_subset_1(A_83,C_84)
      | ~ m1_subset_1(B_85,k1_zfmisc_1(C_84))
      | ~ r2_hidden(A_83,B_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_158,plain,(
    ! [A_83,B_17,A_16] :
      ( m1_subset_1(A_83,B_17)
      | ~ r2_hidden(A_83,A_16)
      | ~ r1_tarski(A_16,B_17) ) ),
    inference(resolution,[status(thm)],[c_22,c_150])).

tff(c_1385,plain,(
    ! [B_211] :
      ( m1_subset_1('#skF_3'('#skF_4','#skF_5'),B_211)
      | ~ r1_tarski(u1_struct_0('#skF_4'),B_211) ) ),
    inference(resolution,[status(thm)],[c_1346,c_158])).

tff(c_1395,plain,(
    m1_subset_1('#skF_3'('#skF_4','#skF_5'),u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_12,c_1385])).

tff(c_30,plain,(
    ! [A_26,B_27] :
      ( k6_domain_1(A_26,B_27) = k1_tarski(B_27)
      | ~ m1_subset_1(B_27,A_26)
      | v1_xboole_0(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_1431,plain,
    ( k6_domain_1(u1_struct_0('#skF_4'),'#skF_3'('#skF_4','#skF_5')) = k1_tarski('#skF_3'('#skF_4','#skF_5'))
    | v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_1395,c_30])).

tff(c_1434,plain,(
    k6_domain_1(u1_struct_0('#skF_4'),'#skF_3'('#skF_4','#skF_5')) = k1_tarski('#skF_3'('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_124,c_1431])).

tff(c_262,plain,(
    ! [A_113,B_114,C_115] :
      ( k9_subset_1(A_113,B_114,C_115) = k3_xboole_0(B_114,C_115)
      | ~ m1_subset_1(C_115,k1_zfmisc_1(A_113)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_271,plain,(
    ! [B_114] : k9_subset_1(u1_struct_0('#skF_4'),B_114,'#skF_5') = k3_xboole_0(B_114,'#skF_5') ),
    inference(resolution,[status(thm)],[c_52,c_262])).

tff(c_436,plain,(
    ! [A_140,C_141,B_142] :
      ( k9_subset_1(A_140,C_141,B_142) = k9_subset_1(A_140,B_142,C_141)
      | ~ m1_subset_1(C_141,k1_zfmisc_1(A_140)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_447,plain,(
    ! [B_142] : k9_subset_1(u1_struct_0('#skF_4'),B_142,'#skF_5') = k9_subset_1(u1_struct_0('#skF_4'),'#skF_5',B_142) ),
    inference(resolution,[status(thm)],[c_52,c_436])).

tff(c_453,plain,(
    ! [B_142] : k9_subset_1(u1_struct_0('#skF_4'),'#skF_5',B_142) = k3_xboole_0(B_142,'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_271,c_447])).

tff(c_50,plain,(
    ! [C_52] :
      ( k9_subset_1(u1_struct_0('#skF_4'),'#skF_5',k2_pre_topc('#skF_4',k6_domain_1(u1_struct_0('#skF_4'),C_52))) = k6_domain_1(u1_struct_0('#skF_4'),C_52)
      | ~ r2_hidden(C_52,'#skF_5')
      | ~ m1_subset_1(C_52,u1_struct_0('#skF_4')) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_455,plain,(
    ! [C_52] :
      ( k3_xboole_0(k2_pre_topc('#skF_4',k6_domain_1(u1_struct_0('#skF_4'),C_52)),'#skF_5') = k6_domain_1(u1_struct_0('#skF_4'),C_52)
      | ~ r2_hidden(C_52,'#skF_5')
      | ~ m1_subset_1(C_52,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_453,c_50])).

tff(c_1576,plain,
    ( k3_xboole_0(k2_pre_topc('#skF_4',k1_tarski('#skF_3'('#skF_4','#skF_5'))),'#skF_5') = k6_domain_1(u1_struct_0('#skF_4'),'#skF_3'('#skF_4','#skF_5'))
    | ~ r2_hidden('#skF_3'('#skF_4','#skF_5'),'#skF_5')
    | ~ m1_subset_1('#skF_3'('#skF_4','#skF_5'),u1_struct_0('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1434,c_455])).

tff(c_1589,plain,(
    k3_xboole_0(k2_pre_topc('#skF_4',k1_tarski('#skF_3'('#skF_4','#skF_5'))),'#skF_5') = k1_tarski('#skF_3'('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1395,c_1128,c_1434,c_1576])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_110,plain,(
    ! [C_69,B_70,A_71] :
      ( r2_hidden(C_69,B_70)
      | ~ r2_hidden(C_69,A_71)
      | ~ r1_tarski(A_71,B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_335,plain,(
    ! [A_127,B_128,B_129] :
      ( r2_hidden('#skF_1'(A_127,B_128),B_129)
      | ~ r1_tarski(A_127,B_129)
      | r1_tarski(A_127,B_128) ) ),
    inference(resolution,[status(thm)],[c_6,c_110])).

tff(c_2251,plain,(
    ! [A_274,B_275,B_276,B_277] :
      ( r2_hidden('#skF_1'(A_274,B_275),B_276)
      | ~ r1_tarski(B_277,B_276)
      | ~ r1_tarski(A_274,B_277)
      | r1_tarski(A_274,B_275) ) ),
    inference(resolution,[status(thm)],[c_335,c_2])).

tff(c_2285,plain,(
    ! [A_278,B_279] :
      ( r2_hidden('#skF_1'(A_278,B_279),u1_struct_0('#skF_4'))
      | ~ r1_tarski(A_278,'#skF_5')
      | r1_tarski(A_278,B_279) ) ),
    inference(resolution,[status(thm)],[c_67,c_2251])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_2394,plain,(
    ! [A_281] :
      ( ~ r1_tarski(A_281,'#skF_5')
      | r1_tarski(A_281,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_2285,c_4])).

tff(c_270,plain,(
    ! [B_17,B_114,A_16] :
      ( k9_subset_1(B_17,B_114,A_16) = k3_xboole_0(B_114,A_16)
      | ~ r1_tarski(A_16,B_17) ) ),
    inference(resolution,[status(thm)],[c_22,c_262])).

tff(c_2460,plain,(
    ! [B_114,A_281] :
      ( k9_subset_1(u1_struct_0('#skF_4'),B_114,A_281) = k3_xboole_0(B_114,A_281)
      | ~ r1_tarski(A_281,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_2394,c_270])).

tff(c_451,plain,(
    ! [B_17,B_142,A_16] :
      ( k9_subset_1(B_17,B_142,A_16) = k9_subset_1(B_17,A_16,B_142)
      | ~ r1_tarski(A_16,B_17) ) ),
    inference(resolution,[status(thm)],[c_22,c_436])).

tff(c_2838,plain,(
    ! [B_296,A_297] :
      ( k9_subset_1(u1_struct_0('#skF_4'),B_296,A_297) = k9_subset_1(u1_struct_0('#skF_4'),A_297,B_296)
      | ~ r1_tarski(A_297,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_2394,c_451])).

tff(c_3892,plain,(
    ! [A_342,B_343] :
      ( k9_subset_1(u1_struct_0('#skF_4'),A_342,B_343) = k3_xboole_0(B_343,A_342)
      | ~ r1_tarski(A_342,'#skF_5')
      | ~ r1_tarski(A_342,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2460,c_2838])).

tff(c_42,plain,(
    ! [A_34,B_42,D_47] :
      ( k9_subset_1(u1_struct_0(A_34),B_42,D_47) != k6_domain_1(u1_struct_0(A_34),'#skF_3'(A_34,B_42))
      | ~ v3_pre_topc(D_47,A_34)
      | ~ m1_subset_1(D_47,k1_zfmisc_1(u1_struct_0(A_34)))
      | v2_tex_2(B_42,A_34)
      | ~ m1_subset_1(B_42,k1_zfmisc_1(u1_struct_0(A_34)))
      | ~ l1_pre_topc(A_34)
      | ~ v2_pre_topc(A_34)
      | v2_struct_0(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_3916,plain,(
    ! [A_342,B_343] :
      ( k6_domain_1(u1_struct_0('#skF_4'),'#skF_3'('#skF_4',A_342)) != k3_xboole_0(B_343,A_342)
      | ~ v3_pre_topc(B_343,'#skF_4')
      | ~ m1_subset_1(B_343,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_tex_2(A_342,'#skF_4')
      | ~ m1_subset_1(A_342,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ r1_tarski(A_342,'#skF_5')
      | ~ r1_tarski(A_342,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3892,c_42])).

tff(c_4007,plain,(
    ! [A_342,B_343] :
      ( k6_domain_1(u1_struct_0('#skF_4'),'#skF_3'('#skF_4',A_342)) != k3_xboole_0(B_343,A_342)
      | ~ v3_pre_topc(B_343,'#skF_4')
      | ~ m1_subset_1(B_343,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_tex_2(A_342,'#skF_4')
      | ~ m1_subset_1(A_342,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_struct_0('#skF_4')
      | ~ r1_tarski(A_342,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_54,c_3916])).

tff(c_4165,plain,(
    ! [A_347,B_348] :
      ( k6_domain_1(u1_struct_0('#skF_4'),'#skF_3'('#skF_4',A_347)) != k3_xboole_0(B_348,A_347)
      | ~ v3_pre_topc(B_348,'#skF_4')
      | ~ m1_subset_1(B_348,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_tex_2(A_347,'#skF_4')
      | ~ m1_subset_1(A_347,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r1_tarski(A_347,'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_4007])).

tff(c_4172,plain,
    ( k6_domain_1(u1_struct_0('#skF_4'),'#skF_3'('#skF_4','#skF_5')) != k1_tarski('#skF_3'('#skF_4','#skF_5'))
    | ~ v3_pre_topc(k2_pre_topc('#skF_4',k1_tarski('#skF_3'('#skF_4','#skF_5'))),'#skF_4')
    | ~ m1_subset_1(k2_pre_topc('#skF_4',k1_tarski('#skF_3'('#skF_4','#skF_5'))),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | v2_tex_2('#skF_5','#skF_4')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ r1_tarski('#skF_5','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1589,c_4165])).

tff(c_4192,plain,
    ( ~ v3_pre_topc(k2_pre_topc('#skF_4',k1_tarski('#skF_3'('#skF_4','#skF_5'))),'#skF_4')
    | ~ m1_subset_1(k2_pre_topc('#skF_4',k1_tarski('#skF_3'('#skF_4','#skF_5'))),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | v2_tex_2('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_52,c_1434,c_4172])).

tff(c_4193,plain,
    ( ~ v3_pre_topc(k2_pre_topc('#skF_4',k1_tarski('#skF_3'('#skF_4','#skF_5'))),'#skF_4')
    | ~ m1_subset_1(k2_pre_topc('#skF_4',k1_tarski('#skF_3'('#skF_4','#skF_5'))),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_4192])).

tff(c_4472,plain,(
    ~ m1_subset_1(k2_pre_topc('#skF_4',k1_tarski('#skF_3'('#skF_4','#skF_5'))),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_4193])).

tff(c_4475,plain,
    ( ~ m1_subset_1(k1_tarski('#skF_3'('#skF_4','#skF_5')),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_4472])).

tff(c_4481,plain,(
    ~ m1_subset_1(k1_tarski('#skF_3'('#skF_4','#skF_5')),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_4475])).

tff(c_4485,plain,(
    ~ r2_hidden('#skF_3'('#skF_4','#skF_5'),u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_18,c_4481])).

tff(c_4492,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1346,c_4485])).

tff(c_4493,plain,(
    ~ v3_pre_topc(k2_pre_topc('#skF_4',k1_tarski('#skF_3'('#skF_4','#skF_5'))),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_4193])).

tff(c_56,plain,(
    v3_tdlat_3('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_4494,plain,(
    m1_subset_1(k2_pre_topc('#skF_4',k1_tarski('#skF_3'('#skF_4','#skF_5'))),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_4193])).

tff(c_34,plain,(
    ! [B_33,A_30] :
      ( v3_pre_topc(B_33,A_30)
      | ~ v4_pre_topc(B_33,A_30)
      | ~ m1_subset_1(B_33,k1_zfmisc_1(u1_struct_0(A_30)))
      | ~ v3_tdlat_3(A_30)
      | ~ l1_pre_topc(A_30)
      | ~ v2_pre_topc(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_4509,plain,
    ( v3_pre_topc(k2_pre_topc('#skF_4',k1_tarski('#skF_3'('#skF_4','#skF_5'))),'#skF_4')
    | ~ v4_pre_topc(k2_pre_topc('#skF_4',k1_tarski('#skF_3'('#skF_4','#skF_5'))),'#skF_4')
    | ~ v3_tdlat_3('#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_4494,c_34])).

tff(c_4536,plain,
    ( v3_pre_topc(k2_pre_topc('#skF_4',k1_tarski('#skF_3'('#skF_4','#skF_5'))),'#skF_4')
    | ~ v4_pre_topc(k2_pre_topc('#skF_4',k1_tarski('#skF_3'('#skF_4','#skF_5'))),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_54,c_56,c_4509])).

tff(c_4537,plain,(
    ~ v4_pre_topc(k2_pre_topc('#skF_4',k1_tarski('#skF_3'('#skF_4','#skF_5'))),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_4493,c_4536])).

tff(c_4550,plain,
    ( ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | ~ r2_hidden('#skF_3'('#skF_4','#skF_5'),u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_589,c_4537])).

tff(c_4557,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1346,c_58,c_54,c_4550])).

tff(c_4559,plain,(
    v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_123])).

tff(c_4599,plain,(
    ! [B_362,A_363,A_364] :
      ( ~ v1_xboole_0(B_362)
      | ~ r2_hidden(A_363,A_364)
      | ~ r1_tarski(A_364,B_362) ) ),
    inference(resolution,[status(thm)],[c_22,c_114])).

tff(c_4603,plain,(
    ! [B_365,A_366,B_367] :
      ( ~ v1_xboole_0(B_365)
      | ~ r1_tarski(A_366,B_365)
      | r1_tarski(A_366,B_367) ) ),
    inference(resolution,[status(thm)],[c_6,c_4599])).

tff(c_4614,plain,(
    ! [B_368,B_369] :
      ( ~ v1_xboole_0(B_368)
      | r1_tarski(B_368,B_369) ) ),
    inference(resolution,[status(thm)],[c_12,c_4603])).

tff(c_82,plain,(
    ! [B_59,A_60] :
      ( B_59 = A_60
      | ~ r1_tarski(B_59,A_60)
      | ~ r1_tarski(A_60,B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_87,plain,
    ( u1_struct_0('#skF_4') = '#skF_5'
    | ~ r1_tarski(u1_struct_0('#skF_4'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_67,c_82])).

tff(c_92,plain,(
    ~ r1_tarski(u1_struct_0('#skF_4'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_87])).

tff(c_4623,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_4614,c_92])).

tff(c_4631,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4559,c_4623])).

tff(c_4632,plain,(
    u1_struct_0('#skF_4') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_87])).

tff(c_4636,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4632,c_52])).

tff(c_86857,plain,(
    ! [A_2004,B_2005] :
      ( r2_hidden('#skF_3'(A_2004,B_2005),B_2005)
      | v2_tex_2(B_2005,A_2004)
      | ~ m1_subset_1(B_2005,k1_zfmisc_1(u1_struct_0(A_2004)))
      | ~ l1_pre_topc(A_2004)
      | ~ v2_pre_topc(A_2004)
      | v2_struct_0(A_2004) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_86869,plain,(
    ! [B_2005] :
      ( r2_hidden('#skF_3'('#skF_4',B_2005),B_2005)
      | v2_tex_2(B_2005,'#skF_4')
      | ~ m1_subset_1(B_2005,k1_zfmisc_1('#skF_5'))
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4632,c_86857])).

tff(c_86878,plain,(
    ! [B_2005] :
      ( r2_hidden('#skF_3'('#skF_4',B_2005),B_2005)
      | v2_tex_2(B_2005,'#skF_4')
      | ~ m1_subset_1(B_2005,k1_zfmisc_1('#skF_5'))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_54,c_86869])).

tff(c_86928,plain,(
    ! [B_2011] :
      ( r2_hidden('#skF_3'('#skF_4',B_2011),B_2011)
      | v2_tex_2(B_2011,'#skF_4')
      | ~ m1_subset_1(B_2011,k1_zfmisc_1('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_86878])).

tff(c_5760,plain,(
    ! [A_517,B_518] :
      ( r2_hidden('#skF_3'(A_517,B_518),B_518)
      | v2_tex_2(B_518,A_517)
      | ~ m1_subset_1(B_518,k1_zfmisc_1(u1_struct_0(A_517)))
      | ~ l1_pre_topc(A_517)
      | ~ v2_pre_topc(A_517)
      | v2_struct_0(A_517) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_7800,plain,(
    ! [A_665,A_666] :
      ( r2_hidden('#skF_3'(A_665,A_666),A_666)
      | v2_tex_2(A_666,A_665)
      | ~ l1_pre_topc(A_665)
      | ~ v2_pre_topc(A_665)
      | v2_struct_0(A_665)
      | ~ r1_tarski(A_666,u1_struct_0(A_665)) ) ),
    inference(resolution,[status(thm)],[c_22,c_5760])).

tff(c_7877,plain,(
    ! [A_665,A_666,B_2] :
      ( r2_hidden('#skF_3'(A_665,A_666),B_2)
      | ~ r1_tarski(A_666,B_2)
      | v2_tex_2(A_666,A_665)
      | ~ l1_pre_topc(A_665)
      | ~ v2_pre_topc(A_665)
      | v2_struct_0(A_665)
      | ~ r1_tarski(A_666,u1_struct_0(A_665)) ) ),
    inference(resolution,[status(thm)],[c_7800,c_2])).

tff(c_5775,plain,(
    ! [B_518] :
      ( r2_hidden('#skF_3'('#skF_4',B_518),B_518)
      | v2_tex_2(B_518,'#skF_4')
      | ~ m1_subset_1(B_518,k1_zfmisc_1('#skF_5'))
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4632,c_5760])).

tff(c_5785,plain,(
    ! [B_518] :
      ( r2_hidden('#skF_3'('#skF_4',B_518),B_518)
      | v2_tex_2(B_518,'#skF_4')
      | ~ m1_subset_1(B_518,k1_zfmisc_1('#skF_5'))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_54,c_5775])).

tff(c_5817,plain,(
    ! [B_521] :
      ( r2_hidden('#skF_3'('#skF_4',B_521),B_521)
      | v2_tex_2(B_521,'#skF_4')
      | ~ m1_subset_1(B_521,k1_zfmisc_1('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_5785])).

tff(c_4746,plain,(
    ! [A_405,C_406,B_407] :
      ( m1_subset_1(A_405,C_406)
      | ~ m1_subset_1(B_407,k1_zfmisc_1(C_406))
      | ~ r2_hidden(A_405,B_407) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_4754,plain,(
    ! [A_405] :
      ( m1_subset_1(A_405,'#skF_5')
      | ~ r2_hidden(A_405,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_4636,c_4746])).

tff(c_5841,plain,
    ( m1_subset_1('#skF_3'('#skF_4','#skF_5'),'#skF_5')
    | v2_tex_2('#skF_5','#skF_4')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_5817,c_4754])).

tff(c_5861,plain,
    ( m1_subset_1('#skF_3'('#skF_4','#skF_5'),'#skF_5')
    | v2_tex_2('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4636,c_5841])).

tff(c_5862,plain,(
    m1_subset_1('#skF_3'('#skF_4','#skF_5'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_5861])).

tff(c_4678,plain,(
    ! [C_382,B_383,A_384] :
      ( ~ v1_xboole_0(C_382)
      | ~ m1_subset_1(B_383,k1_zfmisc_1(C_382))
      | ~ r2_hidden(A_384,B_383) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_4686,plain,(
    ! [A_384] :
      ( ~ v1_xboole_0('#skF_5')
      | ~ r2_hidden(A_384,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_4636,c_4678])).

tff(c_4688,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_4686])).

tff(c_5869,plain,
    ( k6_domain_1('#skF_5','#skF_3'('#skF_4','#skF_5')) = k1_tarski('#skF_3'('#skF_4','#skF_5'))
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_5862,c_30])).

tff(c_5872,plain,(
    k6_domain_1('#skF_5','#skF_3'('#skF_4','#skF_5')) = k1_tarski('#skF_3'('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_4688,c_5869])).

tff(c_4788,plain,(
    ! [A_418,B_419,C_420] :
      ( k9_subset_1(A_418,B_419,C_420) = k3_xboole_0(B_419,C_420)
      | ~ m1_subset_1(C_420,k1_zfmisc_1(A_418)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_4812,plain,(
    ! [B_425,B_426,A_427] :
      ( k9_subset_1(B_425,B_426,A_427) = k3_xboole_0(B_426,A_427)
      | ~ r1_tarski(A_427,B_425) ) ),
    inference(resolution,[status(thm)],[c_22,c_4788])).

tff(c_4821,plain,(
    ! [B_7,B_426] : k9_subset_1(B_7,B_426,B_7) = k3_xboole_0(B_426,B_7) ),
    inference(resolution,[status(thm)],[c_12,c_4812])).

tff(c_4919,plain,(
    ! [A_441,C_442,B_443] :
      ( k9_subset_1(A_441,C_442,B_443) = k9_subset_1(A_441,B_443,C_442)
      | ~ m1_subset_1(C_442,k1_zfmisc_1(A_441)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_4923,plain,(
    ! [B_443] : k9_subset_1('#skF_5',B_443,'#skF_5') = k9_subset_1('#skF_5','#skF_5',B_443) ),
    inference(resolution,[status(thm)],[c_4636,c_4919])).

tff(c_4928,plain,(
    ! [B_443] : k9_subset_1('#skF_5','#skF_5',B_443) = k3_xboole_0(B_443,'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4821,c_4923])).

tff(c_4634,plain,(
    ! [C_52] :
      ( k9_subset_1('#skF_5','#skF_5',k2_pre_topc('#skF_4',k6_domain_1('#skF_5',C_52))) = k6_domain_1('#skF_5',C_52)
      | ~ r2_hidden(C_52,'#skF_5')
      | ~ m1_subset_1(C_52,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4632,c_4632,c_4632,c_4632,c_50])).

tff(c_4930,plain,(
    ! [C_52] :
      ( k3_xboole_0(k2_pre_topc('#skF_4',k6_domain_1('#skF_5',C_52)),'#skF_5') = k6_domain_1('#skF_5',C_52)
      | ~ r2_hidden(C_52,'#skF_5')
      | ~ m1_subset_1(C_52,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4928,c_4634])).

tff(c_5941,plain,
    ( k3_xboole_0(k2_pre_topc('#skF_4',k1_tarski('#skF_3'('#skF_4','#skF_5'))),'#skF_5') = k6_domain_1('#skF_5','#skF_3'('#skF_4','#skF_5'))
    | ~ r2_hidden('#skF_3'('#skF_4','#skF_5'),'#skF_5')
    | ~ m1_subset_1('#skF_3'('#skF_4','#skF_5'),'#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_5872,c_4930])).

tff(c_5945,plain,
    ( k3_xboole_0(k2_pre_topc('#skF_4',k1_tarski('#skF_3'('#skF_4','#skF_5'))),'#skF_5') = k1_tarski('#skF_3'('#skF_4','#skF_5'))
    | ~ r2_hidden('#skF_3'('#skF_4','#skF_5'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5862,c_5872,c_5941])).

tff(c_83250,plain,(
    ~ r2_hidden('#skF_3'('#skF_4','#skF_5'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_5945])).

tff(c_83253,plain,
    ( ~ r1_tarski('#skF_5','#skF_5')
    | v2_tex_2('#skF_5','#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4')
    | ~ r1_tarski('#skF_5',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_7877,c_83250])).

tff(c_83265,plain,
    ( v2_tex_2('#skF_5','#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_4632,c_58,c_54,c_12,c_83253])).

tff(c_83267,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_48,c_83265])).

tff(c_83269,plain,(
    r2_hidden('#skF_3'('#skF_4','#skF_5'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_5945])).

tff(c_83268,plain,(
    k3_xboole_0(k2_pre_topc('#skF_4',k1_tarski('#skF_3'('#skF_4','#skF_5'))),'#skF_5') = k1_tarski('#skF_3'('#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_5945])).

tff(c_5283,plain,(
    ! [A_474,B_475] :
      ( v4_pre_topc(k2_pre_topc(A_474,B_475),A_474)
      | ~ m1_subset_1(B_475,k1_zfmisc_1(u1_struct_0(A_474)))
      | ~ l1_pre_topc(A_474)
      | ~ v2_pre_topc(A_474) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_5293,plain,(
    ! [B_475] :
      ( v4_pre_topc(k2_pre_topc('#skF_4',B_475),'#skF_4')
      | ~ m1_subset_1(B_475,k1_zfmisc_1('#skF_5'))
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4632,c_5283])).

tff(c_5301,plain,(
    ! [B_475] :
      ( v4_pre_topc(k2_pre_topc('#skF_4',B_475),'#skF_4')
      | ~ m1_subset_1(B_475,k1_zfmisc_1('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_54,c_5293])).

tff(c_5346,plain,(
    ! [A_487,B_488] :
      ( m1_subset_1(k2_pre_topc(A_487,B_488),k1_zfmisc_1(u1_struct_0(A_487)))
      | ~ m1_subset_1(B_488,k1_zfmisc_1(u1_struct_0(A_487)))
      | ~ l1_pre_topc(A_487) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_5365,plain,(
    ! [B_488] :
      ( m1_subset_1(k2_pre_topc('#skF_4',B_488),k1_zfmisc_1('#skF_5'))
      | ~ m1_subset_1(B_488,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4632,c_5346])).

tff(c_5374,plain,(
    ! [B_488] :
      ( m1_subset_1(k2_pre_topc('#skF_4',B_488),k1_zfmisc_1('#skF_5'))
      | ~ m1_subset_1(B_488,k1_zfmisc_1('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_4632,c_5365])).

tff(c_5618,plain,(
    ! [B_506,A_507] :
      ( v3_pre_topc(B_506,A_507)
      | ~ v4_pre_topc(B_506,A_507)
      | ~ m1_subset_1(B_506,k1_zfmisc_1(u1_struct_0(A_507)))
      | ~ v3_tdlat_3(A_507)
      | ~ l1_pre_topc(A_507)
      | ~ v2_pre_topc(A_507) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_5635,plain,(
    ! [B_506] :
      ( v3_pre_topc(B_506,'#skF_4')
      | ~ v4_pre_topc(B_506,'#skF_4')
      | ~ m1_subset_1(B_506,k1_zfmisc_1('#skF_5'))
      | ~ v3_tdlat_3('#skF_4')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4632,c_5618])).

tff(c_5647,plain,(
    ! [B_508] :
      ( v3_pre_topc(B_508,'#skF_4')
      | ~ v4_pre_topc(B_508,'#skF_4')
      | ~ m1_subset_1(B_508,k1_zfmisc_1('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_54,c_56,c_5635])).

tff(c_6298,plain,(
    ! [B_567] :
      ( v3_pre_topc(k2_pre_topc('#skF_4',B_567),'#skF_4')
      | ~ v4_pre_topc(k2_pre_topc('#skF_4',B_567),'#skF_4')
      | ~ m1_subset_1(B_567,k1_zfmisc_1('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_5374,c_5647])).

tff(c_6323,plain,(
    ! [B_475] :
      ( v3_pre_topc(k2_pre_topc('#skF_4',B_475),'#skF_4')
      | ~ m1_subset_1(B_475,k1_zfmisc_1('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_5301,c_6298])).

tff(c_4975,plain,(
    ! [B_446,B_447,A_448] :
      ( k9_subset_1(B_446,B_447,A_448) = k9_subset_1(B_446,A_448,B_447)
      | ~ r1_tarski(A_448,B_446) ) ),
    inference(resolution,[status(thm)],[c_22,c_4919])).

tff(c_4981,plain,(
    ! [B_7,B_447] : k9_subset_1(B_7,B_7,B_447) = k9_subset_1(B_7,B_447,B_7) ),
    inference(resolution,[status(thm)],[c_12,c_4975])).

tff(c_4985,plain,(
    ! [B_7,B_447] : k9_subset_1(B_7,B_7,B_447) = k3_xboole_0(B_447,B_7) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4821,c_4981])).

tff(c_6079,plain,(
    ! [A_543,B_544,D_545] :
      ( k9_subset_1(u1_struct_0(A_543),B_544,D_545) != k6_domain_1(u1_struct_0(A_543),'#skF_3'(A_543,B_544))
      | ~ v3_pre_topc(D_545,A_543)
      | ~ m1_subset_1(D_545,k1_zfmisc_1(u1_struct_0(A_543)))
      | v2_tex_2(B_544,A_543)
      | ~ m1_subset_1(B_544,k1_zfmisc_1(u1_struct_0(A_543)))
      | ~ l1_pre_topc(A_543)
      | ~ v2_pre_topc(A_543)
      | v2_struct_0(A_543) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_6102,plain,(
    ! [B_544,D_545] :
      ( k9_subset_1('#skF_5',B_544,D_545) != k6_domain_1(u1_struct_0('#skF_4'),'#skF_3'('#skF_4',B_544))
      | ~ v3_pre_topc(D_545,'#skF_4')
      | ~ m1_subset_1(D_545,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_tex_2(B_544,'#skF_4')
      | ~ m1_subset_1(B_544,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4632,c_6079])).

tff(c_6106,plain,(
    ! [B_544,D_545] :
      ( k9_subset_1('#skF_5',B_544,D_545) != k6_domain_1('#skF_5','#skF_3'('#skF_4',B_544))
      | ~ v3_pre_topc(D_545,'#skF_4')
      | ~ m1_subset_1(D_545,k1_zfmisc_1('#skF_5'))
      | v2_tex_2(B_544,'#skF_4')
      | ~ m1_subset_1(B_544,k1_zfmisc_1('#skF_5'))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_54,c_4632,c_4632,c_4632,c_6102])).

tff(c_6185,plain,(
    ! [B_554,D_555] :
      ( k9_subset_1('#skF_5',B_554,D_555) != k6_domain_1('#skF_5','#skF_3'('#skF_4',B_554))
      | ~ v3_pre_topc(D_555,'#skF_4')
      | ~ m1_subset_1(D_555,k1_zfmisc_1('#skF_5'))
      | v2_tex_2(B_554,'#skF_4')
      | ~ m1_subset_1(B_554,k1_zfmisc_1('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_6106])).

tff(c_6202,plain,(
    ! [B_447] :
      ( k6_domain_1('#skF_5','#skF_3'('#skF_4','#skF_5')) != k3_xboole_0(B_447,'#skF_5')
      | ~ v3_pre_topc(B_447,'#skF_4')
      | ~ m1_subset_1(B_447,k1_zfmisc_1('#skF_5'))
      | v2_tex_2('#skF_5','#skF_4')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4985,c_6185])).

tff(c_6210,plain,(
    ! [B_447] :
      ( k3_xboole_0(B_447,'#skF_5') != k1_tarski('#skF_3'('#skF_4','#skF_5'))
      | ~ v3_pre_topc(B_447,'#skF_4')
      | ~ m1_subset_1(B_447,k1_zfmisc_1('#skF_5'))
      | v2_tex_2('#skF_5','#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4636,c_5872,c_6202])).

tff(c_6419,plain,(
    ! [B_579] :
      ( k3_xboole_0(B_579,'#skF_5') != k1_tarski('#skF_3'('#skF_4','#skF_5'))
      | ~ v3_pre_topc(B_579,'#skF_4')
      | ~ m1_subset_1(B_579,k1_zfmisc_1('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_6210])).

tff(c_9339,plain,(
    ! [B_735] :
      ( k3_xboole_0(k2_pre_topc('#skF_4',B_735),'#skF_5') != k1_tarski('#skF_3'('#skF_4','#skF_5'))
      | ~ v3_pre_topc(k2_pre_topc('#skF_4',B_735),'#skF_4')
      | ~ m1_subset_1(B_735,k1_zfmisc_1('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_5374,c_6419])).

tff(c_9352,plain,(
    ! [B_736] :
      ( k3_xboole_0(k2_pre_topc('#skF_4',B_736),'#skF_5') != k1_tarski('#skF_3'('#skF_4','#skF_5'))
      | ~ m1_subset_1(B_736,k1_zfmisc_1('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_6323,c_9339])).

tff(c_9394,plain,(
    ! [A_14] :
      ( k3_xboole_0(k2_pre_topc('#skF_4',k1_tarski(A_14)),'#skF_5') != k1_tarski('#skF_3'('#skF_4','#skF_5'))
      | ~ r2_hidden(A_14,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_18,c_9352])).

tff(c_84726,plain,(
    ~ r2_hidden('#skF_3'('#skF_4','#skF_5'),'#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_83268,c_9394])).

tff(c_84748,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_83269,c_84726])).

tff(c_84749,plain,(
    ! [A_384] : ~ r2_hidden(A_384,'#skF_5') ),
    inference(splitRight,[status(thm)],[c_4686])).

tff(c_86953,plain,
    ( v2_tex_2('#skF_5','#skF_4')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_86928,c_84749])).

tff(c_86966,plain,(
    v2_tex_2('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4636,c_86953])).

tff(c_86968,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_86966])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:33:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 27.78/17.59  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 27.78/17.61  
% 27.78/17.61  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 27.88/17.61  %$ v4_pre_topc > v3_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k6_domain_1 > k3_xboole_0 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_3 > #skF_5 > #skF_4 > #skF_1
% 27.88/17.61  
% 27.88/17.61  %Foreground sorts:
% 27.88/17.61  
% 27.88/17.61  
% 27.88/17.61  %Background operators:
% 27.88/17.61  
% 27.88/17.61  
% 27.88/17.61  %Foreground operators:
% 27.88/17.61  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 27.88/17.61  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 27.88/17.61  tff('#skF_2', type, '#skF_2': $i > $i).
% 27.88/17.61  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 27.88/17.61  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 27.88/17.61  tff(k1_tarski, type, k1_tarski: $i > $i).
% 27.88/17.61  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 27.88/17.61  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 27.88/17.61  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 27.88/17.61  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 27.88/17.61  tff('#skF_5', type, '#skF_5': $i).
% 27.88/17.61  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 27.88/17.61  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 27.88/17.61  tff(v3_tdlat_3, type, v3_tdlat_3: $i > $o).
% 27.88/17.61  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 27.88/17.61  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 27.88/17.61  tff('#skF_4', type, '#skF_4': $i).
% 27.88/17.61  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 27.88/17.61  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 27.88/17.61  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 27.88/17.61  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 27.88/17.61  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 27.88/17.61  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 27.88/17.61  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 27.88/17.61  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 27.88/17.61  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 27.88/17.61  
% 27.92/17.64  tff(f_149, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_hidden(C, B) => (k9_subset_1(u1_struct_0(A), B, k2_pre_topc(A, k6_domain_1(u1_struct_0(A), C))) = k6_domain_1(u1_struct_0(A), C))))) => v2_tex_2(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t58_tex_2)).
% 27.92/17.64  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 27.92/17.64  tff(f_54, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 27.92/17.64  tff(f_127, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((![C]: (m1_subset_1(C, u1_struct_0(A)) => ~(r2_hidden(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(v3_pre_topc(D, A) & (k9_subset_1(u1_struct_0(A), B, D) = k6_domain_1(u1_struct_0(A), C)))))))) => v2_tex_2(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_tex_2)).
% 27.92/17.64  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 27.92/17.64  tff(f_50, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(k1_tarski(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_subset_1)).
% 27.92/17.64  tff(f_88, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v4_pre_topc(k2_pre_topc(A, B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_tops_1)).
% 27.92/17.64  tff(f_73, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 27.92/17.64  tff(f_67, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 27.92/17.64  tff(f_60, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 27.92/17.64  tff(f_80, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 27.92/17.64  tff(f_46, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 27.92/17.64  tff(f_42, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k9_subset_1(A, C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k9_subset_1)).
% 27.92/17.64  tff(f_101, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (v3_tdlat_3(A) <=> (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => v3_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_tdlat_3)).
% 27.92/17.64  tff(c_48, plain, (~v2_tex_2('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_149])).
% 27.92/17.64  tff(c_12, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 27.92/17.64  tff(c_52, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_149])).
% 27.92/17.64  tff(c_63, plain, (![A_54, B_55]: (r1_tarski(A_54, B_55) | ~m1_subset_1(A_54, k1_zfmisc_1(B_55)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 27.92/17.64  tff(c_67, plain, (r1_tarski('#skF_5', u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_52, c_63])).
% 27.92/17.64  tff(c_60, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_149])).
% 27.92/17.64  tff(c_58, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_149])).
% 27.92/17.64  tff(c_54, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_149])).
% 27.92/17.64  tff(c_1100, plain, (![A_195, B_196]: (r2_hidden('#skF_3'(A_195, B_196), B_196) | v2_tex_2(B_196, A_195) | ~m1_subset_1(B_196, k1_zfmisc_1(u1_struct_0(A_195))) | ~l1_pre_topc(A_195) | ~v2_pre_topc(A_195) | v2_struct_0(A_195))), inference(cnfTransformation, [status(thm)], [f_127])).
% 27.92/17.64  tff(c_1118, plain, (r2_hidden('#skF_3'('#skF_4', '#skF_5'), '#skF_5') | v2_tex_2('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_52, c_1100])).
% 27.92/17.64  tff(c_1127, plain, (r2_hidden('#skF_3'('#skF_4', '#skF_5'), '#skF_5') | v2_tex_2('#skF_5', '#skF_4') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_54, c_1118])).
% 27.92/17.64  tff(c_1128, plain, (r2_hidden('#skF_3'('#skF_4', '#skF_5'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_60, c_48, c_1127])).
% 27.92/17.64  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 27.92/17.64  tff(c_1163, plain, (![B_198]: (r2_hidden('#skF_3'('#skF_4', '#skF_5'), B_198) | ~r1_tarski('#skF_5', B_198))), inference(resolution, [status(thm)], [c_1128, c_2])).
% 27.92/17.64  tff(c_1321, plain, (![B_208, B_209]: (r2_hidden('#skF_3'('#skF_4', '#skF_5'), B_208) | ~r1_tarski(B_209, B_208) | ~r1_tarski('#skF_5', B_209))), inference(resolution, [status(thm)], [c_1163, c_2])).
% 27.92/17.64  tff(c_1335, plain, (r2_hidden('#skF_3'('#skF_4', '#skF_5'), u1_struct_0('#skF_4')) | ~r1_tarski('#skF_5', '#skF_5')), inference(resolution, [status(thm)], [c_67, c_1321])).
% 27.92/17.64  tff(c_1346, plain, (r2_hidden('#skF_3'('#skF_4', '#skF_5'), u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_1335])).
% 27.92/17.64  tff(c_18, plain, (![A_14, B_15]: (m1_subset_1(k1_tarski(A_14), k1_zfmisc_1(B_15)) | ~r2_hidden(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_50])).
% 27.92/17.64  tff(c_573, plain, (![A_153, B_154]: (v4_pre_topc(k2_pre_topc(A_153, B_154), A_153) | ~m1_subset_1(B_154, k1_zfmisc_1(u1_struct_0(A_153))) | ~l1_pre_topc(A_153) | ~v2_pre_topc(A_153))), inference(cnfTransformation, [status(thm)], [f_88])).
% 27.92/17.64  tff(c_589, plain, (![A_153, A_14]: (v4_pre_topc(k2_pre_topc(A_153, k1_tarski(A_14)), A_153) | ~l1_pre_topc(A_153) | ~v2_pre_topc(A_153) | ~r2_hidden(A_14, u1_struct_0(A_153)))), inference(resolution, [status(thm)], [c_18, c_573])).
% 27.92/17.64  tff(c_28, plain, (![A_24, B_25]: (m1_subset_1(k2_pre_topc(A_24, B_25), k1_zfmisc_1(u1_struct_0(A_24))) | ~m1_subset_1(B_25, k1_zfmisc_1(u1_struct_0(A_24))) | ~l1_pre_topc(A_24))), inference(cnfTransformation, [status(thm)], [f_73])).
% 27.92/17.64  tff(c_114, plain, (![C_72, B_73, A_74]: (~v1_xboole_0(C_72) | ~m1_subset_1(B_73, k1_zfmisc_1(C_72)) | ~r2_hidden(A_74, B_73))), inference(cnfTransformation, [status(thm)], [f_67])).
% 27.92/17.64  tff(c_123, plain, (![A_74]: (~v1_xboole_0(u1_struct_0('#skF_4')) | ~r2_hidden(A_74, '#skF_5'))), inference(resolution, [status(thm)], [c_52, c_114])).
% 27.92/17.64  tff(c_124, plain, (~v1_xboole_0(u1_struct_0('#skF_4'))), inference(splitLeft, [status(thm)], [c_123])).
% 27.92/17.64  tff(c_22, plain, (![A_16, B_17]: (m1_subset_1(A_16, k1_zfmisc_1(B_17)) | ~r1_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_54])).
% 27.92/17.64  tff(c_150, plain, (![A_83, C_84, B_85]: (m1_subset_1(A_83, C_84) | ~m1_subset_1(B_85, k1_zfmisc_1(C_84)) | ~r2_hidden(A_83, B_85))), inference(cnfTransformation, [status(thm)], [f_60])).
% 27.92/17.64  tff(c_158, plain, (![A_83, B_17, A_16]: (m1_subset_1(A_83, B_17) | ~r2_hidden(A_83, A_16) | ~r1_tarski(A_16, B_17))), inference(resolution, [status(thm)], [c_22, c_150])).
% 27.92/17.64  tff(c_1385, plain, (![B_211]: (m1_subset_1('#skF_3'('#skF_4', '#skF_5'), B_211) | ~r1_tarski(u1_struct_0('#skF_4'), B_211))), inference(resolution, [status(thm)], [c_1346, c_158])).
% 27.92/17.64  tff(c_1395, plain, (m1_subset_1('#skF_3'('#skF_4', '#skF_5'), u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_12, c_1385])).
% 27.92/17.64  tff(c_30, plain, (![A_26, B_27]: (k6_domain_1(A_26, B_27)=k1_tarski(B_27) | ~m1_subset_1(B_27, A_26) | v1_xboole_0(A_26))), inference(cnfTransformation, [status(thm)], [f_80])).
% 27.92/17.64  tff(c_1431, plain, (k6_domain_1(u1_struct_0('#skF_4'), '#skF_3'('#skF_4', '#skF_5'))=k1_tarski('#skF_3'('#skF_4', '#skF_5')) | v1_xboole_0(u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_1395, c_30])).
% 27.92/17.64  tff(c_1434, plain, (k6_domain_1(u1_struct_0('#skF_4'), '#skF_3'('#skF_4', '#skF_5'))=k1_tarski('#skF_3'('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_124, c_1431])).
% 27.92/17.64  tff(c_262, plain, (![A_113, B_114, C_115]: (k9_subset_1(A_113, B_114, C_115)=k3_xboole_0(B_114, C_115) | ~m1_subset_1(C_115, k1_zfmisc_1(A_113)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 27.92/17.64  tff(c_271, plain, (![B_114]: (k9_subset_1(u1_struct_0('#skF_4'), B_114, '#skF_5')=k3_xboole_0(B_114, '#skF_5'))), inference(resolution, [status(thm)], [c_52, c_262])).
% 27.92/17.64  tff(c_436, plain, (![A_140, C_141, B_142]: (k9_subset_1(A_140, C_141, B_142)=k9_subset_1(A_140, B_142, C_141) | ~m1_subset_1(C_141, k1_zfmisc_1(A_140)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 27.92/17.64  tff(c_447, plain, (![B_142]: (k9_subset_1(u1_struct_0('#skF_4'), B_142, '#skF_5')=k9_subset_1(u1_struct_0('#skF_4'), '#skF_5', B_142))), inference(resolution, [status(thm)], [c_52, c_436])).
% 27.92/17.64  tff(c_453, plain, (![B_142]: (k9_subset_1(u1_struct_0('#skF_4'), '#skF_5', B_142)=k3_xboole_0(B_142, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_271, c_447])).
% 27.92/17.64  tff(c_50, plain, (![C_52]: (k9_subset_1(u1_struct_0('#skF_4'), '#skF_5', k2_pre_topc('#skF_4', k6_domain_1(u1_struct_0('#skF_4'), C_52)))=k6_domain_1(u1_struct_0('#skF_4'), C_52) | ~r2_hidden(C_52, '#skF_5') | ~m1_subset_1(C_52, u1_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_149])).
% 27.92/17.64  tff(c_455, plain, (![C_52]: (k3_xboole_0(k2_pre_topc('#skF_4', k6_domain_1(u1_struct_0('#skF_4'), C_52)), '#skF_5')=k6_domain_1(u1_struct_0('#skF_4'), C_52) | ~r2_hidden(C_52, '#skF_5') | ~m1_subset_1(C_52, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_453, c_50])).
% 27.92/17.64  tff(c_1576, plain, (k3_xboole_0(k2_pre_topc('#skF_4', k1_tarski('#skF_3'('#skF_4', '#skF_5'))), '#skF_5')=k6_domain_1(u1_struct_0('#skF_4'), '#skF_3'('#skF_4', '#skF_5')) | ~r2_hidden('#skF_3'('#skF_4', '#skF_5'), '#skF_5') | ~m1_subset_1('#skF_3'('#skF_4', '#skF_5'), u1_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1434, c_455])).
% 27.92/17.64  tff(c_1589, plain, (k3_xboole_0(k2_pre_topc('#skF_4', k1_tarski('#skF_3'('#skF_4', '#skF_5'))), '#skF_5')=k1_tarski('#skF_3'('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_1395, c_1128, c_1434, c_1576])).
% 27.92/17.64  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 27.92/17.64  tff(c_110, plain, (![C_69, B_70, A_71]: (r2_hidden(C_69, B_70) | ~r2_hidden(C_69, A_71) | ~r1_tarski(A_71, B_70))), inference(cnfTransformation, [status(thm)], [f_32])).
% 27.92/17.64  tff(c_335, plain, (![A_127, B_128, B_129]: (r2_hidden('#skF_1'(A_127, B_128), B_129) | ~r1_tarski(A_127, B_129) | r1_tarski(A_127, B_128))), inference(resolution, [status(thm)], [c_6, c_110])).
% 27.92/17.64  tff(c_2251, plain, (![A_274, B_275, B_276, B_277]: (r2_hidden('#skF_1'(A_274, B_275), B_276) | ~r1_tarski(B_277, B_276) | ~r1_tarski(A_274, B_277) | r1_tarski(A_274, B_275))), inference(resolution, [status(thm)], [c_335, c_2])).
% 27.92/17.64  tff(c_2285, plain, (![A_278, B_279]: (r2_hidden('#skF_1'(A_278, B_279), u1_struct_0('#skF_4')) | ~r1_tarski(A_278, '#skF_5') | r1_tarski(A_278, B_279))), inference(resolution, [status(thm)], [c_67, c_2251])).
% 27.92/17.64  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 27.92/17.64  tff(c_2394, plain, (![A_281]: (~r1_tarski(A_281, '#skF_5') | r1_tarski(A_281, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_2285, c_4])).
% 27.92/17.64  tff(c_270, plain, (![B_17, B_114, A_16]: (k9_subset_1(B_17, B_114, A_16)=k3_xboole_0(B_114, A_16) | ~r1_tarski(A_16, B_17))), inference(resolution, [status(thm)], [c_22, c_262])).
% 27.92/17.64  tff(c_2460, plain, (![B_114, A_281]: (k9_subset_1(u1_struct_0('#skF_4'), B_114, A_281)=k3_xboole_0(B_114, A_281) | ~r1_tarski(A_281, '#skF_5'))), inference(resolution, [status(thm)], [c_2394, c_270])).
% 27.92/17.64  tff(c_451, plain, (![B_17, B_142, A_16]: (k9_subset_1(B_17, B_142, A_16)=k9_subset_1(B_17, A_16, B_142) | ~r1_tarski(A_16, B_17))), inference(resolution, [status(thm)], [c_22, c_436])).
% 27.92/17.64  tff(c_2838, plain, (![B_296, A_297]: (k9_subset_1(u1_struct_0('#skF_4'), B_296, A_297)=k9_subset_1(u1_struct_0('#skF_4'), A_297, B_296) | ~r1_tarski(A_297, '#skF_5'))), inference(resolution, [status(thm)], [c_2394, c_451])).
% 27.92/17.64  tff(c_3892, plain, (![A_342, B_343]: (k9_subset_1(u1_struct_0('#skF_4'), A_342, B_343)=k3_xboole_0(B_343, A_342) | ~r1_tarski(A_342, '#skF_5') | ~r1_tarski(A_342, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_2460, c_2838])).
% 27.92/17.64  tff(c_42, plain, (![A_34, B_42, D_47]: (k9_subset_1(u1_struct_0(A_34), B_42, D_47)!=k6_domain_1(u1_struct_0(A_34), '#skF_3'(A_34, B_42)) | ~v3_pre_topc(D_47, A_34) | ~m1_subset_1(D_47, k1_zfmisc_1(u1_struct_0(A_34))) | v2_tex_2(B_42, A_34) | ~m1_subset_1(B_42, k1_zfmisc_1(u1_struct_0(A_34))) | ~l1_pre_topc(A_34) | ~v2_pre_topc(A_34) | v2_struct_0(A_34))), inference(cnfTransformation, [status(thm)], [f_127])).
% 27.92/17.64  tff(c_3916, plain, (![A_342, B_343]: (k6_domain_1(u1_struct_0('#skF_4'), '#skF_3'('#skF_4', A_342))!=k3_xboole_0(B_343, A_342) | ~v3_pre_topc(B_343, '#skF_4') | ~m1_subset_1(B_343, k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_tex_2(A_342, '#skF_4') | ~m1_subset_1(A_342, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~r1_tarski(A_342, '#skF_5') | ~r1_tarski(A_342, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_3892, c_42])).
% 27.92/17.64  tff(c_4007, plain, (![A_342, B_343]: (k6_domain_1(u1_struct_0('#skF_4'), '#skF_3'('#skF_4', A_342))!=k3_xboole_0(B_343, A_342) | ~v3_pre_topc(B_343, '#skF_4') | ~m1_subset_1(B_343, k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_tex_2(A_342, '#skF_4') | ~m1_subset_1(A_342, k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_struct_0('#skF_4') | ~r1_tarski(A_342, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_54, c_3916])).
% 27.92/17.64  tff(c_4165, plain, (![A_347, B_348]: (k6_domain_1(u1_struct_0('#skF_4'), '#skF_3'('#skF_4', A_347))!=k3_xboole_0(B_348, A_347) | ~v3_pre_topc(B_348, '#skF_4') | ~m1_subset_1(B_348, k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_tex_2(A_347, '#skF_4') | ~m1_subset_1(A_347, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r1_tarski(A_347, '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_60, c_4007])).
% 27.92/17.64  tff(c_4172, plain, (k6_domain_1(u1_struct_0('#skF_4'), '#skF_3'('#skF_4', '#skF_5'))!=k1_tarski('#skF_3'('#skF_4', '#skF_5')) | ~v3_pre_topc(k2_pre_topc('#skF_4', k1_tarski('#skF_3'('#skF_4', '#skF_5'))), '#skF_4') | ~m1_subset_1(k2_pre_topc('#skF_4', k1_tarski('#skF_3'('#skF_4', '#skF_5'))), k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_tex_2('#skF_5', '#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r1_tarski('#skF_5', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1589, c_4165])).
% 27.92/17.64  tff(c_4192, plain, (~v3_pre_topc(k2_pre_topc('#skF_4', k1_tarski('#skF_3'('#skF_4', '#skF_5'))), '#skF_4') | ~m1_subset_1(k2_pre_topc('#skF_4', k1_tarski('#skF_3'('#skF_4', '#skF_5'))), k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_tex_2('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_52, c_1434, c_4172])).
% 27.92/17.64  tff(c_4193, plain, (~v3_pre_topc(k2_pre_topc('#skF_4', k1_tarski('#skF_3'('#skF_4', '#skF_5'))), '#skF_4') | ~m1_subset_1(k2_pre_topc('#skF_4', k1_tarski('#skF_3'('#skF_4', '#skF_5'))), k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_48, c_4192])).
% 27.92/17.64  tff(c_4472, plain, (~m1_subset_1(k2_pre_topc('#skF_4', k1_tarski('#skF_3'('#skF_4', '#skF_5'))), k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(splitLeft, [status(thm)], [c_4193])).
% 27.92/17.64  tff(c_4475, plain, (~m1_subset_1(k1_tarski('#skF_3'('#skF_4', '#skF_5')), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_28, c_4472])).
% 27.92/17.64  tff(c_4481, plain, (~m1_subset_1(k1_tarski('#skF_3'('#skF_4', '#skF_5')), k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_4475])).
% 27.92/17.64  tff(c_4485, plain, (~r2_hidden('#skF_3'('#skF_4', '#skF_5'), u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_18, c_4481])).
% 27.92/17.64  tff(c_4492, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1346, c_4485])).
% 27.92/17.64  tff(c_4493, plain, (~v3_pre_topc(k2_pre_topc('#skF_4', k1_tarski('#skF_3'('#skF_4', '#skF_5'))), '#skF_4')), inference(splitRight, [status(thm)], [c_4193])).
% 27.92/17.64  tff(c_56, plain, (v3_tdlat_3('#skF_4')), inference(cnfTransformation, [status(thm)], [f_149])).
% 27.92/17.64  tff(c_4494, plain, (m1_subset_1(k2_pre_topc('#skF_4', k1_tarski('#skF_3'('#skF_4', '#skF_5'))), k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(splitRight, [status(thm)], [c_4193])).
% 27.92/17.64  tff(c_34, plain, (![B_33, A_30]: (v3_pre_topc(B_33, A_30) | ~v4_pre_topc(B_33, A_30) | ~m1_subset_1(B_33, k1_zfmisc_1(u1_struct_0(A_30))) | ~v3_tdlat_3(A_30) | ~l1_pre_topc(A_30) | ~v2_pre_topc(A_30))), inference(cnfTransformation, [status(thm)], [f_101])).
% 27.92/17.64  tff(c_4509, plain, (v3_pre_topc(k2_pre_topc('#skF_4', k1_tarski('#skF_3'('#skF_4', '#skF_5'))), '#skF_4') | ~v4_pre_topc(k2_pre_topc('#skF_4', k1_tarski('#skF_3'('#skF_4', '#skF_5'))), '#skF_4') | ~v3_tdlat_3('#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_4494, c_34])).
% 27.92/17.64  tff(c_4536, plain, (v3_pre_topc(k2_pre_topc('#skF_4', k1_tarski('#skF_3'('#skF_4', '#skF_5'))), '#skF_4') | ~v4_pre_topc(k2_pre_topc('#skF_4', k1_tarski('#skF_3'('#skF_4', '#skF_5'))), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_54, c_56, c_4509])).
% 27.92/17.64  tff(c_4537, plain, (~v4_pre_topc(k2_pre_topc('#skF_4', k1_tarski('#skF_3'('#skF_4', '#skF_5'))), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_4493, c_4536])).
% 27.92/17.64  tff(c_4550, plain, (~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | ~r2_hidden('#skF_3'('#skF_4', '#skF_5'), u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_589, c_4537])).
% 27.92/17.64  tff(c_4557, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1346, c_58, c_54, c_4550])).
% 27.92/17.64  tff(c_4559, plain, (v1_xboole_0(u1_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_123])).
% 27.92/17.64  tff(c_4599, plain, (![B_362, A_363, A_364]: (~v1_xboole_0(B_362) | ~r2_hidden(A_363, A_364) | ~r1_tarski(A_364, B_362))), inference(resolution, [status(thm)], [c_22, c_114])).
% 27.92/17.64  tff(c_4603, plain, (![B_365, A_366, B_367]: (~v1_xboole_0(B_365) | ~r1_tarski(A_366, B_365) | r1_tarski(A_366, B_367))), inference(resolution, [status(thm)], [c_6, c_4599])).
% 27.92/17.64  tff(c_4614, plain, (![B_368, B_369]: (~v1_xboole_0(B_368) | r1_tarski(B_368, B_369))), inference(resolution, [status(thm)], [c_12, c_4603])).
% 27.92/17.64  tff(c_82, plain, (![B_59, A_60]: (B_59=A_60 | ~r1_tarski(B_59, A_60) | ~r1_tarski(A_60, B_59))), inference(cnfTransformation, [status(thm)], [f_38])).
% 27.92/17.64  tff(c_87, plain, (u1_struct_0('#skF_4')='#skF_5' | ~r1_tarski(u1_struct_0('#skF_4'), '#skF_5')), inference(resolution, [status(thm)], [c_67, c_82])).
% 27.92/17.64  tff(c_92, plain, (~r1_tarski(u1_struct_0('#skF_4'), '#skF_5')), inference(splitLeft, [status(thm)], [c_87])).
% 27.92/17.64  tff(c_4623, plain, (~v1_xboole_0(u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_4614, c_92])).
% 27.92/17.64  tff(c_4631, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4559, c_4623])).
% 27.92/17.64  tff(c_4632, plain, (u1_struct_0('#skF_4')='#skF_5'), inference(splitRight, [status(thm)], [c_87])).
% 27.92/17.64  tff(c_4636, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_4632, c_52])).
% 27.92/17.64  tff(c_86857, plain, (![A_2004, B_2005]: (r2_hidden('#skF_3'(A_2004, B_2005), B_2005) | v2_tex_2(B_2005, A_2004) | ~m1_subset_1(B_2005, k1_zfmisc_1(u1_struct_0(A_2004))) | ~l1_pre_topc(A_2004) | ~v2_pre_topc(A_2004) | v2_struct_0(A_2004))), inference(cnfTransformation, [status(thm)], [f_127])).
% 27.92/17.64  tff(c_86869, plain, (![B_2005]: (r2_hidden('#skF_3'('#skF_4', B_2005), B_2005) | v2_tex_2(B_2005, '#skF_4') | ~m1_subset_1(B_2005, k1_zfmisc_1('#skF_5')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_4632, c_86857])).
% 27.92/17.64  tff(c_86878, plain, (![B_2005]: (r2_hidden('#skF_3'('#skF_4', B_2005), B_2005) | v2_tex_2(B_2005, '#skF_4') | ~m1_subset_1(B_2005, k1_zfmisc_1('#skF_5')) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_54, c_86869])).
% 27.92/17.64  tff(c_86928, plain, (![B_2011]: (r2_hidden('#skF_3'('#skF_4', B_2011), B_2011) | v2_tex_2(B_2011, '#skF_4') | ~m1_subset_1(B_2011, k1_zfmisc_1('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_60, c_86878])).
% 27.92/17.64  tff(c_5760, plain, (![A_517, B_518]: (r2_hidden('#skF_3'(A_517, B_518), B_518) | v2_tex_2(B_518, A_517) | ~m1_subset_1(B_518, k1_zfmisc_1(u1_struct_0(A_517))) | ~l1_pre_topc(A_517) | ~v2_pre_topc(A_517) | v2_struct_0(A_517))), inference(cnfTransformation, [status(thm)], [f_127])).
% 27.92/17.64  tff(c_7800, plain, (![A_665, A_666]: (r2_hidden('#skF_3'(A_665, A_666), A_666) | v2_tex_2(A_666, A_665) | ~l1_pre_topc(A_665) | ~v2_pre_topc(A_665) | v2_struct_0(A_665) | ~r1_tarski(A_666, u1_struct_0(A_665)))), inference(resolution, [status(thm)], [c_22, c_5760])).
% 27.92/17.64  tff(c_7877, plain, (![A_665, A_666, B_2]: (r2_hidden('#skF_3'(A_665, A_666), B_2) | ~r1_tarski(A_666, B_2) | v2_tex_2(A_666, A_665) | ~l1_pre_topc(A_665) | ~v2_pre_topc(A_665) | v2_struct_0(A_665) | ~r1_tarski(A_666, u1_struct_0(A_665)))), inference(resolution, [status(thm)], [c_7800, c_2])).
% 27.92/17.64  tff(c_5775, plain, (![B_518]: (r2_hidden('#skF_3'('#skF_4', B_518), B_518) | v2_tex_2(B_518, '#skF_4') | ~m1_subset_1(B_518, k1_zfmisc_1('#skF_5')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_4632, c_5760])).
% 27.92/17.64  tff(c_5785, plain, (![B_518]: (r2_hidden('#skF_3'('#skF_4', B_518), B_518) | v2_tex_2(B_518, '#skF_4') | ~m1_subset_1(B_518, k1_zfmisc_1('#skF_5')) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_54, c_5775])).
% 27.92/17.64  tff(c_5817, plain, (![B_521]: (r2_hidden('#skF_3'('#skF_4', B_521), B_521) | v2_tex_2(B_521, '#skF_4') | ~m1_subset_1(B_521, k1_zfmisc_1('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_60, c_5785])).
% 27.92/17.64  tff(c_4746, plain, (![A_405, C_406, B_407]: (m1_subset_1(A_405, C_406) | ~m1_subset_1(B_407, k1_zfmisc_1(C_406)) | ~r2_hidden(A_405, B_407))), inference(cnfTransformation, [status(thm)], [f_60])).
% 27.92/17.64  tff(c_4754, plain, (![A_405]: (m1_subset_1(A_405, '#skF_5') | ~r2_hidden(A_405, '#skF_5'))), inference(resolution, [status(thm)], [c_4636, c_4746])).
% 27.92/17.64  tff(c_5841, plain, (m1_subset_1('#skF_3'('#skF_4', '#skF_5'), '#skF_5') | v2_tex_2('#skF_5', '#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_5'))), inference(resolution, [status(thm)], [c_5817, c_4754])).
% 27.92/17.64  tff(c_5861, plain, (m1_subset_1('#skF_3'('#skF_4', '#skF_5'), '#skF_5') | v2_tex_2('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4636, c_5841])).
% 27.92/17.64  tff(c_5862, plain, (m1_subset_1('#skF_3'('#skF_4', '#skF_5'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_48, c_5861])).
% 27.92/17.64  tff(c_4678, plain, (![C_382, B_383, A_384]: (~v1_xboole_0(C_382) | ~m1_subset_1(B_383, k1_zfmisc_1(C_382)) | ~r2_hidden(A_384, B_383))), inference(cnfTransformation, [status(thm)], [f_67])).
% 27.92/17.64  tff(c_4686, plain, (![A_384]: (~v1_xboole_0('#skF_5') | ~r2_hidden(A_384, '#skF_5'))), inference(resolution, [status(thm)], [c_4636, c_4678])).
% 27.92/17.64  tff(c_4688, plain, (~v1_xboole_0('#skF_5')), inference(splitLeft, [status(thm)], [c_4686])).
% 27.92/17.64  tff(c_5869, plain, (k6_domain_1('#skF_5', '#skF_3'('#skF_4', '#skF_5'))=k1_tarski('#skF_3'('#skF_4', '#skF_5')) | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_5862, c_30])).
% 27.92/17.64  tff(c_5872, plain, (k6_domain_1('#skF_5', '#skF_3'('#skF_4', '#skF_5'))=k1_tarski('#skF_3'('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_4688, c_5869])).
% 27.92/17.64  tff(c_4788, plain, (![A_418, B_419, C_420]: (k9_subset_1(A_418, B_419, C_420)=k3_xboole_0(B_419, C_420) | ~m1_subset_1(C_420, k1_zfmisc_1(A_418)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 27.92/17.64  tff(c_4812, plain, (![B_425, B_426, A_427]: (k9_subset_1(B_425, B_426, A_427)=k3_xboole_0(B_426, A_427) | ~r1_tarski(A_427, B_425))), inference(resolution, [status(thm)], [c_22, c_4788])).
% 27.92/17.64  tff(c_4821, plain, (![B_7, B_426]: (k9_subset_1(B_7, B_426, B_7)=k3_xboole_0(B_426, B_7))), inference(resolution, [status(thm)], [c_12, c_4812])).
% 27.92/17.64  tff(c_4919, plain, (![A_441, C_442, B_443]: (k9_subset_1(A_441, C_442, B_443)=k9_subset_1(A_441, B_443, C_442) | ~m1_subset_1(C_442, k1_zfmisc_1(A_441)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 27.92/17.64  tff(c_4923, plain, (![B_443]: (k9_subset_1('#skF_5', B_443, '#skF_5')=k9_subset_1('#skF_5', '#skF_5', B_443))), inference(resolution, [status(thm)], [c_4636, c_4919])).
% 27.92/17.64  tff(c_4928, plain, (![B_443]: (k9_subset_1('#skF_5', '#skF_5', B_443)=k3_xboole_0(B_443, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_4821, c_4923])).
% 27.92/17.64  tff(c_4634, plain, (![C_52]: (k9_subset_1('#skF_5', '#skF_5', k2_pre_topc('#skF_4', k6_domain_1('#skF_5', C_52)))=k6_domain_1('#skF_5', C_52) | ~r2_hidden(C_52, '#skF_5') | ~m1_subset_1(C_52, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_4632, c_4632, c_4632, c_4632, c_50])).
% 27.92/17.64  tff(c_4930, plain, (![C_52]: (k3_xboole_0(k2_pre_topc('#skF_4', k6_domain_1('#skF_5', C_52)), '#skF_5')=k6_domain_1('#skF_5', C_52) | ~r2_hidden(C_52, '#skF_5') | ~m1_subset_1(C_52, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_4928, c_4634])).
% 27.92/17.64  tff(c_5941, plain, (k3_xboole_0(k2_pre_topc('#skF_4', k1_tarski('#skF_3'('#skF_4', '#skF_5'))), '#skF_5')=k6_domain_1('#skF_5', '#skF_3'('#skF_4', '#skF_5')) | ~r2_hidden('#skF_3'('#skF_4', '#skF_5'), '#skF_5') | ~m1_subset_1('#skF_3'('#skF_4', '#skF_5'), '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_5872, c_4930])).
% 27.92/17.64  tff(c_5945, plain, (k3_xboole_0(k2_pre_topc('#skF_4', k1_tarski('#skF_3'('#skF_4', '#skF_5'))), '#skF_5')=k1_tarski('#skF_3'('#skF_4', '#skF_5')) | ~r2_hidden('#skF_3'('#skF_4', '#skF_5'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_5862, c_5872, c_5941])).
% 27.92/17.64  tff(c_83250, plain, (~r2_hidden('#skF_3'('#skF_4', '#skF_5'), '#skF_5')), inference(splitLeft, [status(thm)], [c_5945])).
% 27.92/17.64  tff(c_83253, plain, (~r1_tarski('#skF_5', '#skF_5') | v2_tex_2('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~r1_tarski('#skF_5', u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_7877, c_83250])).
% 27.92/17.64  tff(c_83265, plain, (v2_tex_2('#skF_5', '#skF_4') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_4632, c_58, c_54, c_12, c_83253])).
% 27.92/17.64  tff(c_83267, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_48, c_83265])).
% 27.92/17.64  tff(c_83269, plain, (r2_hidden('#skF_3'('#skF_4', '#skF_5'), '#skF_5')), inference(splitRight, [status(thm)], [c_5945])).
% 27.92/17.64  tff(c_83268, plain, (k3_xboole_0(k2_pre_topc('#skF_4', k1_tarski('#skF_3'('#skF_4', '#skF_5'))), '#skF_5')=k1_tarski('#skF_3'('#skF_4', '#skF_5'))), inference(splitRight, [status(thm)], [c_5945])).
% 27.92/17.64  tff(c_5283, plain, (![A_474, B_475]: (v4_pre_topc(k2_pre_topc(A_474, B_475), A_474) | ~m1_subset_1(B_475, k1_zfmisc_1(u1_struct_0(A_474))) | ~l1_pre_topc(A_474) | ~v2_pre_topc(A_474))), inference(cnfTransformation, [status(thm)], [f_88])).
% 27.92/17.64  tff(c_5293, plain, (![B_475]: (v4_pre_topc(k2_pre_topc('#skF_4', B_475), '#skF_4') | ~m1_subset_1(B_475, k1_zfmisc_1('#skF_5')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_4632, c_5283])).
% 27.92/17.64  tff(c_5301, plain, (![B_475]: (v4_pre_topc(k2_pre_topc('#skF_4', B_475), '#skF_4') | ~m1_subset_1(B_475, k1_zfmisc_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_54, c_5293])).
% 27.92/17.64  tff(c_5346, plain, (![A_487, B_488]: (m1_subset_1(k2_pre_topc(A_487, B_488), k1_zfmisc_1(u1_struct_0(A_487))) | ~m1_subset_1(B_488, k1_zfmisc_1(u1_struct_0(A_487))) | ~l1_pre_topc(A_487))), inference(cnfTransformation, [status(thm)], [f_73])).
% 27.92/17.64  tff(c_5365, plain, (![B_488]: (m1_subset_1(k2_pre_topc('#skF_4', B_488), k1_zfmisc_1('#skF_5')) | ~m1_subset_1(B_488, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_4632, c_5346])).
% 27.92/17.64  tff(c_5374, plain, (![B_488]: (m1_subset_1(k2_pre_topc('#skF_4', B_488), k1_zfmisc_1('#skF_5')) | ~m1_subset_1(B_488, k1_zfmisc_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_4632, c_5365])).
% 27.92/17.64  tff(c_5618, plain, (![B_506, A_507]: (v3_pre_topc(B_506, A_507) | ~v4_pre_topc(B_506, A_507) | ~m1_subset_1(B_506, k1_zfmisc_1(u1_struct_0(A_507))) | ~v3_tdlat_3(A_507) | ~l1_pre_topc(A_507) | ~v2_pre_topc(A_507))), inference(cnfTransformation, [status(thm)], [f_101])).
% 27.92/17.64  tff(c_5635, plain, (![B_506]: (v3_pre_topc(B_506, '#skF_4') | ~v4_pre_topc(B_506, '#skF_4') | ~m1_subset_1(B_506, k1_zfmisc_1('#skF_5')) | ~v3_tdlat_3('#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_4632, c_5618])).
% 27.92/17.64  tff(c_5647, plain, (![B_508]: (v3_pre_topc(B_508, '#skF_4') | ~v4_pre_topc(B_508, '#skF_4') | ~m1_subset_1(B_508, k1_zfmisc_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_54, c_56, c_5635])).
% 27.92/17.64  tff(c_6298, plain, (![B_567]: (v3_pre_topc(k2_pre_topc('#skF_4', B_567), '#skF_4') | ~v4_pre_topc(k2_pre_topc('#skF_4', B_567), '#skF_4') | ~m1_subset_1(B_567, k1_zfmisc_1('#skF_5')))), inference(resolution, [status(thm)], [c_5374, c_5647])).
% 27.92/17.64  tff(c_6323, plain, (![B_475]: (v3_pre_topc(k2_pre_topc('#skF_4', B_475), '#skF_4') | ~m1_subset_1(B_475, k1_zfmisc_1('#skF_5')))), inference(resolution, [status(thm)], [c_5301, c_6298])).
% 27.92/17.64  tff(c_4975, plain, (![B_446, B_447, A_448]: (k9_subset_1(B_446, B_447, A_448)=k9_subset_1(B_446, A_448, B_447) | ~r1_tarski(A_448, B_446))), inference(resolution, [status(thm)], [c_22, c_4919])).
% 27.92/17.64  tff(c_4981, plain, (![B_7, B_447]: (k9_subset_1(B_7, B_7, B_447)=k9_subset_1(B_7, B_447, B_7))), inference(resolution, [status(thm)], [c_12, c_4975])).
% 27.92/17.64  tff(c_4985, plain, (![B_7, B_447]: (k9_subset_1(B_7, B_7, B_447)=k3_xboole_0(B_447, B_7))), inference(demodulation, [status(thm), theory('equality')], [c_4821, c_4981])).
% 27.92/17.64  tff(c_6079, plain, (![A_543, B_544, D_545]: (k9_subset_1(u1_struct_0(A_543), B_544, D_545)!=k6_domain_1(u1_struct_0(A_543), '#skF_3'(A_543, B_544)) | ~v3_pre_topc(D_545, A_543) | ~m1_subset_1(D_545, k1_zfmisc_1(u1_struct_0(A_543))) | v2_tex_2(B_544, A_543) | ~m1_subset_1(B_544, k1_zfmisc_1(u1_struct_0(A_543))) | ~l1_pre_topc(A_543) | ~v2_pre_topc(A_543) | v2_struct_0(A_543))), inference(cnfTransformation, [status(thm)], [f_127])).
% 27.92/17.64  tff(c_6102, plain, (![B_544, D_545]: (k9_subset_1('#skF_5', B_544, D_545)!=k6_domain_1(u1_struct_0('#skF_4'), '#skF_3'('#skF_4', B_544)) | ~v3_pre_topc(D_545, '#skF_4') | ~m1_subset_1(D_545, k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_tex_2(B_544, '#skF_4') | ~m1_subset_1(B_544, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_4632, c_6079])).
% 27.92/17.64  tff(c_6106, plain, (![B_544, D_545]: (k9_subset_1('#skF_5', B_544, D_545)!=k6_domain_1('#skF_5', '#skF_3'('#skF_4', B_544)) | ~v3_pre_topc(D_545, '#skF_4') | ~m1_subset_1(D_545, k1_zfmisc_1('#skF_5')) | v2_tex_2(B_544, '#skF_4') | ~m1_subset_1(B_544, k1_zfmisc_1('#skF_5')) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_54, c_4632, c_4632, c_4632, c_6102])).
% 27.92/17.64  tff(c_6185, plain, (![B_554, D_555]: (k9_subset_1('#skF_5', B_554, D_555)!=k6_domain_1('#skF_5', '#skF_3'('#skF_4', B_554)) | ~v3_pre_topc(D_555, '#skF_4') | ~m1_subset_1(D_555, k1_zfmisc_1('#skF_5')) | v2_tex_2(B_554, '#skF_4') | ~m1_subset_1(B_554, k1_zfmisc_1('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_60, c_6106])).
% 27.92/17.64  tff(c_6202, plain, (![B_447]: (k6_domain_1('#skF_5', '#skF_3'('#skF_4', '#skF_5'))!=k3_xboole_0(B_447, '#skF_5') | ~v3_pre_topc(B_447, '#skF_4') | ~m1_subset_1(B_447, k1_zfmisc_1('#skF_5')) | v2_tex_2('#skF_5', '#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_4985, c_6185])).
% 27.92/17.64  tff(c_6210, plain, (![B_447]: (k3_xboole_0(B_447, '#skF_5')!=k1_tarski('#skF_3'('#skF_4', '#skF_5')) | ~v3_pre_topc(B_447, '#skF_4') | ~m1_subset_1(B_447, k1_zfmisc_1('#skF_5')) | v2_tex_2('#skF_5', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_4636, c_5872, c_6202])).
% 27.92/17.64  tff(c_6419, plain, (![B_579]: (k3_xboole_0(B_579, '#skF_5')!=k1_tarski('#skF_3'('#skF_4', '#skF_5')) | ~v3_pre_topc(B_579, '#skF_4') | ~m1_subset_1(B_579, k1_zfmisc_1('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_48, c_6210])).
% 27.92/17.64  tff(c_9339, plain, (![B_735]: (k3_xboole_0(k2_pre_topc('#skF_4', B_735), '#skF_5')!=k1_tarski('#skF_3'('#skF_4', '#skF_5')) | ~v3_pre_topc(k2_pre_topc('#skF_4', B_735), '#skF_4') | ~m1_subset_1(B_735, k1_zfmisc_1('#skF_5')))), inference(resolution, [status(thm)], [c_5374, c_6419])).
% 27.92/17.64  tff(c_9352, plain, (![B_736]: (k3_xboole_0(k2_pre_topc('#skF_4', B_736), '#skF_5')!=k1_tarski('#skF_3'('#skF_4', '#skF_5')) | ~m1_subset_1(B_736, k1_zfmisc_1('#skF_5')))), inference(resolution, [status(thm)], [c_6323, c_9339])).
% 27.92/17.64  tff(c_9394, plain, (![A_14]: (k3_xboole_0(k2_pre_topc('#skF_4', k1_tarski(A_14)), '#skF_5')!=k1_tarski('#skF_3'('#skF_4', '#skF_5')) | ~r2_hidden(A_14, '#skF_5'))), inference(resolution, [status(thm)], [c_18, c_9352])).
% 27.92/17.64  tff(c_84726, plain, (~r2_hidden('#skF_3'('#skF_4', '#skF_5'), '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_83268, c_9394])).
% 27.92/17.64  tff(c_84748, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_83269, c_84726])).
% 27.92/17.64  tff(c_84749, plain, (![A_384]: (~r2_hidden(A_384, '#skF_5'))), inference(splitRight, [status(thm)], [c_4686])).
% 27.92/17.64  tff(c_86953, plain, (v2_tex_2('#skF_5', '#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_5'))), inference(resolution, [status(thm)], [c_86928, c_84749])).
% 27.92/17.64  tff(c_86966, plain, (v2_tex_2('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4636, c_86953])).
% 27.92/17.64  tff(c_86968, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_86966])).
% 27.92/17.64  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 27.92/17.64  
% 27.92/17.64  Inference rules
% 27.92/17.64  ----------------------
% 27.92/17.64  #Ref     : 0
% 27.92/17.64  #Sup     : 21321
% 27.92/17.64  #Fact    : 12
% 27.92/17.64  #Define  : 0
% 27.92/17.64  #Split   : 57
% 27.92/17.64  #Chain   : 0
% 27.92/17.64  #Close   : 0
% 27.92/17.64  
% 27.92/17.64  Ordering : KBO
% 27.92/17.64  
% 27.92/17.64  Simplification rules
% 27.92/17.64  ----------------------
% 27.92/17.64  #Subsume      : 10625
% 27.92/17.64  #Demod        : 5811
% 27.92/17.64  #Tautology    : 3150
% 27.92/17.64  #SimpNegUnit  : 690
% 27.92/17.64  #BackRed      : 117
% 27.92/17.64  
% 27.92/17.64  #Partial instantiations: 0
% 27.92/17.64  #Strategies tried      : 1
% 27.92/17.64  
% 27.92/17.64  Timing (in seconds)
% 27.92/17.64  ----------------------
% 27.92/17.64  Preprocessing        : 0.36
% 27.92/17.64  Parsing              : 0.20
% 27.92/17.64  CNF conversion       : 0.02
% 27.92/17.64  Main loop            : 16.41
% 27.92/17.64  Inferencing          : 2.64
% 27.92/17.64  Reduction            : 3.67
% 27.92/17.64  Demodulation         : 2.47
% 27.92/17.65  BG Simplification    : 0.27
% 27.92/17.65  Subsumption          : 8.78
% 27.92/17.65  Abstraction          : 0.50
% 27.92/17.65  MUC search           : 0.00
% 27.92/17.65  Cooper               : 0.00
% 27.92/17.65  Total                : 16.82
% 27.92/17.65  Index Insertion      : 0.00
% 27.92/17.65  Index Deletion       : 0.00
% 27.92/17.65  Index Matching       : 0.00
% 27.92/17.65  BG Taut test         : 0.00
%------------------------------------------------------------------------------
