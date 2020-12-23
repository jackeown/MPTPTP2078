%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1855+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:33 EST 2020

% Result     : Theorem 4.17s
% Output     : CNFRefutation 4.43s
% Verified   : 
% Statistics : Number of formulae       :  161 (7044 expanded)
%              Number of leaves         :   38 (2313 expanded)
%              Depth                    :   35
%              Number of atoms          :  386 (26711 expanded)
%              Number of equality atoms :   40 (2339 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v7_struct_0 > v2_struct_0 > v1_xboole_0 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k6_domain_1 > k1_tex_2 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(g1_pre_topc,type,(
    g1_pre_topc: ( $i * $i ) > $i )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(v7_struct_0,type,(
    v7_struct_0: $i > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k1_tex_2,type,(
    k1_tex_2: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_162,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & v7_struct_0(B)
              & m1_pre_topc(B,A) )
           => ? [C] :
                ( m1_subset_1(C,u1_struct_0(A))
                & g1_pre_topc(u1_struct_0(B),u1_pre_topc(B)) = g1_pre_topc(u1_struct_0(k1_tex_2(A,C)),u1_pre_topc(k1_tex_2(A,C))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_tex_2)).

tff(f_88,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_81,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_36,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ( v7_struct_0(A)
      <=> ? [B] :
            ( m1_subset_1(B,u1_struct_0(A))
            & u1_struct_0(A) = k6_domain_1(u1_struct_0(A),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tex_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_118,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_110,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_96,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_114,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_zfmisc_1)).

tff(f_103,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l17_tex_2)).

tff(f_124,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_70,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ( ~ v2_struct_0(k1_tex_2(A,B))
        & v1_pre_topc(k1_tex_2(A,B))
        & m1_pre_topc(k1_tex_2(A,B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tex_2)).

tff(f_56,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( ( ~ v2_struct_0(C)
                & v1_pre_topc(C)
                & m1_pre_topc(C,A) )
             => ( C = k1_tex_2(A,B)
              <=> u1_struct_0(C) = k6_domain_1(u1_struct_0(A),B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tex_2)).

tff(f_131,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_143,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_pre_topc(C,A)
             => ( u1_struct_0(B) = u1_struct_0(C)
               => g1_pre_topc(u1_struct_0(B),u1_pre_topc(B)) = g1_pre_topc(u1_struct_0(C),u1_pre_topc(C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_tsep_1)).

tff(c_52,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_46,plain,(
    m1_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_54,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_50,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_70,plain,(
    ! [B_59,A_60] :
      ( l1_pre_topc(B_59)
      | ~ m1_pre_topc(B_59,A_60)
      | ~ l1_pre_topc(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_73,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_46,c_70])).

tff(c_76,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_73])).

tff(c_20,plain,(
    ! [A_16] :
      ( l1_struct_0(A_16)
      | ~ l1_pre_topc(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_48,plain,(
    v7_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_159,plain,(
    ! [A_95] :
      ( k6_domain_1(u1_struct_0(A_95),'#skF_1'(A_95)) = u1_struct_0(A_95)
      | ~ v7_struct_0(A_95)
      | ~ l1_struct_0(A_95)
      | v2_struct_0(A_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_92,plain,(
    ! [A_75,B_76] :
      ( m1_subset_1(k6_domain_1(A_75,B_76),k1_zfmisc_1(A_75))
      | ~ m1_subset_1(B_76,A_75)
      | v1_xboole_0(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_34,plain,(
    ! [A_28,B_29] :
      ( r1_tarski(A_28,B_29)
      | ~ m1_subset_1(A_28,k1_zfmisc_1(B_29)) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_106,plain,(
    ! [A_75,B_76] :
      ( r1_tarski(k6_domain_1(A_75,B_76),A_75)
      | ~ m1_subset_1(B_76,A_75)
      | v1_xboole_0(A_75) ) ),
    inference(resolution,[status(thm)],[c_92,c_34])).

tff(c_165,plain,(
    ! [A_95] :
      ( r1_tarski(u1_struct_0(A_95),u1_struct_0(A_95))
      | ~ m1_subset_1('#skF_1'(A_95),u1_struct_0(A_95))
      | v1_xboole_0(u1_struct_0(A_95))
      | ~ v7_struct_0(A_95)
      | ~ l1_struct_0(A_95)
      | v2_struct_0(A_95) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_159,c_106])).

tff(c_4,plain,(
    ! [A_1] :
      ( k6_domain_1(u1_struct_0(A_1),'#skF_1'(A_1)) = u1_struct_0(A_1)
      | ~ v7_struct_0(A_1)
      | ~ l1_struct_0(A_1)
      | v2_struct_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_124,plain,(
    ! [A_83] :
      ( m1_subset_1('#skF_1'(A_83),u1_struct_0(A_83))
      | ~ v7_struct_0(A_83)
      | ~ l1_struct_0(A_83)
      | v2_struct_0(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_28,plain,(
    ! [A_24,B_25] :
      ( k6_domain_1(A_24,B_25) = k1_tarski(B_25)
      | ~ m1_subset_1(B_25,A_24)
      | v1_xboole_0(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_195,plain,(
    ! [A_108] :
      ( k6_domain_1(u1_struct_0(A_108),'#skF_1'(A_108)) = k1_tarski('#skF_1'(A_108))
      | v1_xboole_0(u1_struct_0(A_108))
      | ~ v7_struct_0(A_108)
      | ~ l1_struct_0(A_108)
      | v2_struct_0(A_108) ) ),
    inference(resolution,[status(thm)],[c_124,c_28])).

tff(c_455,plain,(
    ! [A_142] :
      ( k1_tarski('#skF_1'(A_142)) = u1_struct_0(A_142)
      | v1_xboole_0(u1_struct_0(A_142))
      | ~ v7_struct_0(A_142)
      | ~ l1_struct_0(A_142)
      | v2_struct_0(A_142)
      | ~ v7_struct_0(A_142)
      | ~ l1_struct_0(A_142)
      | v2_struct_0(A_142) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_195])).

tff(c_24,plain,(
    ! [A_20] :
      ( ~ v1_xboole_0(u1_struct_0(A_20))
      | ~ l1_struct_0(A_20)
      | v2_struct_0(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_463,plain,(
    ! [A_143] :
      ( k1_tarski('#skF_1'(A_143)) = u1_struct_0(A_143)
      | ~ v7_struct_0(A_143)
      | ~ l1_struct_0(A_143)
      | v2_struct_0(A_143) ) ),
    inference(resolution,[status(thm)],[c_455,c_24])).

tff(c_30,plain,(
    ! [A_26,B_27] :
      ( r2_hidden(A_26,B_27)
      | ~ r1_tarski(k1_tarski(A_26),B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_492,plain,(
    ! [A_146,B_147] :
      ( r2_hidden('#skF_1'(A_146),B_147)
      | ~ r1_tarski(u1_struct_0(A_146),B_147)
      | ~ v7_struct_0(A_146)
      | ~ l1_struct_0(A_146)
      | v2_struct_0(A_146) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_463,c_30])).

tff(c_108,plain,(
    ! [B_79,A_80] :
      ( m1_subset_1(u1_struct_0(B_79),k1_zfmisc_1(u1_struct_0(A_80)))
      | ~ m1_pre_topc(B_79,A_80)
      | ~ l1_pre_topc(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_38,plain,(
    ! [A_30,C_32,B_31] :
      ( m1_subset_1(A_30,C_32)
      | ~ m1_subset_1(B_31,k1_zfmisc_1(C_32))
      | ~ r2_hidden(A_30,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_120,plain,(
    ! [A_30,A_80,B_79] :
      ( m1_subset_1(A_30,u1_struct_0(A_80))
      | ~ r2_hidden(A_30,u1_struct_0(B_79))
      | ~ m1_pre_topc(B_79,A_80)
      | ~ l1_pre_topc(A_80) ) ),
    inference(resolution,[status(thm)],[c_108,c_38])).

tff(c_572,plain,(
    ! [A_167,A_168,B_169] :
      ( m1_subset_1('#skF_1'(A_167),u1_struct_0(A_168))
      | ~ m1_pre_topc(B_169,A_168)
      | ~ l1_pre_topc(A_168)
      | ~ r1_tarski(u1_struct_0(A_167),u1_struct_0(B_169))
      | ~ v7_struct_0(A_167)
      | ~ l1_struct_0(A_167)
      | v2_struct_0(A_167) ) ),
    inference(resolution,[status(thm)],[c_492,c_120])).

tff(c_576,plain,(
    ! [A_167] :
      ( m1_subset_1('#skF_1'(A_167),u1_struct_0('#skF_2'))
      | ~ l1_pre_topc('#skF_2')
      | ~ r1_tarski(u1_struct_0(A_167),u1_struct_0('#skF_3'))
      | ~ v7_struct_0(A_167)
      | ~ l1_struct_0(A_167)
      | v2_struct_0(A_167) ) ),
    inference(resolution,[status(thm)],[c_46,c_572])).

tff(c_581,plain,(
    ! [A_170] :
      ( m1_subset_1('#skF_1'(A_170),u1_struct_0('#skF_2'))
      | ~ r1_tarski(u1_struct_0(A_170),u1_struct_0('#skF_3'))
      | ~ v7_struct_0(A_170)
      | ~ l1_struct_0(A_170)
      | v2_struct_0(A_170) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_576])).

tff(c_585,plain,
    ( m1_subset_1('#skF_1'('#skF_3'),u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_1'('#skF_3'),u1_struct_0('#skF_3'))
    | v1_xboole_0(u1_struct_0('#skF_3'))
    | ~ v7_struct_0('#skF_3')
    | ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_165,c_581])).

tff(c_592,plain,
    ( m1_subset_1('#skF_1'('#skF_3'),u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_1'('#skF_3'),u1_struct_0('#skF_3'))
    | v1_xboole_0(u1_struct_0('#skF_3'))
    | ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_585])).

tff(c_593,plain,
    ( m1_subset_1('#skF_1'('#skF_3'),u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_1'('#skF_3'),u1_struct_0('#skF_3'))
    | v1_xboole_0(u1_struct_0('#skF_3'))
    | ~ l1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_592])).

tff(c_635,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_593])).

tff(c_638,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_635])).

tff(c_642,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_638])).

tff(c_644,plain,(
    l1_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_593])).

tff(c_6,plain,(
    ! [A_1] :
      ( m1_subset_1('#skF_1'(A_1),u1_struct_0(A_1))
      | ~ v7_struct_0(A_1)
      | ~ l1_struct_0(A_1)
      | v2_struct_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_643,plain,
    ( ~ m1_subset_1('#skF_1'('#skF_3'),u1_struct_0('#skF_3'))
    | v1_xboole_0(u1_struct_0('#skF_3'))
    | m1_subset_1('#skF_1'('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_593])).

tff(c_645,plain,(
    ~ m1_subset_1('#skF_1'('#skF_3'),u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_643])).

tff(c_648,plain,
    ( ~ v7_struct_0('#skF_3')
    | ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_6,c_645])).

tff(c_651,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_644,c_48,c_648])).

tff(c_653,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_651])).

tff(c_654,plain,
    ( m1_subset_1('#skF_1'('#skF_3'),u1_struct_0('#skF_2'))
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_643])).

tff(c_716,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_654])).

tff(c_723,plain,
    ( ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_716,c_24])).

tff(c_732,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_644,c_723])).

tff(c_734,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_732])).

tff(c_735,plain,(
    m1_subset_1('#skF_1'('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_654])).

tff(c_12,plain,(
    ! [A_12,B_13] :
      ( m1_pre_topc(k1_tex_2(A_12,B_13),A_12)
      | ~ m1_subset_1(B_13,u1_struct_0(A_12))
      | ~ l1_pre_topc(A_12)
      | v2_struct_0(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_744,plain,
    ( m1_pre_topc(k1_tex_2('#skF_2','#skF_1'('#skF_3')),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_735,c_12])).

tff(c_761,plain,
    ( m1_pre_topc(k1_tex_2('#skF_2','#skF_1'('#skF_3')),'#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_744])).

tff(c_762,plain,(
    m1_pre_topc(k1_tex_2('#skF_2','#skF_1'('#skF_3')),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_761])).

tff(c_16,plain,(
    ! [A_12,B_13] :
      ( ~ v2_struct_0(k1_tex_2(A_12,B_13))
      | ~ m1_subset_1(B_13,u1_struct_0(A_12))
      | ~ l1_pre_topc(A_12)
      | v2_struct_0(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_750,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_2','#skF_1'('#skF_3')))
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_735,c_16])).

tff(c_769,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_2','#skF_1'('#skF_3')))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_750])).

tff(c_770,plain,(
    ~ v2_struct_0(k1_tex_2('#skF_2','#skF_1'('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_769])).

tff(c_14,plain,(
    ! [A_12,B_13] :
      ( v1_pre_topc(k1_tex_2(A_12,B_13))
      | ~ m1_subset_1(B_13,u1_struct_0(A_12))
      | ~ l1_pre_topc(A_12)
      | v2_struct_0(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_747,plain,
    ( v1_pre_topc(k1_tex_2('#skF_2','#skF_1'('#skF_3')))
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_735,c_14])).

tff(c_765,plain,
    ( v1_pre_topc(k1_tex_2('#skF_2','#skF_1'('#skF_3')))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_747])).

tff(c_766,plain,(
    v1_pre_topc(k1_tex_2('#skF_2','#skF_1'('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_765])).

tff(c_10,plain,(
    ! [A_5,B_9] :
      ( k6_domain_1(u1_struct_0(A_5),B_9) = u1_struct_0(k1_tex_2(A_5,B_9))
      | ~ m1_pre_topc(k1_tex_2(A_5,B_9),A_5)
      | ~ v1_pre_topc(k1_tex_2(A_5,B_9))
      | v2_struct_0(k1_tex_2(A_5,B_9))
      | ~ m1_subset_1(B_9,u1_struct_0(A_5))
      | ~ l1_pre_topc(A_5)
      | v2_struct_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_777,plain,
    ( k6_domain_1(u1_struct_0('#skF_2'),'#skF_1'('#skF_3')) = u1_struct_0(k1_tex_2('#skF_2','#skF_1'('#skF_3')))
    | ~ v1_pre_topc(k1_tex_2('#skF_2','#skF_1'('#skF_3')))
    | v2_struct_0(k1_tex_2('#skF_2','#skF_1'('#skF_3')))
    | ~ m1_subset_1('#skF_1'('#skF_3'),u1_struct_0('#skF_2'))
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_762,c_10])).

tff(c_792,plain,
    ( k6_domain_1(u1_struct_0('#skF_2'),'#skF_1'('#skF_3')) = u1_struct_0(k1_tex_2('#skF_2','#skF_1'('#skF_3')))
    | v2_struct_0(k1_tex_2('#skF_2','#skF_1'('#skF_3')))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_735,c_766,c_777])).

tff(c_793,plain,(
    k6_domain_1(u1_struct_0('#skF_2'),'#skF_1'('#skF_3')) = u1_struct_0(k1_tex_2('#skF_2','#skF_1'('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_770,c_792])).

tff(c_736,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_654])).

tff(c_655,plain,(
    m1_subset_1('#skF_1'('#skF_3'),u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_643])).

tff(c_666,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_3','#skF_1'('#skF_3')))
    | ~ l1_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_655,c_16])).

tff(c_684,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_3','#skF_1'('#skF_3')))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_666])).

tff(c_685,plain,(
    ~ v2_struct_0(k1_tex_2('#skF_3','#skF_1'('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_684])).

tff(c_663,plain,
    ( v1_pre_topc(k1_tex_2('#skF_3','#skF_1'('#skF_3')))
    | ~ l1_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_655,c_14])).

tff(c_680,plain,
    ( v1_pre_topc(k1_tex_2('#skF_3','#skF_1'('#skF_3')))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_663])).

tff(c_681,plain,(
    v1_pre_topc(k1_tex_2('#skF_3','#skF_1'('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_680])).

tff(c_660,plain,
    ( m1_pre_topc(k1_tex_2('#skF_3','#skF_1'('#skF_3')),'#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_655,c_12])).

tff(c_676,plain,
    ( m1_pre_topc(k1_tex_2('#skF_3','#skF_1'('#skF_3')),'#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_660])).

tff(c_677,plain,(
    m1_pre_topc(k1_tex_2('#skF_3','#skF_1'('#skF_3')),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_676])).

tff(c_692,plain,
    ( k6_domain_1(u1_struct_0('#skF_3'),'#skF_1'('#skF_3')) = u1_struct_0(k1_tex_2('#skF_3','#skF_1'('#skF_3')))
    | ~ v1_pre_topc(k1_tex_2('#skF_3','#skF_1'('#skF_3')))
    | v2_struct_0(k1_tex_2('#skF_3','#skF_1'('#skF_3')))
    | ~ m1_subset_1('#skF_1'('#skF_3'),u1_struct_0('#skF_3'))
    | ~ l1_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_677,c_10])).

tff(c_708,plain,
    ( k6_domain_1(u1_struct_0('#skF_3'),'#skF_1'('#skF_3')) = u1_struct_0(k1_tex_2('#skF_3','#skF_1'('#skF_3')))
    | v2_struct_0(k1_tex_2('#skF_3','#skF_1'('#skF_3')))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_655,c_681,c_692])).

tff(c_709,plain,(
    k6_domain_1(u1_struct_0('#skF_3'),'#skF_1'('#skF_3')) = u1_struct_0(k1_tex_2('#skF_3','#skF_1'('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_685,c_708])).

tff(c_814,plain,
    ( u1_struct_0(k1_tex_2('#skF_3','#skF_1'('#skF_3'))) = u1_struct_0('#skF_3')
    | ~ v7_struct_0('#skF_3')
    | ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_709,c_4])).

tff(c_842,plain,
    ( u1_struct_0(k1_tex_2('#skF_3','#skF_1'('#skF_3'))) = u1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_644,c_48,c_814])).

tff(c_843,plain,(
    u1_struct_0(k1_tex_2('#skF_3','#skF_1'('#skF_3'))) = u1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_842])).

tff(c_857,plain,(
    k6_domain_1(u1_struct_0('#skF_3'),'#skF_1'('#skF_3')) = u1_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_843,c_709])).

tff(c_128,plain,(
    ! [A_83] :
      ( k6_domain_1(u1_struct_0(A_83),'#skF_1'(A_83)) = k1_tarski('#skF_1'(A_83))
      | v1_xboole_0(u1_struct_0(A_83))
      | ~ v7_struct_0(A_83)
      | ~ l1_struct_0(A_83)
      | v2_struct_0(A_83) ) ),
    inference(resolution,[status(thm)],[c_124,c_28])).

tff(c_1024,plain,
    ( k1_tarski('#skF_1'('#skF_3')) = u1_struct_0('#skF_3')
    | v1_xboole_0(u1_struct_0('#skF_3'))
    | ~ v7_struct_0('#skF_3')
    | ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_857,c_128])).

tff(c_1052,plain,
    ( k1_tarski('#skF_1'('#skF_3')) = u1_struct_0('#skF_3')
    | v1_xboole_0(u1_struct_0('#skF_3'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_644,c_48,c_1024])).

tff(c_1053,plain,(
    k1_tarski('#skF_1'('#skF_3')) = u1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_736,c_1052])).

tff(c_771,plain,
    ( k6_domain_1(u1_struct_0('#skF_2'),'#skF_1'('#skF_3')) = k1_tarski('#skF_1'('#skF_3'))
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_735,c_28])).

tff(c_1414,plain,
    ( u1_struct_0(k1_tex_2('#skF_2','#skF_1'('#skF_3'))) = u1_struct_0('#skF_3')
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_793,c_1053,c_771])).

tff(c_1415,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_1414])).

tff(c_122,plain,(
    ! [B_79,A_80] :
      ( r1_tarski(u1_struct_0(B_79),u1_struct_0(A_80))
      | ~ m1_pre_topc(B_79,A_80)
      | ~ l1_pre_topc(A_80) ) ),
    inference(resolution,[status(thm)],[c_108,c_34])).

tff(c_1099,plain,(
    ! [B_27] :
      ( r2_hidden('#skF_1'('#skF_3'),B_27)
      | ~ r1_tarski(u1_struct_0('#skF_3'),B_27) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1053,c_30])).

tff(c_1033,plain,
    ( r1_tarski(u1_struct_0('#skF_3'),u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_1'('#skF_3'),u1_struct_0('#skF_3'))
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_857,c_106])).

tff(c_1062,plain,
    ( r1_tarski(u1_struct_0('#skF_3'),u1_struct_0('#skF_3'))
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_655,c_1033])).

tff(c_1063,plain,(
    r1_tarski(u1_struct_0('#skF_3'),u1_struct_0('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_736,c_1062])).

tff(c_32,plain,(
    ! [A_26,B_27] :
      ( r1_tarski(k1_tarski(A_26),B_27)
      | ~ r2_hidden(A_26,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_1188,plain,(
    ! [B_178] :
      ( r2_hidden('#skF_1'('#skF_3'),B_178)
      | ~ r1_tarski(u1_struct_0('#skF_3'),B_178) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1053,c_30])).

tff(c_36,plain,(
    ! [A_28,B_29] :
      ( m1_subset_1(A_28,k1_zfmisc_1(B_29))
      | ~ r1_tarski(A_28,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_77,plain,(
    ! [C_61,B_62,A_63] :
      ( ~ v1_xboole_0(C_61)
      | ~ m1_subset_1(B_62,k1_zfmisc_1(C_61))
      | ~ r2_hidden(A_63,B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_80,plain,(
    ! [B_29,A_63,A_28] :
      ( ~ v1_xboole_0(B_29)
      | ~ r2_hidden(A_63,A_28)
      | ~ r1_tarski(A_28,B_29) ) ),
    inference(resolution,[status(thm)],[c_36,c_77])).

tff(c_1280,plain,(
    ! [B_180,B_181] :
      ( ~ v1_xboole_0(B_180)
      | ~ r1_tarski(B_181,B_180)
      | ~ r1_tarski(u1_struct_0('#skF_3'),B_181) ) ),
    inference(resolution,[status(thm)],[c_1188,c_80])).

tff(c_1307,plain,(
    ! [B_182,A_183] :
      ( ~ v1_xboole_0(B_182)
      | ~ r1_tarski(u1_struct_0('#skF_3'),k1_tarski(A_183))
      | ~ r2_hidden(A_183,B_182) ) ),
    inference(resolution,[status(thm)],[c_32,c_1280])).

tff(c_1309,plain,(
    ! [B_182] :
      ( ~ v1_xboole_0(B_182)
      | ~ r1_tarski(u1_struct_0('#skF_3'),u1_struct_0('#skF_3'))
      | ~ r2_hidden('#skF_1'('#skF_3'),B_182) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1053,c_1307])).

tff(c_1343,plain,(
    ! [B_185] :
      ( ~ v1_xboole_0(B_185)
      | ~ r2_hidden('#skF_1'('#skF_3'),B_185) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1063,c_1309])).

tff(c_1361,plain,(
    ! [B_186] :
      ( ~ v1_xboole_0(B_186)
      | ~ r1_tarski(u1_struct_0('#skF_3'),B_186) ) ),
    inference(resolution,[status(thm)],[c_1099,c_1343])).

tff(c_1378,plain,(
    ! [A_80] :
      ( ~ v1_xboole_0(u1_struct_0(A_80))
      | ~ m1_pre_topc('#skF_3',A_80)
      | ~ l1_pre_topc(A_80) ) ),
    inference(resolution,[status(thm)],[c_122,c_1361])).

tff(c_1418,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_1415,c_1378])).

tff(c_1429,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_46,c_1418])).

tff(c_1430,plain,(
    u1_struct_0(k1_tex_2('#skF_2','#skF_1'('#skF_3'))) = u1_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_1414])).

tff(c_81,plain,(
    ! [A_64,C_65,B_66] :
      ( m1_subset_1(A_64,C_65)
      | ~ m1_subset_1(B_66,k1_zfmisc_1(C_65))
      | ~ r2_hidden(A_64,B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_84,plain,(
    ! [A_64,B_29,A_28] :
      ( m1_subset_1(A_64,B_29)
      | ~ r2_hidden(A_64,A_28)
      | ~ r1_tarski(A_28,B_29) ) ),
    inference(resolution,[status(thm)],[c_36,c_81])).

tff(c_1868,plain,(
    ! [B_204,B_205] :
      ( m1_subset_1('#skF_1'('#skF_3'),B_204)
      | ~ r1_tarski(B_205,B_204)
      | ~ r1_tarski(u1_struct_0('#skF_3'),B_205) ) ),
    inference(resolution,[status(thm)],[c_1188,c_84])).

tff(c_2019,plain,(
    ! [B_211,A_212] :
      ( m1_subset_1('#skF_1'('#skF_3'),B_211)
      | ~ r1_tarski(u1_struct_0('#skF_3'),k1_tarski(A_212))
      | ~ r2_hidden(A_212,B_211) ) ),
    inference(resolution,[status(thm)],[c_32,c_1868])).

tff(c_2021,plain,(
    ! [B_211] :
      ( m1_subset_1('#skF_1'('#skF_3'),B_211)
      | ~ r1_tarski(u1_struct_0('#skF_3'),u1_struct_0('#skF_3'))
      | ~ r2_hidden('#skF_1'('#skF_3'),B_211) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1053,c_2019])).

tff(c_2026,plain,(
    ! [B_213] :
      ( m1_subset_1('#skF_1'('#skF_3'),B_213)
      | ~ r2_hidden('#skF_1'('#skF_3'),B_213) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1063,c_2021])).

tff(c_2044,plain,(
    ! [B_214] :
      ( m1_subset_1('#skF_1'('#skF_3'),B_214)
      | ~ r1_tarski(u1_struct_0('#skF_3'),B_214) ) ),
    inference(resolution,[status(thm)],[c_1099,c_2026])).

tff(c_2080,plain,(
    ! [A_215] :
      ( m1_subset_1('#skF_1'('#skF_3'),u1_struct_0(A_215))
      | ~ m1_pre_topc('#skF_3',A_215)
      | ~ l1_pre_topc(A_215) ) ),
    inference(resolution,[status(thm)],[c_122,c_2044])).

tff(c_261,plain,(
    ! [C_111,B_112,A_113] :
      ( g1_pre_topc(u1_struct_0(C_111),u1_pre_topc(C_111)) = g1_pre_topc(u1_struct_0(B_112),u1_pre_topc(B_112))
      | u1_struct_0(C_111) != u1_struct_0(B_112)
      | ~ m1_pre_topc(C_111,A_113)
      | ~ m1_pre_topc(B_112,A_113)
      | ~ l1_pre_topc(A_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_265,plain,(
    ! [B_112] :
      ( g1_pre_topc(u1_struct_0(B_112),u1_pre_topc(B_112)) = g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))
      | u1_struct_0(B_112) != u1_struct_0('#skF_3')
      | ~ m1_pre_topc(B_112,'#skF_2')
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_46,c_261])).

tff(c_270,plain,(
    ! [B_114] :
      ( g1_pre_topc(u1_struct_0(B_114),u1_pre_topc(B_114)) = g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))
      | u1_struct_0(B_114) != u1_struct_0('#skF_3')
      | ~ m1_pre_topc(B_114,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_265])).

tff(c_44,plain,(
    ! [C_47] :
      ( g1_pre_topc(u1_struct_0(k1_tex_2('#skF_2',C_47)),u1_pre_topc(k1_tex_2('#skF_2',C_47))) != g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))
      | ~ m1_subset_1(C_47,u1_struct_0('#skF_2')) ) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_283,plain,(
    ! [C_47] :
      ( ~ m1_subset_1(C_47,u1_struct_0('#skF_2'))
      | u1_struct_0(k1_tex_2('#skF_2',C_47)) != u1_struct_0('#skF_3')
      | ~ m1_pre_topc(k1_tex_2('#skF_2',C_47),'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_270,c_44])).

tff(c_2084,plain,
    ( u1_struct_0(k1_tex_2('#skF_2','#skF_1'('#skF_3'))) != u1_struct_0('#skF_3')
    | ~ m1_pre_topc(k1_tex_2('#skF_2','#skF_1'('#skF_3')),'#skF_2')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_2080,c_283])).

tff(c_2108,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_46,c_762,c_1430,c_2084])).

%------------------------------------------------------------------------------
