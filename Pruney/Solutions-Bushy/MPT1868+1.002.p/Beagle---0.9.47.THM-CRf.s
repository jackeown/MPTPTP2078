%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1868+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:35 EST 2020

% Result     : Theorem 8.20s
% Output     : CNFRefutation 8.59s
% Verified   : 
% Statistics : Number of formulae       :  137 (1175 expanded)
%              Number of leaves         :   45 ( 403 expanded)
%              Depth                    :   20
%              Number of atoms          :  242 (2614 expanded)
%              Number of equality atoms :   54 ( 425 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v2_tex_2 > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k9_subset_1 > k6_domain_1 > k3_xboole_0 > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_tarski > k1_struct_0 > o_0_0_xboole_0 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k1_struct_0,type,(
    k1_struct_0: $i > $i )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_148,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => v2_tex_2(k6_domain_1(u1_struct_0(A),B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_tex_2)).

tff(f_94,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => v3_pre_topc(k2_struct_0(A),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_tops_1)).

tff(f_87,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_43,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_102,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_113,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_131,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_121,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_72,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => m1_subset_1(k2_struct_0(A),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_struct_0)).

tff(f_117,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k9_subset_1(A,C,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k9_subset_1)).

tff(f_88,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

tff(f_135,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_boole)).

tff(f_106,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => v1_xboole_0(k1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_struct_0)).

tff(f_68,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => m1_subset_1(k1_struct_0(A),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_struct_0)).

tff(f_35,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_xboole_0(B)
           => v3_pre_topc(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_tops_1)).

tff(f_127,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_zfmisc_1)).

tff(f_64,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tex_2(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ~ ( r1_tarski(C,B)
                    & ! [D] :
                        ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                       => ~ ( v3_pre_topc(D,A)
                            & k9_subset_1(u1_struct_0(A),B,D) = C ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tex_2)).

tff(c_62,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_60,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_32,plain,(
    ! [A_41] :
      ( v3_pre_topc(k2_struct_0(A_41),A_41)
      | ~ l1_pre_topc(A_41)
      | ~ v2_pre_topc(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_28,plain,(
    ! [A_40] :
      ( l1_struct_0(A_40)
      | ~ l1_pre_topc(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_64,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_98,plain,(
    ! [A_64] :
      ( u1_struct_0(A_64) = k2_struct_0(A_64)
      | ~ l1_struct_0(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_111,plain,(
    ! [A_65] :
      ( u1_struct_0(A_65) = k2_struct_0(A_65)
      | ~ l1_pre_topc(A_65) ) ),
    inference(resolution,[status(thm)],[c_28,c_98])).

tff(c_115,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_111])).

tff(c_123,plain,(
    ! [A_68] :
      ( ~ v1_xboole_0(u1_struct_0(A_68))
      | ~ l1_struct_0(A_68)
      | v2_struct_0(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_126,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_3'))
    | ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_115,c_123])).

tff(c_127,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_3'))
    | ~ l1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_126])).

tff(c_128,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_127])).

tff(c_131,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_128])).

tff(c_135,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_131])).

tff(c_136,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_127])).

tff(c_58,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_117,plain,(
    m1_subset_1('#skF_4',k2_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_115,c_58])).

tff(c_284,plain,(
    ! [A_83,B_84] :
      ( k6_domain_1(A_83,B_84) = k1_tarski(B_84)
      | ~ m1_subset_1(B_84,A_83)
      | v1_xboole_0(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_302,plain,
    ( k6_domain_1(k2_struct_0('#skF_3'),'#skF_4') = k1_tarski('#skF_4')
    | v1_xboole_0(k2_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_117,c_284])).

tff(c_310,plain,(
    k6_domain_1(k2_struct_0('#skF_3'),'#skF_4') = k1_tarski('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_136,c_302])).

tff(c_8414,plain,(
    ! [A_338,B_339] :
      ( m1_subset_1(k6_domain_1(A_338,B_339),k1_zfmisc_1(A_338))
      | ~ m1_subset_1(B_339,A_338)
      | v1_xboole_0(A_338) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_8429,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_3')))
    | ~ m1_subset_1('#skF_4',k2_struct_0('#skF_3'))
    | v1_xboole_0(k2_struct_0('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_310,c_8414])).

tff(c_8439,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_3')))
    | v1_xboole_0(k2_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_8429])).

tff(c_8440,plain,(
    m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_136,c_8439])).

tff(c_50,plain,(
    ! [A_53,B_54] :
      ( r1_tarski(A_53,B_54)
      | ~ m1_subset_1(A_53,k1_zfmisc_1(B_54)) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_8450,plain,(
    r1_tarski(k1_tarski('#skF_4'),k2_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_8440,c_50])).

tff(c_42,plain,(
    ! [A_49,B_50] :
      ( k3_xboole_0(A_49,B_50) = A_49
      | ~ r1_tarski(A_49,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_8454,plain,(
    k3_xboole_0(k1_tarski('#skF_4'),k2_struct_0('#skF_3')) = k1_tarski('#skF_4') ),
    inference(resolution,[status(thm)],[c_8450,c_42])).

tff(c_137,plain,(
    l1_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_127])).

tff(c_202,plain,(
    ! [A_76] :
      ( m1_subset_1(k2_struct_0(A_76),k1_zfmisc_1(u1_struct_0(A_76)))
      | ~ l1_struct_0(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_208,plain,
    ( m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(k2_struct_0('#skF_3')))
    | ~ l1_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_115,c_202])).

tff(c_211,plain,(
    m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(k2_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_208])).

tff(c_8467,plain,(
    ! [A_340,B_341,C_342] :
      ( k9_subset_1(A_340,B_341,C_342) = k3_xboole_0(B_341,C_342)
      | ~ m1_subset_1(C_342,k1_zfmisc_1(A_340)) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_8490,plain,(
    ! [B_341] : k9_subset_1(k2_struct_0('#skF_3'),B_341,k2_struct_0('#skF_3')) = k3_xboole_0(B_341,k2_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_211,c_8467])).

tff(c_8610,plain,(
    ! [A_349,C_350,B_351] :
      ( k9_subset_1(A_349,C_350,B_351) = k9_subset_1(A_349,B_351,C_350)
      | ~ m1_subset_1(C_350,k1_zfmisc_1(A_349)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_8626,plain,(
    ! [B_351] : k9_subset_1(k2_struct_0('#skF_3'),k2_struct_0('#skF_3'),B_351) = k9_subset_1(k2_struct_0('#skF_3'),B_351,k2_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_211,c_8610])).

tff(c_9167,plain,(
    ! [B_376] : k9_subset_1(k2_struct_0('#skF_3'),k2_struct_0('#skF_3'),B_376) = k3_xboole_0(B_376,k2_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8490,c_8626])).

tff(c_8487,plain,(
    ! [B_341] : k9_subset_1(k2_struct_0('#skF_3'),B_341,k1_tarski('#skF_4')) = k3_xboole_0(B_341,k1_tarski('#skF_4')) ),
    inference(resolution,[status(thm)],[c_8440,c_8467])).

tff(c_9174,plain,(
    k3_xboole_0(k2_struct_0('#skF_3'),k1_tarski('#skF_4')) = k3_xboole_0(k1_tarski('#skF_4'),k2_struct_0('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_9167,c_8487])).

tff(c_9205,plain,(
    k3_xboole_0(k2_struct_0('#skF_3'),k1_tarski('#skF_4')) = k1_tarski('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8454,c_9174])).

tff(c_56,plain,(
    ~ v2_tex_2(k6_domain_1(u1_struct_0('#skF_3'),'#skF_4'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_116,plain,(
    ~ v2_tex_2(k6_domain_1(k2_struct_0('#skF_3'),'#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_115,c_56])).

tff(c_311,plain,(
    ~ v2_tex_2(k1_tarski('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_310,c_116])).

tff(c_30,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_66,plain,(
    ! [A_58] :
      ( k1_xboole_0 = A_58
      | ~ v1_xboole_0(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_70,plain,(
    o_0_0_xboole_0 = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_30,c_66])).

tff(c_71,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_30])).

tff(c_83,plain,(
    ! [A_61] :
      ( v1_xboole_0(k1_struct_0(A_61))
      | ~ l1_struct_0(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_54,plain,(
    ! [A_55] :
      ( k1_xboole_0 = A_55
      | ~ v1_xboole_0(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_88,plain,(
    ! [A_62] :
      ( k1_struct_0(A_62) = k1_xboole_0
      | ~ l1_struct_0(A_62) ) ),
    inference(resolution,[status(thm)],[c_83,c_54])).

tff(c_93,plain,(
    ! [A_63] :
      ( k1_struct_0(A_63) = k1_xboole_0
      | ~ l1_pre_topc(A_63) ) ),
    inference(resolution,[status(thm)],[c_28,c_88])).

tff(c_97,plain,(
    k1_struct_0('#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_60,c_93])).

tff(c_178,plain,(
    ! [A_75] :
      ( m1_subset_1(k1_struct_0(A_75),k1_zfmisc_1(u1_struct_0(A_75)))
      | ~ l1_struct_0(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_184,plain,
    ( m1_subset_1(k1_struct_0('#skF_3'),k1_zfmisc_1(k2_struct_0('#skF_3')))
    | ~ l1_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_115,c_178])).

tff(c_190,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_97,c_184])).

tff(c_8782,plain,(
    ! [B_356,A_357] :
      ( v3_pre_topc(B_356,A_357)
      | ~ v1_xboole_0(B_356)
      | ~ m1_subset_1(B_356,k1_zfmisc_1(u1_struct_0(A_357)))
      | ~ l1_pre_topc(A_357)
      | ~ v2_pre_topc(A_357) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_8803,plain,(
    ! [B_356] :
      ( v3_pre_topc(B_356,'#skF_3')
      | ~ v1_xboole_0(B_356)
      | ~ m1_subset_1(B_356,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_115,c_8782])).

tff(c_8839,plain,(
    ! [B_358] :
      ( v3_pre_topc(B_358,'#skF_3')
      | ~ v1_xboole_0(B_358)
      | ~ m1_subset_1(B_358,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_8803])).

tff(c_8865,plain,
    ( v3_pre_topc(k1_xboole_0,'#skF_3')
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_190,c_8839])).

tff(c_8881,plain,(
    v3_pre_topc(k1_xboole_0,'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_8865])).

tff(c_48,plain,(
    ! [B_52] : r1_tarski(k1_xboole_0,k1_tarski(B_52)) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_138,plain,(
    ! [A_69,B_70] :
      ( k3_xboole_0(A_69,B_70) = A_69
      | ~ r1_tarski(A_69,B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_146,plain,(
    ! [B_52] : k3_xboole_0(k1_xboole_0,k1_tarski(B_52)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_48,c_138])).

tff(c_8939,plain,(
    ! [A_361,B_362] :
      ( r1_tarski('#skF_2'(A_361,B_362),B_362)
      | v2_tex_2(B_362,A_361)
      | ~ m1_subset_1(B_362,k1_zfmisc_1(u1_struct_0(A_361)))
      | ~ l1_pre_topc(A_361) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_8954,plain,(
    ! [B_362] :
      ( r1_tarski('#skF_2'('#skF_3',B_362),B_362)
      | v2_tex_2(B_362,'#skF_3')
      | ~ m1_subset_1(B_362,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_115,c_8939])).

tff(c_9019,plain,(
    ! [B_367] :
      ( r1_tarski('#skF_2'('#skF_3',B_367),B_367)
      | v2_tex_2(B_367,'#skF_3')
      | ~ m1_subset_1(B_367,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_8954])).

tff(c_9027,plain,
    ( r1_tarski('#skF_2'('#skF_3',k1_tarski('#skF_4')),k1_tarski('#skF_4'))
    | v2_tex_2(k1_tarski('#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_8440,c_9019])).

tff(c_9046,plain,(
    r1_tarski('#skF_2'('#skF_3',k1_tarski('#skF_4')),k1_tarski('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_311,c_9027])).

tff(c_44,plain,(
    ! [B_52,A_51] :
      ( k1_tarski(B_52) = A_51
      | k1_xboole_0 = A_51
      | ~ r1_tarski(A_51,k1_tarski(B_52)) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_9063,plain,
    ( '#skF_2'('#skF_3',k1_tarski('#skF_4')) = k1_tarski('#skF_4')
    | '#skF_2'('#skF_3',k1_tarski('#skF_4')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_9046,c_44])).

tff(c_9598,plain,(
    '#skF_2'('#skF_3',k1_tarski('#skF_4')) = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_9063])).

tff(c_52,plain,(
    ! [A_53,B_54] :
      ( m1_subset_1(A_53,k1_zfmisc_1(B_54))
      | ~ r1_tarski(A_53,B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_9257,plain,(
    ! [B_378,B_379,A_380] :
      ( k9_subset_1(B_378,B_379,A_380) = k9_subset_1(B_378,A_380,B_379)
      | ~ r1_tarski(A_380,B_378) ) ),
    inference(resolution,[status(thm)],[c_52,c_8610])).

tff(c_9275,plain,(
    ! [B_379] : k9_subset_1(k2_struct_0('#skF_3'),k1_tarski('#skF_4'),B_379) = k9_subset_1(k2_struct_0('#skF_3'),B_379,k1_tarski('#skF_4')) ),
    inference(resolution,[status(thm)],[c_8450,c_9257])).

tff(c_9299,plain,(
    ! [B_379] : k9_subset_1(k2_struct_0('#skF_3'),k1_tarski('#skF_4'),B_379) = k3_xboole_0(B_379,k1_tarski('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8487,c_9275])).

tff(c_9529,plain,(
    ! [A_395,B_396,D_397] :
      ( k9_subset_1(u1_struct_0(A_395),B_396,D_397) != '#skF_2'(A_395,B_396)
      | ~ v3_pre_topc(D_397,A_395)
      | ~ m1_subset_1(D_397,k1_zfmisc_1(u1_struct_0(A_395)))
      | v2_tex_2(B_396,A_395)
      | ~ m1_subset_1(B_396,k1_zfmisc_1(u1_struct_0(A_395)))
      | ~ l1_pre_topc(A_395) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_9531,plain,(
    ! [B_396,D_397] :
      ( k9_subset_1(k2_struct_0('#skF_3'),B_396,D_397) != '#skF_2'('#skF_3',B_396)
      | ~ v3_pre_topc(D_397,'#skF_3')
      | ~ m1_subset_1(D_397,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_tex_2(B_396,'#skF_3')
      | ~ m1_subset_1(B_396,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_115,c_9529])).

tff(c_10097,plain,(
    ! [B_423,D_424] :
      ( k9_subset_1(k2_struct_0('#skF_3'),B_423,D_424) != '#skF_2'('#skF_3',B_423)
      | ~ v3_pre_topc(D_424,'#skF_3')
      | ~ m1_subset_1(D_424,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | v2_tex_2(B_423,'#skF_3')
      | ~ m1_subset_1(B_423,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_115,c_115,c_9531])).

tff(c_10099,plain,(
    ! [B_379] :
      ( k3_xboole_0(B_379,k1_tarski('#skF_4')) != '#skF_2'('#skF_3',k1_tarski('#skF_4'))
      | ~ v3_pre_topc(B_379,'#skF_3')
      | ~ m1_subset_1(B_379,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | v2_tex_2(k1_tarski('#skF_4'),'#skF_3')
      | ~ m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9299,c_10097])).

tff(c_10111,plain,(
    ! [B_379] :
      ( k3_xboole_0(B_379,k1_tarski('#skF_4')) != k1_xboole_0
      | ~ v3_pre_topc(B_379,'#skF_3')
      | ~ m1_subset_1(B_379,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | v2_tex_2(k1_tarski('#skF_4'),'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8440,c_9598,c_10099])).

tff(c_10382,plain,(
    ! [B_433] :
      ( k3_xboole_0(B_433,k1_tarski('#skF_4')) != k1_xboole_0
      | ~ v3_pre_topc(B_433,'#skF_3')
      | ~ m1_subset_1(B_433,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_311,c_10111])).

tff(c_10411,plain,
    ( k3_xboole_0(k1_xboole_0,k1_tarski('#skF_4')) != k1_xboole_0
    | ~ v3_pre_topc(k1_xboole_0,'#skF_3') ),
    inference(resolution,[status(thm)],[c_190,c_10382])).

tff(c_10431,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8881,c_146,c_10411])).

tff(c_10432,plain,(
    '#skF_2'('#skF_3',k1_tarski('#skF_4')) = k1_tarski('#skF_4') ),
    inference(splitRight,[status(thm)],[c_9063])).

tff(c_10932,plain,(
    ! [B_458,D_459] :
      ( k9_subset_1(k2_struct_0('#skF_3'),B_458,D_459) != '#skF_2'('#skF_3',B_458)
      | ~ v3_pre_topc(D_459,'#skF_3')
      | ~ m1_subset_1(D_459,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | v2_tex_2(B_458,'#skF_3')
      | ~ m1_subset_1(B_458,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_115,c_115,c_9531])).

tff(c_10934,plain,(
    ! [B_379] :
      ( k3_xboole_0(B_379,k1_tarski('#skF_4')) != '#skF_2'('#skF_3',k1_tarski('#skF_4'))
      | ~ v3_pre_topc(B_379,'#skF_3')
      | ~ m1_subset_1(B_379,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | v2_tex_2(k1_tarski('#skF_4'),'#skF_3')
      | ~ m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9299,c_10932])).

tff(c_10946,plain,(
    ! [B_379] :
      ( k3_xboole_0(B_379,k1_tarski('#skF_4')) != k1_tarski('#skF_4')
      | ~ v3_pre_topc(B_379,'#skF_3')
      | ~ m1_subset_1(B_379,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | v2_tex_2(k1_tarski('#skF_4'),'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8440,c_10432,c_10934])).

tff(c_11216,plain,(
    ! [B_468] :
      ( k3_xboole_0(B_468,k1_tarski('#skF_4')) != k1_tarski('#skF_4')
      | ~ v3_pre_topc(B_468,'#skF_3')
      | ~ m1_subset_1(B_468,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_311,c_10946])).

tff(c_11242,plain,
    ( k3_xboole_0(k2_struct_0('#skF_3'),k1_tarski('#skF_4')) != k1_tarski('#skF_4')
    | ~ v3_pre_topc(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_211,c_11216])).

tff(c_11263,plain,(
    ~ v3_pre_topc(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9205,c_11242])).

tff(c_11270,plain,
    ( ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_11263])).

tff(c_11274,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_11270])).

%------------------------------------------------------------------------------
