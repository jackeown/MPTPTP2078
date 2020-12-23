%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1868+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:35 EST 2020

% Result     : Theorem 12.84s
% Output     : CNFRefutation 12.99s
% Verified   : 
% Statistics : Number of formulae       :  131 (1754 expanded)
%              Number of leaves         :   45 ( 580 expanded)
%              Depth                    :   24
%              Number of atoms          :  241 (3597 expanded)
%              Number of equality atoms :   50 ( 652 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v2_tex_2 > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k9_subset_1 > k6_domain_1 > k3_xboole_0 > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_tarski > k1_struct_0 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

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

tff(f_147,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => v2_tex_2(k6_domain_1(u1_struct_0(A),B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_tex_2)).

tff(f_91,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => v3_pre_topc(k2_struct_0(A),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_tops_1)).

tff(f_85,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_103,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => v1_xboole_0(k1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_struct_0)).

tff(f_134,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_boole)).

tff(f_45,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_99,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_110,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_81,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_130,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_118,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_74,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => m1_subset_1(k2_struct_0(A),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_struct_0)).

tff(f_66,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tex_2)).

tff(f_126,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_zfmisc_1)).

tff(f_70,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => m1_subset_1(k1_struct_0(A),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_struct_0)).

tff(f_35,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_xboole_0(B)
           => v3_pre_topc(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_tops_1)).

tff(f_120,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_114,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k9_subset_1(A,C,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k9_subset_1)).

tff(c_62,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_60,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_30,plain,(
    ! [A_40] :
      ( v3_pre_topc(k2_struct_0(A_40),A_40)
      | ~ l1_pre_topc(A_40)
      | ~ v2_pre_topc(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_64,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_28,plain,(
    ! [A_39] :
      ( l1_struct_0(A_39)
      | ~ l1_pre_topc(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_76,plain,(
    ! [A_62] :
      ( v1_xboole_0(k1_struct_0(A_62))
      | ~ l1_struct_0(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_54,plain,(
    ! [A_55] :
      ( k1_xboole_0 = A_55
      | ~ v1_xboole_0(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_81,plain,(
    ! [A_63] :
      ( k1_struct_0(A_63) = k1_xboole_0
      | ~ l1_struct_0(A_63) ) ),
    inference(resolution,[status(thm)],[c_76,c_54])).

tff(c_86,plain,(
    ! [A_64] :
      ( k1_struct_0(A_64) = k1_xboole_0
      | ~ l1_pre_topc(A_64) ) ),
    inference(resolution,[status(thm)],[c_28,c_81])).

tff(c_90,plain,(
    k1_struct_0('#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_60,c_86])).

tff(c_34,plain,(
    ! [A_42] :
      ( v1_xboole_0(k1_struct_0(A_42))
      | ~ l1_struct_0(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_94,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ l1_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_34])).

tff(c_98,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_94])).

tff(c_106,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_98])).

tff(c_110,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_106])).

tff(c_112,plain,(
    l1_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_94])).

tff(c_123,plain,(
    ! [A_66] :
      ( u1_struct_0(A_66) = k2_struct_0(A_66)
      | ~ l1_struct_0(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_130,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_112,c_123])).

tff(c_219,plain,(
    ! [A_70] :
      ( ~ v1_xboole_0(u1_struct_0(A_70))
      | ~ l1_struct_0(A_70)
      | v2_struct_0(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_222,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_3'))
    | ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_130,c_219])).

tff(c_224,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_3'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_222])).

tff(c_225,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_224])).

tff(c_58,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_133,plain,(
    m1_subset_1('#skF_4',k2_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_58])).

tff(c_376,plain,(
    ! [A_88,B_89] :
      ( k6_domain_1(A_88,B_89) = k1_tarski(B_89)
      | ~ m1_subset_1(B_89,A_88)
      | v1_xboole_0(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_394,plain,
    ( k6_domain_1(k2_struct_0('#skF_3'),'#skF_4') = k1_tarski('#skF_4')
    | v1_xboole_0(k2_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_133,c_376])).

tff(c_402,plain,(
    k6_domain_1(k2_struct_0('#skF_3'),'#skF_4') = k1_tarski('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_225,c_394])).

tff(c_408,plain,(
    ! [A_90,B_91] :
      ( m1_subset_1(k6_domain_1(A_90,B_91),k1_zfmisc_1(A_90))
      | ~ m1_subset_1(B_91,A_90)
      | v1_xboole_0(A_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_417,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_3')))
    | ~ m1_subset_1('#skF_4',k2_struct_0('#skF_3'))
    | v1_xboole_0(k2_struct_0('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_402,c_408])).

tff(c_421,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_3')))
    | v1_xboole_0(k2_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_417])).

tff(c_422,plain,(
    m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_225,c_421])).

tff(c_50,plain,(
    ! [A_53,B_54] :
      ( r1_tarski(A_53,B_54)
      | ~ m1_subset_1(A_53,k1_zfmisc_1(B_54)) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_430,plain,(
    r1_tarski(k1_tarski('#skF_4'),k2_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_422,c_50])).

tff(c_40,plain,(
    ! [A_48,B_49] :
      ( k3_xboole_0(A_48,B_49) = A_48
      | ~ r1_tarski(A_48,B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_434,plain,(
    k3_xboole_0(k1_tarski('#skF_4'),k2_struct_0('#skF_3')) = k1_tarski('#skF_4') ),
    inference(resolution,[status(thm)],[c_430,c_40])).

tff(c_4,plain,(
    ! [B_5,A_4] : k3_xboole_0(B_5,A_4) = k3_xboole_0(A_4,B_5) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_300,plain,(
    ! [A_82] :
      ( m1_subset_1(k2_struct_0(A_82),k1_zfmisc_1(u1_struct_0(A_82)))
      | ~ l1_struct_0(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_306,plain,
    ( m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(k2_struct_0('#skF_3')))
    | ~ l1_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_130,c_300])).

tff(c_309,plain,(
    m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(k2_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_306])).

tff(c_56,plain,(
    ~ v2_tex_2(k6_domain_1(u1_struct_0('#skF_3'),'#skF_4'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_132,plain,(
    ~ v2_tex_2(k6_domain_1(k2_struct_0('#skF_3'),'#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_56])).

tff(c_403,plain,(
    ~ v2_tex_2(k1_tarski('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_402,c_132])).

tff(c_5037,plain,(
    ! [A_277,B_278] :
      ( r1_tarski('#skF_2'(A_277,B_278),B_278)
      | v2_tex_2(B_278,A_277)
      | ~ m1_subset_1(B_278,k1_zfmisc_1(u1_struct_0(A_277)))
      | ~ l1_pre_topc(A_277) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_5049,plain,(
    ! [B_278] :
      ( r1_tarski('#skF_2'('#skF_3',B_278),B_278)
      | v2_tex_2(B_278,'#skF_3')
      | ~ m1_subset_1(B_278,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_130,c_5037])).

tff(c_5385,plain,(
    ! [B_297] :
      ( r1_tarski('#skF_2'('#skF_3',B_297),B_297)
      | v2_tex_2(B_297,'#skF_3')
      | ~ m1_subset_1(B_297,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_5049])).

tff(c_5387,plain,
    ( r1_tarski('#skF_2'('#skF_3',k1_tarski('#skF_4')),k1_tarski('#skF_4'))
    | v2_tex_2(k1_tarski('#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_422,c_5385])).

tff(c_5400,plain,(
    r1_tarski('#skF_2'('#skF_3',k1_tarski('#skF_4')),k1_tarski('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_403,c_5387])).

tff(c_44,plain,(
    ! [B_52,A_51] :
      ( k1_tarski(B_52) = A_51
      | k1_xboole_0 = A_51
      | ~ r1_tarski(A_51,k1_tarski(B_52)) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_5441,plain,
    ( '#skF_2'('#skF_3',k1_tarski('#skF_4')) = k1_tarski('#skF_4')
    | '#skF_2'('#skF_3',k1_tarski('#skF_4')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_5400,c_44])).

tff(c_5469,plain,(
    '#skF_2'('#skF_3',k1_tarski('#skF_4')) = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_5441])).

tff(c_259,plain,(
    ! [A_79] :
      ( m1_subset_1(k1_struct_0(A_79),k1_zfmisc_1(u1_struct_0(A_79)))
      | ~ l1_struct_0(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_268,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_259])).

tff(c_273,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_130,c_268])).

tff(c_111,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_94])).

tff(c_4912,plain,(
    ! [B_270,A_271] :
      ( v3_pre_topc(B_270,A_271)
      | ~ v1_xboole_0(B_270)
      | ~ m1_subset_1(B_270,k1_zfmisc_1(u1_struct_0(A_271)))
      | ~ l1_pre_topc(A_271)
      | ~ v2_pre_topc(A_271) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_4929,plain,(
    ! [B_270] :
      ( v3_pre_topc(B_270,'#skF_3')
      | ~ v1_xboole_0(B_270)
      | ~ m1_subset_1(B_270,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_130,c_4912])).

tff(c_4965,plain,(
    ! [B_274] :
      ( v3_pre_topc(B_274,'#skF_3')
      | ~ v1_xboole_0(B_274)
      | ~ m1_subset_1(B_274,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_4929])).

tff(c_4978,plain,
    ( v3_pre_topc(k1_xboole_0,'#skF_3')
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_273,c_4965])).

tff(c_4990,plain,(
    v3_pre_topc(k1_xboole_0,'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_4978])).

tff(c_42,plain,(
    ! [A_50] : k3_xboole_0(A_50,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_435,plain,(
    ! [A_92,B_93,C_94] :
      ( k9_subset_1(A_92,B_93,C_94) = k3_xboole_0(B_93,C_94)
      | ~ m1_subset_1(C_94,k1_zfmisc_1(A_92)) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_445,plain,(
    ! [B_93] : k9_subset_1(k2_struct_0('#skF_3'),B_93,k1_xboole_0) = k3_xboole_0(B_93,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_273,c_435])).

tff(c_455,plain,(
    ! [B_93] : k9_subset_1(k2_struct_0('#skF_3'),B_93,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_445])).

tff(c_5483,plain,(
    ! [A_302,B_303,D_304] :
      ( k9_subset_1(u1_struct_0(A_302),B_303,D_304) != '#skF_2'(A_302,B_303)
      | ~ v3_pre_topc(D_304,A_302)
      | ~ m1_subset_1(D_304,k1_zfmisc_1(u1_struct_0(A_302)))
      | v2_tex_2(B_303,A_302)
      | ~ m1_subset_1(B_303,k1_zfmisc_1(u1_struct_0(A_302)))
      | ~ l1_pre_topc(A_302) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_5489,plain,(
    ! [B_303,D_304] :
      ( k9_subset_1(k2_struct_0('#skF_3'),B_303,D_304) != '#skF_2'('#skF_3',B_303)
      | ~ v3_pre_topc(D_304,'#skF_3')
      | ~ m1_subset_1(D_304,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_tex_2(B_303,'#skF_3')
      | ~ m1_subset_1(B_303,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_130,c_5483])).

tff(c_14864,plain,(
    ! [B_609,D_610] :
      ( k9_subset_1(k2_struct_0('#skF_3'),B_609,D_610) != '#skF_2'('#skF_3',B_609)
      | ~ v3_pre_topc(D_610,'#skF_3')
      | ~ m1_subset_1(D_610,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | v2_tex_2(B_609,'#skF_3')
      | ~ m1_subset_1(B_609,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_130,c_130,c_5489])).

tff(c_14925,plain,(
    ! [B_93] :
      ( '#skF_2'('#skF_3',B_93) != k1_xboole_0
      | ~ v3_pre_topc(k1_xboole_0,'#skF_3')
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | v2_tex_2(B_93,'#skF_3')
      | ~ m1_subset_1(B_93,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_455,c_14864])).

tff(c_15002,plain,(
    ! [B_614] :
      ( '#skF_2'('#skF_3',B_614) != k1_xboole_0
      | v2_tex_2(B_614,'#skF_3')
      | ~ m1_subset_1(B_614,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_273,c_4990,c_14925])).

tff(c_15011,plain,
    ( '#skF_2'('#skF_3',k1_tarski('#skF_4')) != k1_xboole_0
    | v2_tex_2(k1_tarski('#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_422,c_15002])).

tff(c_15030,plain,(
    v2_tex_2(k1_tarski('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5469,c_15011])).

tff(c_15032,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_403,c_15030])).

tff(c_15033,plain,(
    '#skF_2'('#skF_3',k1_tarski('#skF_4')) = k1_tarski('#skF_4') ),
    inference(splitRight,[status(thm)],[c_5441])).

tff(c_450,plain,(
    ! [B_93] : k9_subset_1(k2_struct_0('#skF_3'),B_93,k1_tarski('#skF_4')) = k3_xboole_0(B_93,k1_tarski('#skF_4')) ),
    inference(resolution,[status(thm)],[c_422,c_435])).

tff(c_549,plain,(
    ! [A_107,C_108,B_109] :
      ( k9_subset_1(A_107,C_108,B_109) = k9_subset_1(A_107,B_109,C_108)
      | ~ m1_subset_1(C_108,k1_zfmisc_1(A_107)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_551,plain,(
    ! [B_109] : k9_subset_1(k2_struct_0('#skF_3'),k1_tarski('#skF_4'),B_109) = k9_subset_1(k2_struct_0('#skF_3'),B_109,k1_tarski('#skF_4')) ),
    inference(resolution,[status(thm)],[c_422,c_549])).

tff(c_565,plain,(
    ! [B_109] : k9_subset_1(k2_struct_0('#skF_3'),k1_tarski('#skF_4'),B_109) = k3_xboole_0(B_109,k1_tarski('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_450,c_551])).

tff(c_15336,plain,(
    ! [A_627,B_628,D_629] :
      ( k9_subset_1(u1_struct_0(A_627),B_628,D_629) != '#skF_2'(A_627,B_628)
      | ~ v3_pre_topc(D_629,A_627)
      | ~ m1_subset_1(D_629,k1_zfmisc_1(u1_struct_0(A_627)))
      | v2_tex_2(B_628,A_627)
      | ~ m1_subset_1(B_628,k1_zfmisc_1(u1_struct_0(A_627)))
      | ~ l1_pre_topc(A_627) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_15346,plain,(
    ! [B_628,D_629] :
      ( k9_subset_1(k2_struct_0('#skF_3'),B_628,D_629) != '#skF_2'('#skF_3',B_628)
      | ~ v3_pre_topc(D_629,'#skF_3')
      | ~ m1_subset_1(D_629,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_tex_2(B_628,'#skF_3')
      | ~ m1_subset_1(B_628,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_130,c_15336])).

tff(c_24579,plain,(
    ! [B_927,D_928] :
      ( k9_subset_1(k2_struct_0('#skF_3'),B_927,D_928) != '#skF_2'('#skF_3',B_927)
      | ~ v3_pre_topc(D_928,'#skF_3')
      | ~ m1_subset_1(D_928,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | v2_tex_2(B_927,'#skF_3')
      | ~ m1_subset_1(B_927,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_130,c_130,c_15346])).

tff(c_24632,plain,(
    ! [B_109] :
      ( k3_xboole_0(B_109,k1_tarski('#skF_4')) != '#skF_2'('#skF_3',k1_tarski('#skF_4'))
      | ~ v3_pre_topc(B_109,'#skF_3')
      | ~ m1_subset_1(B_109,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | v2_tex_2(k1_tarski('#skF_4'),'#skF_3')
      | ~ m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_565,c_24579])).

tff(c_24654,plain,(
    ! [B_109] :
      ( k3_xboole_0(B_109,k1_tarski('#skF_4')) != k1_tarski('#skF_4')
      | ~ v3_pre_topc(B_109,'#skF_3')
      | ~ m1_subset_1(B_109,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | v2_tex_2(k1_tarski('#skF_4'),'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_422,c_15033,c_24632])).

tff(c_24755,plain,(
    ! [B_935] :
      ( k3_xboole_0(B_935,k1_tarski('#skF_4')) != k1_tarski('#skF_4')
      | ~ v3_pre_topc(B_935,'#skF_3')
      | ~ m1_subset_1(B_935,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_403,c_24654])).

tff(c_24771,plain,
    ( k3_xboole_0(k2_struct_0('#skF_3'),k1_tarski('#skF_4')) != k1_tarski('#skF_4')
    | ~ v3_pre_topc(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_309,c_24755])).

tff(c_24789,plain,(
    ~ v3_pre_topc(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_434,c_4,c_24771])).

tff(c_24803,plain,
    ( ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_24789])).

tff(c_24807,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_24803])).

%------------------------------------------------------------------------------
