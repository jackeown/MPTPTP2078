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
% DateTime   : Thu Dec  3 10:24:17 EST 2020

% Result     : Theorem 2.94s
% Output     : CNFRefutation 3.07s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 199 expanded)
%              Number of leaves         :   37 (  85 expanded)
%              Depth                    :   12
%              Number of atoms          :  190 ( 544 expanded)
%              Number of equality atoms :    9 (  32 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m2_connsp_2 > m1_connsp_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k6_domain_1 > k2_tarski > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(m1_connsp_2,type,(
    m1_connsp_2: ( $i * $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m2_connsp_2,type,(
    m2_connsp_2: ( $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_145,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( m2_connsp_2(C,A,k6_domain_1(u1_struct_0(A),B))
                <=> m1_connsp_2(C,A,B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_connsp_2)).

tff(f_88,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( m1_connsp_2(C,A,B)
              <=> r2_hidden(B,k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_connsp_2)).

tff(f_49,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_71,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_57,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_64,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_27,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_102,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( m2_connsp_2(C,A,B)
              <=> r1_tarski(B,k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_connsp_2)).

tff(c_50,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_44,plain,(
    m1_subset_1('#skF_2',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_52,plain,
    ( ~ m1_connsp_2('#skF_3','#skF_1','#skF_2')
    | ~ m2_connsp_2('#skF_3','#skF_1',k6_domain_1(u1_struct_0('#skF_1'),'#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_79,plain,(
    ~ m2_connsp_2('#skF_3','#skF_1',k6_domain_1(u1_struct_0('#skF_1'),'#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_58,plain,
    ( m2_connsp_2('#skF_3','#skF_1',k6_domain_1(u1_struct_0('#skF_1'),'#skF_2'))
    | m1_connsp_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_123,plain,(
    m1_connsp_2('#skF_3','#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_79,c_58])).

tff(c_48,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_46,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_42,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_299,plain,(
    ! [B_128,A_129,C_130] :
      ( r2_hidden(B_128,k1_tops_1(A_129,C_130))
      | ~ m1_connsp_2(C_130,A_129,B_128)
      | ~ m1_subset_1(C_130,k1_zfmisc_1(u1_struct_0(A_129)))
      | ~ m1_subset_1(B_128,u1_struct_0(A_129))
      | ~ l1_pre_topc(A_129)
      | ~ v2_pre_topc(A_129)
      | v2_struct_0(A_129) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_306,plain,(
    ! [B_128] :
      ( r2_hidden(B_128,k1_tops_1('#skF_1','#skF_3'))
      | ~ m1_connsp_2('#skF_3','#skF_1',B_128)
      | ~ m1_subset_1(B_128,u1_struct_0('#skF_1'))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_42,c_299])).

tff(c_314,plain,(
    ! [B_128] :
      ( r2_hidden(B_128,k1_tops_1('#skF_1','#skF_3'))
      | ~ m1_connsp_2('#skF_3','#skF_1',B_128)
      | ~ m1_subset_1(B_128,u1_struct_0('#skF_1'))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_306])).

tff(c_315,plain,(
    ! [B_128] :
      ( r2_hidden(B_128,k1_tops_1('#skF_1','#skF_3'))
      | ~ m1_connsp_2('#skF_3','#skF_1',B_128)
      | ~ m1_subset_1(B_128,u1_struct_0('#skF_1')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_314])).

tff(c_22,plain,(
    ! [A_32] :
      ( l1_struct_0(A_32)
      | ~ l1_pre_topc(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_98,plain,(
    ! [A_80,B_81] :
      ( k6_domain_1(A_80,B_81) = k1_tarski(B_81)
      | ~ m1_subset_1(B_81,A_80)
      | v1_xboole_0(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_106,plain,
    ( k6_domain_1(u1_struct_0('#skF_1'),'#skF_2') = k1_tarski('#skF_2')
    | v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_44,c_98])).

tff(c_107,plain,(
    v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_106])).

tff(c_24,plain,(
    ! [A_33] :
      ( ~ v1_xboole_0(u1_struct_0(A_33))
      | ~ l1_struct_0(A_33)
      | v2_struct_0(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_110,plain,
    ( ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_107,c_24])).

tff(c_113,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_110])).

tff(c_116,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_113])).

tff(c_120,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_116])).

tff(c_121,plain,(
    k6_domain_1(u1_struct_0('#skF_1'),'#skF_2') = k1_tarski('#skF_2') ),
    inference(splitRight,[status(thm)],[c_106])).

tff(c_124,plain,(
    ~ m2_connsp_2('#skF_3','#skF_1',k1_tarski('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_79])).

tff(c_122,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_106])).

tff(c_146,plain,(
    ! [A_87,B_88] :
      ( m1_subset_1(k6_domain_1(A_87,B_88),k1_zfmisc_1(A_87))
      | ~ m1_subset_1(B_88,A_87)
      | v1_xboole_0(A_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_152,plain,
    ( m1_subset_1(k1_tarski('#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1'))
    | v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_121,c_146])).

tff(c_155,plain,
    ( m1_subset_1(k1_tarski('#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_152])).

tff(c_156,plain,(
    m1_subset_1(k1_tarski('#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_122,c_155])).

tff(c_2,plain,(
    ! [A_1] : k2_tarski(A_1,A_1) = k1_tarski(A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_129,plain,(
    ! [A_82,B_83,C_84] :
      ( r1_tarski(k2_tarski(A_82,B_83),C_84)
      | ~ r2_hidden(B_83,C_84)
      | ~ r2_hidden(A_82,C_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_138,plain,(
    ! [A_1,C_84] :
      ( r1_tarski(k1_tarski(A_1),C_84)
      | ~ r2_hidden(A_1,C_84)
      | ~ r2_hidden(A_1,C_84) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_129])).

tff(c_231,plain,(
    ! [C_119,A_120,B_121] :
      ( m2_connsp_2(C_119,A_120,B_121)
      | ~ r1_tarski(B_121,k1_tops_1(A_120,C_119))
      | ~ m1_subset_1(C_119,k1_zfmisc_1(u1_struct_0(A_120)))
      | ~ m1_subset_1(B_121,k1_zfmisc_1(u1_struct_0(A_120)))
      | ~ l1_pre_topc(A_120)
      | ~ v2_pre_topc(A_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_352,plain,(
    ! [C_141,A_142,A_143] :
      ( m2_connsp_2(C_141,A_142,k1_tarski(A_143))
      | ~ m1_subset_1(C_141,k1_zfmisc_1(u1_struct_0(A_142)))
      | ~ m1_subset_1(k1_tarski(A_143),k1_zfmisc_1(u1_struct_0(A_142)))
      | ~ l1_pre_topc(A_142)
      | ~ v2_pre_topc(A_142)
      | ~ r2_hidden(A_143,k1_tops_1(A_142,C_141)) ) ),
    inference(resolution,[status(thm)],[c_138,c_231])).

tff(c_359,plain,(
    ! [A_143] :
      ( m2_connsp_2('#skF_3','#skF_1',k1_tarski(A_143))
      | ~ m1_subset_1(k1_tarski(A_143),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | ~ r2_hidden(A_143,k1_tops_1('#skF_1','#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_42,c_352])).

tff(c_367,plain,(
    ! [A_144] :
      ( m2_connsp_2('#skF_3','#skF_1',k1_tarski(A_144))
      | ~ m1_subset_1(k1_tarski(A_144),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ r2_hidden(A_144,k1_tops_1('#skF_1','#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_359])).

tff(c_370,plain,
    ( m2_connsp_2('#skF_3','#skF_1',k1_tarski('#skF_2'))
    | ~ r2_hidden('#skF_2',k1_tops_1('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_156,c_367])).

tff(c_373,plain,(
    ~ r2_hidden('#skF_2',k1_tops_1('#skF_1','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_124,c_370])).

tff(c_401,plain,
    ( ~ m1_connsp_2('#skF_3','#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_315,c_373])).

tff(c_405,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_123,c_401])).

tff(c_406,plain,(
    ~ m1_connsp_2('#skF_3','#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_428,plain,(
    ! [A_159,B_160] :
      ( k6_domain_1(A_159,B_160) = k1_tarski(B_160)
      | ~ m1_subset_1(B_160,A_159)
      | v1_xboole_0(A_159) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_436,plain,
    ( k6_domain_1(u1_struct_0('#skF_1'),'#skF_2') = k1_tarski('#skF_2')
    | v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_44,c_428])).

tff(c_442,plain,(
    v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_436])).

tff(c_445,plain,
    ( ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_442,c_24])).

tff(c_448,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_445])).

tff(c_451,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_448])).

tff(c_455,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_451])).

tff(c_456,plain,(
    k6_domain_1(u1_struct_0('#skF_1'),'#skF_2') = k1_tarski('#skF_2') ),
    inference(splitRight,[status(thm)],[c_436])).

tff(c_407,plain,(
    m2_connsp_2('#skF_3','#skF_1',k6_domain_1(u1_struct_0('#skF_1'),'#skF_2')) ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_459,plain,(
    m2_connsp_2('#skF_3','#skF_1',k1_tarski('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_456,c_407])).

tff(c_457,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_436])).

tff(c_26,plain,(
    ! [A_34,B_35] :
      ( m1_subset_1(k6_domain_1(A_34,B_35),k1_zfmisc_1(A_34))
      | ~ m1_subset_1(B_35,A_34)
      | v1_xboole_0(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_463,plain,
    ( m1_subset_1(k1_tarski('#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1'))
    | v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_456,c_26])).

tff(c_467,plain,
    ( m1_subset_1(k1_tarski('#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_463])).

tff(c_468,plain,(
    m1_subset_1(k1_tarski('#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_457,c_467])).

tff(c_568,plain,(
    ! [B_201,A_202,C_203] :
      ( r1_tarski(B_201,k1_tops_1(A_202,C_203))
      | ~ m2_connsp_2(C_203,A_202,B_201)
      | ~ m1_subset_1(C_203,k1_zfmisc_1(u1_struct_0(A_202)))
      | ~ m1_subset_1(B_201,k1_zfmisc_1(u1_struct_0(A_202)))
      | ~ l1_pre_topc(A_202)
      | ~ v2_pre_topc(A_202) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_575,plain,(
    ! [B_201] :
      ( r1_tarski(B_201,k1_tops_1('#skF_1','#skF_3'))
      | ~ m2_connsp_2('#skF_3','#skF_1',B_201)
      | ~ m1_subset_1(B_201,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_42,c_568])).

tff(c_583,plain,(
    ! [B_204] :
      ( r1_tarski(B_204,k1_tops_1('#skF_1','#skF_3'))
      | ~ m2_connsp_2('#skF_3','#skF_1',B_204)
      | ~ m1_subset_1(B_204,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_575])).

tff(c_586,plain,
    ( r1_tarski(k1_tarski('#skF_2'),k1_tops_1('#skF_1','#skF_3'))
    | ~ m2_connsp_2('#skF_3','#skF_1',k1_tarski('#skF_2')) ),
    inference(resolution,[status(thm)],[c_468,c_583])).

tff(c_596,plain,(
    r1_tarski(k1_tarski('#skF_2'),k1_tops_1('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_459,c_586])).

tff(c_410,plain,(
    ! [A_148,C_149,B_150] :
      ( r2_hidden(A_148,C_149)
      | ~ r1_tarski(k2_tarski(A_148,B_150),C_149) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_413,plain,(
    ! [A_1,C_149] :
      ( r2_hidden(A_1,C_149)
      | ~ r1_tarski(k1_tarski(A_1),C_149) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_410])).

tff(c_609,plain,(
    r2_hidden('#skF_2',k1_tops_1('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_596,c_413])).

tff(c_678,plain,(
    ! [C_217,A_218,B_219] :
      ( m1_connsp_2(C_217,A_218,B_219)
      | ~ r2_hidden(B_219,k1_tops_1(A_218,C_217))
      | ~ m1_subset_1(C_217,k1_zfmisc_1(u1_struct_0(A_218)))
      | ~ m1_subset_1(B_219,u1_struct_0(A_218))
      | ~ l1_pre_topc(A_218)
      | ~ v2_pre_topc(A_218)
      | v2_struct_0(A_218) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_684,plain,
    ( m1_connsp_2('#skF_3','#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1'))
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_609,c_678])).

tff(c_695,plain,
    ( m1_connsp_2('#skF_3','#skF_1','#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_684])).

tff(c_697,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_406,c_695])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:37:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.94/1.45  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.94/1.46  
% 2.94/1.46  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.94/1.47  %$ m2_connsp_2 > m1_connsp_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k6_domain_1 > k2_tarski > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 2.94/1.47  
% 2.94/1.47  %Foreground sorts:
% 2.94/1.47  
% 2.94/1.47  
% 2.94/1.47  %Background operators:
% 2.94/1.47  
% 2.94/1.47  
% 2.94/1.47  %Foreground operators:
% 2.94/1.47  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.94/1.47  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 2.94/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.94/1.47  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.94/1.47  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.94/1.47  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.94/1.47  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.94/1.47  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.94/1.47  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.94/1.47  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.94/1.47  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.94/1.47  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 2.94/1.47  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.94/1.47  tff('#skF_2', type, '#skF_2': $i).
% 2.94/1.47  tff('#skF_3', type, '#skF_3': $i).
% 2.94/1.47  tff('#skF_1', type, '#skF_1': $i).
% 2.94/1.47  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.94/1.47  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.94/1.47  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.94/1.47  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.94/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.94/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.94/1.47  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.94/1.47  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.94/1.47  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.94/1.47  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.94/1.47  tff(m2_connsp_2, type, m2_connsp_2: ($i * $i * $i) > $o).
% 2.94/1.47  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.94/1.47  
% 3.07/1.48  tff(f_145, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m2_connsp_2(C, A, k6_domain_1(u1_struct_0(A), B)) <=> m1_connsp_2(C, A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_connsp_2)).
% 3.07/1.48  tff(f_88, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m1_connsp_2(C, A, B) <=> r2_hidden(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_connsp_2)).
% 3.07/1.48  tff(f_49, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.07/1.48  tff(f_71, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 3.07/1.48  tff(f_57, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 3.07/1.48  tff(f_64, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 3.07/1.48  tff(f_27, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 3.07/1.48  tff(f_45, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 3.07/1.48  tff(f_102, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m2_connsp_2(C, A, B) <=> r1_tarski(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_connsp_2)).
% 3.07/1.48  tff(c_50, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_145])).
% 3.07/1.48  tff(c_44, plain, (m1_subset_1('#skF_2', u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_145])).
% 3.07/1.48  tff(c_52, plain, (~m1_connsp_2('#skF_3', '#skF_1', '#skF_2') | ~m2_connsp_2('#skF_3', '#skF_1', k6_domain_1(u1_struct_0('#skF_1'), '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_145])).
% 3.07/1.48  tff(c_79, plain, (~m2_connsp_2('#skF_3', '#skF_1', k6_domain_1(u1_struct_0('#skF_1'), '#skF_2'))), inference(splitLeft, [status(thm)], [c_52])).
% 3.07/1.48  tff(c_58, plain, (m2_connsp_2('#skF_3', '#skF_1', k6_domain_1(u1_struct_0('#skF_1'), '#skF_2')) | m1_connsp_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_145])).
% 3.07/1.48  tff(c_123, plain, (m1_connsp_2('#skF_3', '#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_79, c_58])).
% 3.07/1.48  tff(c_48, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_145])).
% 3.07/1.48  tff(c_46, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_145])).
% 3.07/1.48  tff(c_42, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_145])).
% 3.07/1.48  tff(c_299, plain, (![B_128, A_129, C_130]: (r2_hidden(B_128, k1_tops_1(A_129, C_130)) | ~m1_connsp_2(C_130, A_129, B_128) | ~m1_subset_1(C_130, k1_zfmisc_1(u1_struct_0(A_129))) | ~m1_subset_1(B_128, u1_struct_0(A_129)) | ~l1_pre_topc(A_129) | ~v2_pre_topc(A_129) | v2_struct_0(A_129))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.07/1.48  tff(c_306, plain, (![B_128]: (r2_hidden(B_128, k1_tops_1('#skF_1', '#skF_3')) | ~m1_connsp_2('#skF_3', '#skF_1', B_128) | ~m1_subset_1(B_128, u1_struct_0('#skF_1')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_42, c_299])).
% 3.07/1.48  tff(c_314, plain, (![B_128]: (r2_hidden(B_128, k1_tops_1('#skF_1', '#skF_3')) | ~m1_connsp_2('#skF_3', '#skF_1', B_128) | ~m1_subset_1(B_128, u1_struct_0('#skF_1')) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_306])).
% 3.07/1.48  tff(c_315, plain, (![B_128]: (r2_hidden(B_128, k1_tops_1('#skF_1', '#skF_3')) | ~m1_connsp_2('#skF_3', '#skF_1', B_128) | ~m1_subset_1(B_128, u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_50, c_314])).
% 3.07/1.48  tff(c_22, plain, (![A_32]: (l1_struct_0(A_32) | ~l1_pre_topc(A_32))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.07/1.48  tff(c_98, plain, (![A_80, B_81]: (k6_domain_1(A_80, B_81)=k1_tarski(B_81) | ~m1_subset_1(B_81, A_80) | v1_xboole_0(A_80))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.07/1.48  tff(c_106, plain, (k6_domain_1(u1_struct_0('#skF_1'), '#skF_2')=k1_tarski('#skF_2') | v1_xboole_0(u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_44, c_98])).
% 3.07/1.48  tff(c_107, plain, (v1_xboole_0(u1_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_106])).
% 3.07/1.48  tff(c_24, plain, (![A_33]: (~v1_xboole_0(u1_struct_0(A_33)) | ~l1_struct_0(A_33) | v2_struct_0(A_33))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.07/1.48  tff(c_110, plain, (~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_107, c_24])).
% 3.07/1.48  tff(c_113, plain, (~l1_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_50, c_110])).
% 3.07/1.48  tff(c_116, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_22, c_113])).
% 3.07/1.48  tff(c_120, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_116])).
% 3.07/1.48  tff(c_121, plain, (k6_domain_1(u1_struct_0('#skF_1'), '#skF_2')=k1_tarski('#skF_2')), inference(splitRight, [status(thm)], [c_106])).
% 3.07/1.48  tff(c_124, plain, (~m2_connsp_2('#skF_3', '#skF_1', k1_tarski('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_121, c_79])).
% 3.07/1.48  tff(c_122, plain, (~v1_xboole_0(u1_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_106])).
% 3.07/1.48  tff(c_146, plain, (![A_87, B_88]: (m1_subset_1(k6_domain_1(A_87, B_88), k1_zfmisc_1(A_87)) | ~m1_subset_1(B_88, A_87) | v1_xboole_0(A_87))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.07/1.48  tff(c_152, plain, (m1_subset_1(k1_tarski('#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', u1_struct_0('#skF_1')) | v1_xboole_0(u1_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_121, c_146])).
% 3.07/1.48  tff(c_155, plain, (m1_subset_1(k1_tarski('#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | v1_xboole_0(u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_152])).
% 3.07/1.48  tff(c_156, plain, (m1_subset_1(k1_tarski('#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_122, c_155])).
% 3.07/1.48  tff(c_2, plain, (![A_1]: (k2_tarski(A_1, A_1)=k1_tarski(A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.07/1.48  tff(c_129, plain, (![A_82, B_83, C_84]: (r1_tarski(k2_tarski(A_82, B_83), C_84) | ~r2_hidden(B_83, C_84) | ~r2_hidden(A_82, C_84))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.07/1.48  tff(c_138, plain, (![A_1, C_84]: (r1_tarski(k1_tarski(A_1), C_84) | ~r2_hidden(A_1, C_84) | ~r2_hidden(A_1, C_84))), inference(superposition, [status(thm), theory('equality')], [c_2, c_129])).
% 3.07/1.48  tff(c_231, plain, (![C_119, A_120, B_121]: (m2_connsp_2(C_119, A_120, B_121) | ~r1_tarski(B_121, k1_tops_1(A_120, C_119)) | ~m1_subset_1(C_119, k1_zfmisc_1(u1_struct_0(A_120))) | ~m1_subset_1(B_121, k1_zfmisc_1(u1_struct_0(A_120))) | ~l1_pre_topc(A_120) | ~v2_pre_topc(A_120))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.07/1.48  tff(c_352, plain, (![C_141, A_142, A_143]: (m2_connsp_2(C_141, A_142, k1_tarski(A_143)) | ~m1_subset_1(C_141, k1_zfmisc_1(u1_struct_0(A_142))) | ~m1_subset_1(k1_tarski(A_143), k1_zfmisc_1(u1_struct_0(A_142))) | ~l1_pre_topc(A_142) | ~v2_pre_topc(A_142) | ~r2_hidden(A_143, k1_tops_1(A_142, C_141)))), inference(resolution, [status(thm)], [c_138, c_231])).
% 3.07/1.48  tff(c_359, plain, (![A_143]: (m2_connsp_2('#skF_3', '#skF_1', k1_tarski(A_143)) | ~m1_subset_1(k1_tarski(A_143), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | ~r2_hidden(A_143, k1_tops_1('#skF_1', '#skF_3')))), inference(resolution, [status(thm)], [c_42, c_352])).
% 3.07/1.48  tff(c_367, plain, (![A_144]: (m2_connsp_2('#skF_3', '#skF_1', k1_tarski(A_144)) | ~m1_subset_1(k1_tarski(A_144), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~r2_hidden(A_144, k1_tops_1('#skF_1', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_359])).
% 3.07/1.48  tff(c_370, plain, (m2_connsp_2('#skF_3', '#skF_1', k1_tarski('#skF_2')) | ~r2_hidden('#skF_2', k1_tops_1('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_156, c_367])).
% 3.07/1.48  tff(c_373, plain, (~r2_hidden('#skF_2', k1_tops_1('#skF_1', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_124, c_370])).
% 3.07/1.48  tff(c_401, plain, (~m1_connsp_2('#skF_3', '#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_315, c_373])).
% 3.07/1.48  tff(c_405, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_123, c_401])).
% 3.07/1.48  tff(c_406, plain, (~m1_connsp_2('#skF_3', '#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_52])).
% 3.07/1.48  tff(c_428, plain, (![A_159, B_160]: (k6_domain_1(A_159, B_160)=k1_tarski(B_160) | ~m1_subset_1(B_160, A_159) | v1_xboole_0(A_159))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.07/1.48  tff(c_436, plain, (k6_domain_1(u1_struct_0('#skF_1'), '#skF_2')=k1_tarski('#skF_2') | v1_xboole_0(u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_44, c_428])).
% 3.07/1.48  tff(c_442, plain, (v1_xboole_0(u1_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_436])).
% 3.07/1.48  tff(c_445, plain, (~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_442, c_24])).
% 3.07/1.48  tff(c_448, plain, (~l1_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_50, c_445])).
% 3.07/1.48  tff(c_451, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_22, c_448])).
% 3.07/1.48  tff(c_455, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_451])).
% 3.07/1.48  tff(c_456, plain, (k6_domain_1(u1_struct_0('#skF_1'), '#skF_2')=k1_tarski('#skF_2')), inference(splitRight, [status(thm)], [c_436])).
% 3.07/1.48  tff(c_407, plain, (m2_connsp_2('#skF_3', '#skF_1', k6_domain_1(u1_struct_0('#skF_1'), '#skF_2'))), inference(splitRight, [status(thm)], [c_52])).
% 3.07/1.48  tff(c_459, plain, (m2_connsp_2('#skF_3', '#skF_1', k1_tarski('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_456, c_407])).
% 3.07/1.48  tff(c_457, plain, (~v1_xboole_0(u1_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_436])).
% 3.07/1.48  tff(c_26, plain, (![A_34, B_35]: (m1_subset_1(k6_domain_1(A_34, B_35), k1_zfmisc_1(A_34)) | ~m1_subset_1(B_35, A_34) | v1_xboole_0(A_34))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.07/1.48  tff(c_463, plain, (m1_subset_1(k1_tarski('#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', u1_struct_0('#skF_1')) | v1_xboole_0(u1_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_456, c_26])).
% 3.07/1.48  tff(c_467, plain, (m1_subset_1(k1_tarski('#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | v1_xboole_0(u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_463])).
% 3.07/1.48  tff(c_468, plain, (m1_subset_1(k1_tarski('#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_457, c_467])).
% 3.07/1.48  tff(c_568, plain, (![B_201, A_202, C_203]: (r1_tarski(B_201, k1_tops_1(A_202, C_203)) | ~m2_connsp_2(C_203, A_202, B_201) | ~m1_subset_1(C_203, k1_zfmisc_1(u1_struct_0(A_202))) | ~m1_subset_1(B_201, k1_zfmisc_1(u1_struct_0(A_202))) | ~l1_pre_topc(A_202) | ~v2_pre_topc(A_202))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.07/1.48  tff(c_575, plain, (![B_201]: (r1_tarski(B_201, k1_tops_1('#skF_1', '#skF_3')) | ~m2_connsp_2('#skF_3', '#skF_1', B_201) | ~m1_subset_1(B_201, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_42, c_568])).
% 3.07/1.48  tff(c_583, plain, (![B_204]: (r1_tarski(B_204, k1_tops_1('#skF_1', '#skF_3')) | ~m2_connsp_2('#skF_3', '#skF_1', B_204) | ~m1_subset_1(B_204, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_575])).
% 3.07/1.48  tff(c_586, plain, (r1_tarski(k1_tarski('#skF_2'), k1_tops_1('#skF_1', '#skF_3')) | ~m2_connsp_2('#skF_3', '#skF_1', k1_tarski('#skF_2'))), inference(resolution, [status(thm)], [c_468, c_583])).
% 3.07/1.48  tff(c_596, plain, (r1_tarski(k1_tarski('#skF_2'), k1_tops_1('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_459, c_586])).
% 3.07/1.48  tff(c_410, plain, (![A_148, C_149, B_150]: (r2_hidden(A_148, C_149) | ~r1_tarski(k2_tarski(A_148, B_150), C_149))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.07/1.48  tff(c_413, plain, (![A_1, C_149]: (r2_hidden(A_1, C_149) | ~r1_tarski(k1_tarski(A_1), C_149))), inference(superposition, [status(thm), theory('equality')], [c_2, c_410])).
% 3.07/1.48  tff(c_609, plain, (r2_hidden('#skF_2', k1_tops_1('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_596, c_413])).
% 3.07/1.48  tff(c_678, plain, (![C_217, A_218, B_219]: (m1_connsp_2(C_217, A_218, B_219) | ~r2_hidden(B_219, k1_tops_1(A_218, C_217)) | ~m1_subset_1(C_217, k1_zfmisc_1(u1_struct_0(A_218))) | ~m1_subset_1(B_219, u1_struct_0(A_218)) | ~l1_pre_topc(A_218) | ~v2_pre_topc(A_218) | v2_struct_0(A_218))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.07/1.48  tff(c_684, plain, (m1_connsp_2('#skF_3', '#skF_1', '#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', u1_struct_0('#skF_1')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_609, c_678])).
% 3.07/1.48  tff(c_695, plain, (m1_connsp_2('#skF_3', '#skF_1', '#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_684])).
% 3.07/1.48  tff(c_697, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_406, c_695])).
% 3.07/1.48  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.07/1.48  
% 3.07/1.48  Inference rules
% 3.07/1.48  ----------------------
% 3.07/1.48  #Ref     : 0
% 3.07/1.48  #Sup     : 125
% 3.07/1.48  #Fact    : 0
% 3.07/1.48  #Define  : 0
% 3.07/1.48  #Split   : 9
% 3.07/1.48  #Chain   : 0
% 3.07/1.48  #Close   : 0
% 3.07/1.48  
% 3.07/1.48  Ordering : KBO
% 3.07/1.48  
% 3.07/1.48  Simplification rules
% 3.07/1.48  ----------------------
% 3.07/1.48  #Subsume      : 9
% 3.07/1.48  #Demod        : 93
% 3.07/1.48  #Tautology    : 58
% 3.07/1.48  #SimpNegUnit  : 22
% 3.07/1.48  #BackRed      : 2
% 3.07/1.48  
% 3.07/1.48  #Partial instantiations: 0
% 3.07/1.48  #Strategies tried      : 1
% 3.07/1.48  
% 3.07/1.48  Timing (in seconds)
% 3.07/1.48  ----------------------
% 3.07/1.49  Preprocessing        : 0.34
% 3.07/1.49  Parsing              : 0.18
% 3.07/1.49  CNF conversion       : 0.02
% 3.07/1.49  Main loop            : 0.33
% 3.07/1.49  Inferencing          : 0.13
% 3.07/1.49  Reduction            : 0.10
% 3.07/1.49  Demodulation         : 0.07
% 3.07/1.49  BG Simplification    : 0.02
% 3.07/1.49  Subsumption          : 0.05
% 3.07/1.49  Abstraction          : 0.02
% 3.07/1.49  MUC search           : 0.00
% 3.07/1.49  Cooper               : 0.00
% 3.07/1.49  Total                : 0.71
% 3.07/1.49  Index Insertion      : 0.00
% 3.07/1.49  Index Deletion       : 0.00
% 3.07/1.49  Index Matching       : 0.00
% 3.07/1.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
