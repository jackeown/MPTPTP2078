%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:11 EST 2020

% Result     : Theorem 16.90s
% Output     : CNFRefutation 16.90s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 147 expanded)
%              Number of leaves         :   30 (  64 expanded)
%              Depth                    :   10
%              Number of atoms          :  119 ( 274 expanded)
%              Number of equality atoms :   18 (  41 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tex_2 > r1_tarski > m1_subset_1 > l1_pre_topc > k9_subset_1 > k7_subset_1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_82,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( ( v2_tex_2(B,A)
                    | v2_tex_2(C,A) )
                 => v2_tex_2(k9_subset_1(u1_struct_0(A),B,C),A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_tex_2)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k7_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_subset_1)).

tff(f_33,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_35,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_67,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( r1_tarski(C,B)
                  & v2_tex_2(B,A) )
               => v2_tex_2(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_tex_2)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(c_4,plain,(
    ! [A_3,B_4] : k4_xboole_0(A_3,k4_xboole_0(A_3,B_4)) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_34,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_30,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_32,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_28,plain,
    ( v2_tex_2('#skF_3','#skF_1')
    | v2_tex_2('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_46,plain,(
    v2_tex_2('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_151,plain,(
    ! [A_50,B_51,C_52] :
      ( k7_subset_1(A_50,B_51,C_52) = k4_xboole_0(B_51,C_52)
      | ~ m1_subset_1(B_51,k1_zfmisc_1(A_50)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_162,plain,(
    ! [C_52] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_52) = k4_xboole_0('#skF_2',C_52) ),
    inference(resolution,[status(thm)],[c_32,c_151])).

tff(c_234,plain,(
    ! [A_62,B_63,C_64] :
      ( m1_subset_1(k7_subset_1(A_62,B_63,C_64),k1_zfmisc_1(A_62))
      | ~ m1_subset_1(B_63,k1_zfmisc_1(A_62)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_242,plain,(
    ! [C_52] :
      ( m1_subset_1(k4_xboole_0('#skF_2',C_52),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_162,c_234])).

tff(c_252,plain,(
    ! [C_52] : m1_subset_1(k4_xboole_0('#skF_2',C_52),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_242])).

tff(c_8,plain,(
    ! [A_7] : k2_subset_1(A_7) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_10,plain,(
    ! [A_8] : m1_subset_1(k2_subset_1(A_8),k1_zfmisc_1(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_35,plain,(
    ! [A_8] : m1_subset_1(A_8,k1_zfmisc_1(A_8)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_10])).

tff(c_163,plain,(
    ! [A_8,C_52] : k7_subset_1(A_8,A_8,C_52) = k4_xboole_0(A_8,C_52) ),
    inference(resolution,[status(thm)],[c_35,c_151])).

tff(c_20,plain,(
    ! [A_20,B_21] :
      ( r1_tarski(A_20,B_21)
      | ~ m1_subset_1(A_20,k1_zfmisc_1(B_21)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_630,plain,(
    ! [A_98,B_99,C_100] :
      ( r1_tarski(k7_subset_1(A_98,B_99,C_100),A_98)
      | ~ m1_subset_1(B_99,k1_zfmisc_1(A_98)) ) ),
    inference(resolution,[status(thm)],[c_234,c_20])).

tff(c_24,plain,(
    ! [C_28,A_22,B_26] :
      ( v2_tex_2(C_28,A_22)
      | ~ v2_tex_2(B_26,A_22)
      | ~ r1_tarski(C_28,B_26)
      | ~ m1_subset_1(C_28,k1_zfmisc_1(u1_struct_0(A_22)))
      | ~ m1_subset_1(B_26,k1_zfmisc_1(u1_struct_0(A_22)))
      | ~ l1_pre_topc(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_2944,plain,(
    ! [A_255,B_256,C_257,A_258] :
      ( v2_tex_2(k7_subset_1(A_255,B_256,C_257),A_258)
      | ~ v2_tex_2(A_255,A_258)
      | ~ m1_subset_1(k7_subset_1(A_255,B_256,C_257),k1_zfmisc_1(u1_struct_0(A_258)))
      | ~ m1_subset_1(A_255,k1_zfmisc_1(u1_struct_0(A_258)))
      | ~ l1_pre_topc(A_258)
      | ~ m1_subset_1(B_256,k1_zfmisc_1(A_255)) ) ),
    inference(resolution,[status(thm)],[c_630,c_24])).

tff(c_2978,plain,(
    ! [A_8,C_52,A_258] :
      ( v2_tex_2(k7_subset_1(A_8,A_8,C_52),A_258)
      | ~ v2_tex_2(A_8,A_258)
      | ~ m1_subset_1(k4_xboole_0(A_8,C_52),k1_zfmisc_1(u1_struct_0(A_258)))
      | ~ m1_subset_1(A_8,k1_zfmisc_1(u1_struct_0(A_258)))
      | ~ l1_pre_topc(A_258)
      | ~ m1_subset_1(A_8,k1_zfmisc_1(A_8)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_163,c_2944])).

tff(c_22843,plain,(
    ! [A_645,C_646,A_647] :
      ( v2_tex_2(k4_xboole_0(A_645,C_646),A_647)
      | ~ v2_tex_2(A_645,A_647)
      | ~ m1_subset_1(k4_xboole_0(A_645,C_646),k1_zfmisc_1(u1_struct_0(A_647)))
      | ~ m1_subset_1(A_645,k1_zfmisc_1(u1_struct_0(A_647)))
      | ~ l1_pre_topc(A_647) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_35,c_163,c_2978])).

tff(c_22963,plain,(
    ! [C_52] :
      ( v2_tex_2(k4_xboole_0('#skF_2',C_52),'#skF_1')
      | ~ v2_tex_2('#skF_2','#skF_1')
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_252,c_22843])).

tff(c_23057,plain,(
    ! [C_648] : v2_tex_2(k4_xboole_0('#skF_2',C_648),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_46,c_22963])).

tff(c_23094,plain,(
    ! [B_649] : v2_tex_2(k3_xboole_0('#skF_2',B_649),'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_23057])).

tff(c_23138,plain,(
    ! [B_2] : v2_tex_2(k3_xboole_0(B_2,'#skF_2'),'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_23094])).

tff(c_378,plain,(
    ! [A_79,B_80,C_81] :
      ( k9_subset_1(A_79,B_80,C_81) = k3_xboole_0(B_80,C_81)
      | ~ m1_subset_1(C_81,k1_zfmisc_1(A_79)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_403,plain,(
    ! [B_80] : k9_subset_1(u1_struct_0('#skF_1'),B_80,'#skF_3') = k3_xboole_0(B_80,'#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_378])).

tff(c_26,plain,(
    ~ v2_tex_2(k9_subset_1(u1_struct_0('#skF_1'),'#skF_2','#skF_3'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_433,plain,(
    ~ v2_tex_2(k3_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_403,c_26])).

tff(c_434,plain,(
    ~ v2_tex_2(k3_xboole_0('#skF_3','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_433])).

tff(c_23155,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_23138,c_434])).

tff(c_23156,plain,(
    v2_tex_2('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_23360,plain,(
    ! [A_683,B_684,C_685] :
      ( k7_subset_1(A_683,B_684,C_685) = k4_xboole_0(B_684,C_685)
      | ~ m1_subset_1(B_684,k1_zfmisc_1(A_683)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_23452,plain,(
    ! [C_697] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_3',C_697) = k4_xboole_0('#skF_3',C_697) ),
    inference(resolution,[status(thm)],[c_30,c_23360])).

tff(c_12,plain,(
    ! [A_9,B_10,C_11] :
      ( m1_subset_1(k7_subset_1(A_9,B_10,C_11),k1_zfmisc_1(A_9))
      | ~ m1_subset_1(B_10,k1_zfmisc_1(A_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_23461,plain,(
    ! [C_697] :
      ( m1_subset_1(k4_xboole_0('#skF_3',C_697),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_23452,c_12])).

tff(c_23469,plain,(
    ! [C_697] : m1_subset_1(k4_xboole_0('#skF_3',C_697),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_23461])).

tff(c_23376,plain,(
    ! [A_686,C_687] : k7_subset_1(A_686,A_686,C_687) = k4_xboole_0(A_686,C_687) ),
    inference(resolution,[status(thm)],[c_35,c_23360])).

tff(c_23293,plain,(
    ! [A_667,B_668,C_669] :
      ( m1_subset_1(k7_subset_1(A_667,B_668,C_669),k1_zfmisc_1(A_667))
      | ~ m1_subset_1(B_668,k1_zfmisc_1(A_667)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_23297,plain,(
    ! [A_667,B_668,C_669] :
      ( r1_tarski(k7_subset_1(A_667,B_668,C_669),A_667)
      | ~ m1_subset_1(B_668,k1_zfmisc_1(A_667)) ) ),
    inference(resolution,[status(thm)],[c_23293,c_20])).

tff(c_23382,plain,(
    ! [A_686,C_687] :
      ( r1_tarski(k4_xboole_0(A_686,C_687),A_686)
      | ~ m1_subset_1(A_686,k1_zfmisc_1(A_686)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_23376,c_23297])).

tff(c_23408,plain,(
    ! [A_691,C_692] : r1_tarski(k4_xboole_0(A_691,C_692),A_691) ),
    inference(demodulation,[status(thm),theory(equality)],[c_35,c_23382])).

tff(c_47583,plain,(
    ! [A_1351,C_1352,A_1353] :
      ( v2_tex_2(k4_xboole_0(A_1351,C_1352),A_1353)
      | ~ v2_tex_2(A_1351,A_1353)
      | ~ m1_subset_1(k4_xboole_0(A_1351,C_1352),k1_zfmisc_1(u1_struct_0(A_1353)))
      | ~ m1_subset_1(A_1351,k1_zfmisc_1(u1_struct_0(A_1353)))
      | ~ l1_pre_topc(A_1353) ) ),
    inference(resolution,[status(thm)],[c_23408,c_24])).

tff(c_47707,plain,(
    ! [C_697] :
      ( v2_tex_2(k4_xboole_0('#skF_3',C_697),'#skF_1')
      | ~ v2_tex_2('#skF_3','#skF_1')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_23469,c_47583])).

tff(c_47804,plain,(
    ! [C_1354] : v2_tex_2(k4_xboole_0('#skF_3',C_1354),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_23156,c_47707])).

tff(c_47840,plain,(
    ! [B_4] : v2_tex_2(k3_xboole_0('#skF_3',B_4),'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_47804])).

tff(c_23299,plain,(
    ! [A_673,B_674,C_675] :
      ( k9_subset_1(A_673,B_674,C_675) = k3_xboole_0(B_674,C_675)
      | ~ m1_subset_1(C_675,k1_zfmisc_1(A_673)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_23312,plain,(
    ! [B_674] : k9_subset_1(u1_struct_0('#skF_1'),B_674,'#skF_3') = k3_xboole_0(B_674,'#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_23299])).

tff(c_23324,plain,(
    ~ v2_tex_2(k3_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_23312,c_26])).

tff(c_23325,plain,(
    ~ v2_tex_2(k3_xboole_0('#skF_3','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_23324])).

tff(c_47843,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_47840,c_23325])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:47:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 16.90/8.59  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 16.90/8.59  
% 16.90/8.59  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 16.90/8.60  %$ v2_tex_2 > r1_tarski > m1_subset_1 > l1_pre_topc > k9_subset_1 > k7_subset_1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1
% 16.90/8.60  
% 16.90/8.60  %Foreground sorts:
% 16.90/8.60  
% 16.90/8.60  
% 16.90/8.60  %Background operators:
% 16.90/8.60  
% 16.90/8.60  
% 16.90/8.60  %Foreground operators:
% 16.90/8.60  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 16.90/8.60  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 16.90/8.60  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 16.90/8.60  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 16.90/8.60  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 16.90/8.60  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 16.90/8.60  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 16.90/8.60  tff('#skF_2', type, '#skF_2': $i).
% 16.90/8.60  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 16.90/8.60  tff('#skF_3', type, '#skF_3': $i).
% 16.90/8.60  tff('#skF_1', type, '#skF_1': $i).
% 16.90/8.60  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 16.90/8.60  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 16.90/8.60  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 16.90/8.60  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 16.90/8.60  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 16.90/8.60  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 16.90/8.60  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 16.90/8.60  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 16.90/8.60  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 16.90/8.60  
% 16.90/8.61  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 16.90/8.61  tff(f_82, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v2_tex_2(B, A) | v2_tex_2(C, A)) => v2_tex_2(k9_subset_1(u1_struct_0(A), B, C), A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_tex_2)).
% 16.90/8.61  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 16.90/8.61  tff(f_43, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 16.90/8.61  tff(f_39, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k7_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_subset_1)).
% 16.90/8.61  tff(f_33, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 16.90/8.61  tff(f_35, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 16.90/8.61  tff(f_53, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 16.90/8.61  tff(f_67, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((r1_tarski(C, B) & v2_tex_2(B, A)) => v2_tex_2(C, A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_tex_2)).
% 16.90/8.61  tff(f_47, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 16.90/8.61  tff(c_4, plain, (![A_3, B_4]: (k4_xboole_0(A_3, k4_xboole_0(A_3, B_4))=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 16.90/8.61  tff(c_34, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_82])).
% 16.90/8.61  tff(c_30, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_82])).
% 16.90/8.61  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 16.90/8.61  tff(c_32, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_82])).
% 16.90/8.61  tff(c_28, plain, (v2_tex_2('#skF_3', '#skF_1') | v2_tex_2('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_82])).
% 16.90/8.61  tff(c_46, plain, (v2_tex_2('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_28])).
% 16.90/8.61  tff(c_151, plain, (![A_50, B_51, C_52]: (k7_subset_1(A_50, B_51, C_52)=k4_xboole_0(B_51, C_52) | ~m1_subset_1(B_51, k1_zfmisc_1(A_50)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 16.90/8.61  tff(c_162, plain, (![C_52]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_52)=k4_xboole_0('#skF_2', C_52))), inference(resolution, [status(thm)], [c_32, c_151])).
% 16.90/8.61  tff(c_234, plain, (![A_62, B_63, C_64]: (m1_subset_1(k7_subset_1(A_62, B_63, C_64), k1_zfmisc_1(A_62)) | ~m1_subset_1(B_63, k1_zfmisc_1(A_62)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 16.90/8.61  tff(c_242, plain, (![C_52]: (m1_subset_1(k4_xboole_0('#skF_2', C_52), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_162, c_234])).
% 16.90/8.61  tff(c_252, plain, (![C_52]: (m1_subset_1(k4_xboole_0('#skF_2', C_52), k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_242])).
% 16.90/8.61  tff(c_8, plain, (![A_7]: (k2_subset_1(A_7)=A_7)), inference(cnfTransformation, [status(thm)], [f_33])).
% 16.90/8.61  tff(c_10, plain, (![A_8]: (m1_subset_1(k2_subset_1(A_8), k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 16.90/8.61  tff(c_35, plain, (![A_8]: (m1_subset_1(A_8, k1_zfmisc_1(A_8)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_10])).
% 16.90/8.61  tff(c_163, plain, (![A_8, C_52]: (k7_subset_1(A_8, A_8, C_52)=k4_xboole_0(A_8, C_52))), inference(resolution, [status(thm)], [c_35, c_151])).
% 16.90/8.61  tff(c_20, plain, (![A_20, B_21]: (r1_tarski(A_20, B_21) | ~m1_subset_1(A_20, k1_zfmisc_1(B_21)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 16.90/8.61  tff(c_630, plain, (![A_98, B_99, C_100]: (r1_tarski(k7_subset_1(A_98, B_99, C_100), A_98) | ~m1_subset_1(B_99, k1_zfmisc_1(A_98)))), inference(resolution, [status(thm)], [c_234, c_20])).
% 16.90/8.61  tff(c_24, plain, (![C_28, A_22, B_26]: (v2_tex_2(C_28, A_22) | ~v2_tex_2(B_26, A_22) | ~r1_tarski(C_28, B_26) | ~m1_subset_1(C_28, k1_zfmisc_1(u1_struct_0(A_22))) | ~m1_subset_1(B_26, k1_zfmisc_1(u1_struct_0(A_22))) | ~l1_pre_topc(A_22))), inference(cnfTransformation, [status(thm)], [f_67])).
% 16.90/8.61  tff(c_2944, plain, (![A_255, B_256, C_257, A_258]: (v2_tex_2(k7_subset_1(A_255, B_256, C_257), A_258) | ~v2_tex_2(A_255, A_258) | ~m1_subset_1(k7_subset_1(A_255, B_256, C_257), k1_zfmisc_1(u1_struct_0(A_258))) | ~m1_subset_1(A_255, k1_zfmisc_1(u1_struct_0(A_258))) | ~l1_pre_topc(A_258) | ~m1_subset_1(B_256, k1_zfmisc_1(A_255)))), inference(resolution, [status(thm)], [c_630, c_24])).
% 16.90/8.61  tff(c_2978, plain, (![A_8, C_52, A_258]: (v2_tex_2(k7_subset_1(A_8, A_8, C_52), A_258) | ~v2_tex_2(A_8, A_258) | ~m1_subset_1(k4_xboole_0(A_8, C_52), k1_zfmisc_1(u1_struct_0(A_258))) | ~m1_subset_1(A_8, k1_zfmisc_1(u1_struct_0(A_258))) | ~l1_pre_topc(A_258) | ~m1_subset_1(A_8, k1_zfmisc_1(A_8)))), inference(superposition, [status(thm), theory('equality')], [c_163, c_2944])).
% 16.90/8.61  tff(c_22843, plain, (![A_645, C_646, A_647]: (v2_tex_2(k4_xboole_0(A_645, C_646), A_647) | ~v2_tex_2(A_645, A_647) | ~m1_subset_1(k4_xboole_0(A_645, C_646), k1_zfmisc_1(u1_struct_0(A_647))) | ~m1_subset_1(A_645, k1_zfmisc_1(u1_struct_0(A_647))) | ~l1_pre_topc(A_647))), inference(demodulation, [status(thm), theory('equality')], [c_35, c_163, c_2978])).
% 16.90/8.61  tff(c_22963, plain, (![C_52]: (v2_tex_2(k4_xboole_0('#skF_2', C_52), '#skF_1') | ~v2_tex_2('#skF_2', '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_252, c_22843])).
% 16.90/8.61  tff(c_23057, plain, (![C_648]: (v2_tex_2(k4_xboole_0('#skF_2', C_648), '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_46, c_22963])).
% 16.90/8.61  tff(c_23094, plain, (![B_649]: (v2_tex_2(k3_xboole_0('#skF_2', B_649), '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_4, c_23057])).
% 16.90/8.61  tff(c_23138, plain, (![B_2]: (v2_tex_2(k3_xboole_0(B_2, '#skF_2'), '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_2, c_23094])).
% 16.90/8.61  tff(c_378, plain, (![A_79, B_80, C_81]: (k9_subset_1(A_79, B_80, C_81)=k3_xboole_0(B_80, C_81) | ~m1_subset_1(C_81, k1_zfmisc_1(A_79)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 16.90/8.61  tff(c_403, plain, (![B_80]: (k9_subset_1(u1_struct_0('#skF_1'), B_80, '#skF_3')=k3_xboole_0(B_80, '#skF_3'))), inference(resolution, [status(thm)], [c_30, c_378])).
% 16.90/8.61  tff(c_26, plain, (~v2_tex_2(k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', '#skF_3'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_82])).
% 16.90/8.61  tff(c_433, plain, (~v2_tex_2(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_403, c_26])).
% 16.90/8.61  tff(c_434, plain, (~v2_tex_2(k3_xboole_0('#skF_3', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_433])).
% 16.90/8.61  tff(c_23155, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_23138, c_434])).
% 16.90/8.61  tff(c_23156, plain, (v2_tex_2('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_28])).
% 16.90/8.61  tff(c_23360, plain, (![A_683, B_684, C_685]: (k7_subset_1(A_683, B_684, C_685)=k4_xboole_0(B_684, C_685) | ~m1_subset_1(B_684, k1_zfmisc_1(A_683)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 16.90/8.61  tff(c_23452, plain, (![C_697]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_3', C_697)=k4_xboole_0('#skF_3', C_697))), inference(resolution, [status(thm)], [c_30, c_23360])).
% 16.90/8.61  tff(c_12, plain, (![A_9, B_10, C_11]: (m1_subset_1(k7_subset_1(A_9, B_10, C_11), k1_zfmisc_1(A_9)) | ~m1_subset_1(B_10, k1_zfmisc_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 16.90/8.61  tff(c_23461, plain, (![C_697]: (m1_subset_1(k4_xboole_0('#skF_3', C_697), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_23452, c_12])).
% 16.90/8.61  tff(c_23469, plain, (![C_697]: (m1_subset_1(k4_xboole_0('#skF_3', C_697), k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_23461])).
% 16.90/8.61  tff(c_23376, plain, (![A_686, C_687]: (k7_subset_1(A_686, A_686, C_687)=k4_xboole_0(A_686, C_687))), inference(resolution, [status(thm)], [c_35, c_23360])).
% 16.90/8.61  tff(c_23293, plain, (![A_667, B_668, C_669]: (m1_subset_1(k7_subset_1(A_667, B_668, C_669), k1_zfmisc_1(A_667)) | ~m1_subset_1(B_668, k1_zfmisc_1(A_667)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 16.90/8.61  tff(c_23297, plain, (![A_667, B_668, C_669]: (r1_tarski(k7_subset_1(A_667, B_668, C_669), A_667) | ~m1_subset_1(B_668, k1_zfmisc_1(A_667)))), inference(resolution, [status(thm)], [c_23293, c_20])).
% 16.90/8.61  tff(c_23382, plain, (![A_686, C_687]: (r1_tarski(k4_xboole_0(A_686, C_687), A_686) | ~m1_subset_1(A_686, k1_zfmisc_1(A_686)))), inference(superposition, [status(thm), theory('equality')], [c_23376, c_23297])).
% 16.90/8.61  tff(c_23408, plain, (![A_691, C_692]: (r1_tarski(k4_xboole_0(A_691, C_692), A_691))), inference(demodulation, [status(thm), theory('equality')], [c_35, c_23382])).
% 16.90/8.61  tff(c_47583, plain, (![A_1351, C_1352, A_1353]: (v2_tex_2(k4_xboole_0(A_1351, C_1352), A_1353) | ~v2_tex_2(A_1351, A_1353) | ~m1_subset_1(k4_xboole_0(A_1351, C_1352), k1_zfmisc_1(u1_struct_0(A_1353))) | ~m1_subset_1(A_1351, k1_zfmisc_1(u1_struct_0(A_1353))) | ~l1_pre_topc(A_1353))), inference(resolution, [status(thm)], [c_23408, c_24])).
% 16.90/8.61  tff(c_47707, plain, (![C_697]: (v2_tex_2(k4_xboole_0('#skF_3', C_697), '#skF_1') | ~v2_tex_2('#skF_3', '#skF_1') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_23469, c_47583])).
% 16.90/8.61  tff(c_47804, plain, (![C_1354]: (v2_tex_2(k4_xboole_0('#skF_3', C_1354), '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_30, c_23156, c_47707])).
% 16.90/8.61  tff(c_47840, plain, (![B_4]: (v2_tex_2(k3_xboole_0('#skF_3', B_4), '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_4, c_47804])).
% 16.90/8.61  tff(c_23299, plain, (![A_673, B_674, C_675]: (k9_subset_1(A_673, B_674, C_675)=k3_xboole_0(B_674, C_675) | ~m1_subset_1(C_675, k1_zfmisc_1(A_673)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 16.90/8.61  tff(c_23312, plain, (![B_674]: (k9_subset_1(u1_struct_0('#skF_1'), B_674, '#skF_3')=k3_xboole_0(B_674, '#skF_3'))), inference(resolution, [status(thm)], [c_30, c_23299])).
% 16.90/8.61  tff(c_23324, plain, (~v2_tex_2(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_23312, c_26])).
% 16.90/8.61  tff(c_23325, plain, (~v2_tex_2(k3_xboole_0('#skF_3', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_23324])).
% 16.90/8.61  tff(c_47843, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_47840, c_23325])).
% 16.90/8.61  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 16.90/8.61  
% 16.90/8.61  Inference rules
% 16.90/8.61  ----------------------
% 16.90/8.61  #Ref     : 0
% 16.90/8.61  #Sup     : 11475
% 16.90/8.61  #Fact    : 0
% 16.90/8.61  #Define  : 0
% 16.90/8.61  #Split   : 2
% 16.90/8.61  #Chain   : 0
% 16.90/8.61  #Close   : 0
% 16.90/8.61  
% 16.90/8.61  Ordering : KBO
% 16.90/8.61  
% 16.90/8.61  Simplification rules
% 16.90/8.61  ----------------------
% 16.90/8.61  #Subsume      : 40
% 16.90/8.61  #Demod        : 6853
% 16.90/8.61  #Tautology    : 5357
% 16.90/8.61  #SimpNegUnit  : 2
% 16.90/8.61  #BackRed      : 4
% 16.90/8.61  
% 16.90/8.61  #Partial instantiations: 0
% 16.90/8.61  #Strategies tried      : 1
% 16.90/8.61  
% 16.90/8.61  Timing (in seconds)
% 16.90/8.61  ----------------------
% 16.90/8.62  Preprocessing        : 0.32
% 16.90/8.62  Parsing              : 0.18
% 16.90/8.62  CNF conversion       : 0.02
% 16.90/8.62  Main loop            : 7.51
% 16.90/8.62  Inferencing          : 1.23
% 16.90/8.62  Reduction            : 4.48
% 16.90/8.62  Demodulation         : 4.02
% 16.90/8.62  BG Simplification    : 0.17
% 16.90/8.62  Subsumption          : 1.28
% 16.90/8.62  Abstraction          : 0.25
% 16.90/8.62  MUC search           : 0.00
% 16.90/8.62  Cooper               : 0.00
% 16.90/8.62  Total                : 7.86
% 16.90/8.62  Index Insertion      : 0.00
% 16.90/8.62  Index Deletion       : 0.00
% 16.90/8.62  Index Matching       : 0.00
% 16.90/8.62  BG Taut test         : 0.00
%------------------------------------------------------------------------------
