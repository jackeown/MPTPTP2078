%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:43 EST 2020

% Result     : Theorem 8.23s
% Output     : CNFRefutation 8.23s
% Verified   : 
% Statistics : Number of formulae       :  143 ( 755 expanded)
%              Number of leaves         :   39 ( 274 expanded)
%              Depth                    :   12
%              Number of atoms          :  236 (1491 expanded)
%              Number of equality atoms :   78 ( 457 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tops_1 > v1_tops_1 > r1_tarski > m1_subset_1 > l1_struct_0 > l1_pre_topc > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(v2_tops_1,type,(
    v2_tops_1: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(v1_tops_1,type,(
    v1_tops_1: ( $i * $i ) > $o )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_104,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v2_tops_1(B,A)
            <=> k1_tops_1(A,B) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_tops_1)).

tff(f_69,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_59,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_35,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_85,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_tops_1(B,A)
          <=> k2_pre_topc(A,B) = k2_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tops_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_76,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k3_subset_1(u1_struct_0(A),k2_pre_topc(A,k3_subset_1(u1_struct_0(A),B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_1)).

tff(f_39,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_41,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_51,axiom,(
    ! [A] : k2_subset_1(A) = k3_subset_1(A,k1_subset_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_subset_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_94,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> v1_tops_1(k3_subset_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_1)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

tff(c_52,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_120,plain,(
    k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_46,plain,
    ( k1_tops_1('#skF_1','#skF_2') != k1_xboole_0
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_157,plain,(
    ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_46])).

tff(c_44,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_30,plain,(
    ! [A_23] :
      ( l1_struct_0(A_23)
      | ~ l1_pre_topc(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_115,plain,(
    ! [A_42] :
      ( u1_struct_0(A_42) = k2_struct_0(A_42)
      | ~ l1_struct_0(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_136,plain,(
    ! [A_46] :
      ( u1_struct_0(A_46) = k2_struct_0(A_46)
      | ~ l1_pre_topc(A_46) ) ),
    inference(resolution,[status(thm)],[c_30,c_115])).

tff(c_140,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_136])).

tff(c_42,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_141,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_42])).

tff(c_311,plain,(
    ! [A_59,B_60] :
      ( k4_xboole_0(A_59,B_60) = k3_subset_1(A_59,B_60)
      | ~ m1_subset_1(B_60,k1_zfmisc_1(A_59)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_318,plain,(
    k4_xboole_0(k2_struct_0('#skF_1'),'#skF_2') = k3_subset_1(k2_struct_0('#skF_1'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_141,c_311])).

tff(c_8,plain,(
    ! [A_7,B_8] : r1_tarski(k4_xboole_0(A_7,B_8),A_7) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_342,plain,(
    r1_tarski(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k2_struct_0('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_318,c_8])).

tff(c_24,plain,(
    ! [A_18,B_19] :
      ( m1_subset_1(A_18,k1_zfmisc_1(B_19))
      | ~ r1_tarski(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_904,plain,(
    ! [B_88,A_89] :
      ( v1_tops_1(B_88,A_89)
      | k2_pre_topc(A_89,B_88) != k2_struct_0(A_89)
      | ~ m1_subset_1(B_88,k1_zfmisc_1(u1_struct_0(A_89)))
      | ~ l1_pre_topc(A_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_2001,plain,(
    ! [A_126,A_127] :
      ( v1_tops_1(A_126,A_127)
      | k2_pre_topc(A_127,A_126) != k2_struct_0(A_127)
      | ~ l1_pre_topc(A_127)
      | ~ r1_tarski(A_126,u1_struct_0(A_127)) ) ),
    inference(resolution,[status(thm)],[c_24,c_904])).

tff(c_2023,plain,(
    ! [A_126] :
      ( v1_tops_1(A_126,'#skF_1')
      | k2_pre_topc('#skF_1',A_126) != k2_struct_0('#skF_1')
      | ~ l1_pre_topc('#skF_1')
      | ~ r1_tarski(A_126,k2_struct_0('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_140,c_2001])).

tff(c_2135,plain,(
    ! [A_131] :
      ( v1_tops_1(A_131,'#skF_1')
      | k2_pre_topc('#skF_1',A_131) != k2_struct_0('#skF_1')
      | ~ r1_tarski(A_131,k2_struct_0('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_2023])).

tff(c_2174,plain,
    ( v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) != k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_342,c_2135])).

tff(c_3067,plain,(
    k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) != k2_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_2174])).

tff(c_486,plain,(
    ! [A_68,B_69] :
      ( k3_subset_1(A_68,k3_subset_1(A_68,B_69)) = B_69
      | ~ m1_subset_1(B_69,k1_zfmisc_1(A_68)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_491,plain,(
    k3_subset_1(k2_struct_0('#skF_1'),k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_141,c_486])).

tff(c_1379,plain,(
    ! [A_110,B_111] :
      ( k3_subset_1(u1_struct_0(A_110),k2_pre_topc(A_110,k3_subset_1(u1_struct_0(A_110),B_111))) = k1_tops_1(A_110,B_111)
      | ~ m1_subset_1(B_111,k1_zfmisc_1(u1_struct_0(A_110)))
      | ~ l1_pre_topc(A_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_1414,plain,(
    ! [B_111] :
      ( k3_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),B_111))) = k1_tops_1('#skF_1',B_111)
      | ~ m1_subset_1(B_111,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_140,c_1379])).

tff(c_1451,plain,(
    ! [B_112] :
      ( k3_subset_1(k2_struct_0('#skF_1'),k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),B_112))) = k1_tops_1('#skF_1',B_112)
      | ~ m1_subset_1(B_112,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_140,c_140,c_1414])).

tff(c_1483,plain,
    ( k3_subset_1(k2_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2')) = k1_tops_1('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'))
    | ~ m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_491,c_1451])).

tff(c_2226,plain,(
    ~ m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_1483])).

tff(c_2230,plain,(
    ~ r1_tarski(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_24,c_2226])).

tff(c_2234,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_342,c_2230])).

tff(c_2236,plain,(
    m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_1483])).

tff(c_12,plain,(
    ! [A_11] : k1_subset_1(A_11) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_14,plain,(
    ! [A_12] : k2_subset_1(A_12) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_20,plain,(
    ! [A_17] : k3_subset_1(A_17,k1_subset_1(A_17)) = k2_subset_1(A_17) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_53,plain,(
    ! [A_17] : k3_subset_1(A_17,k1_subset_1(A_17)) = A_17 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_20])).

tff(c_54,plain,(
    ! [A_17] : k3_subset_1(A_17,k1_xboole_0) = A_17 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_53])).

tff(c_492,plain,(
    ! [B_19,A_18] :
      ( k3_subset_1(B_19,k3_subset_1(B_19,A_18)) = A_18
      | ~ r1_tarski(A_18,B_19) ) ),
    inference(resolution,[status(thm)],[c_24,c_486])).

tff(c_8914,plain,(
    ! [A_232,A_233] :
      ( k3_subset_1(u1_struct_0(A_232),k2_pre_topc(A_232,A_233)) = k1_tops_1(A_232,k3_subset_1(u1_struct_0(A_232),A_233))
      | ~ m1_subset_1(k3_subset_1(u1_struct_0(A_232),A_233),k1_zfmisc_1(u1_struct_0(A_232)))
      | ~ l1_pre_topc(A_232)
      | ~ r1_tarski(A_233,u1_struct_0(A_232)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_492,c_1379])).

tff(c_8941,plain,(
    ! [A_233] :
      ( k3_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1',A_233)) = k1_tops_1('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),A_233))
      | ~ m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'),A_233),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ r1_tarski(A_233,u1_struct_0('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_140,c_8914])).

tff(c_9212,plain,(
    ! [A_236] :
      ( k3_subset_1(k2_struct_0('#skF_1'),k2_pre_topc('#skF_1',A_236)) = k1_tops_1('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),A_236))
      | ~ m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'),A_236),k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ r1_tarski(A_236,k2_struct_0('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_44,c_140,c_140,c_140,c_8941])).

tff(c_9261,plain,
    ( k3_subset_1(k2_struct_0('#skF_1'),k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'))) = k1_tops_1('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1')))
    | ~ r1_tarski(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k2_struct_0('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_491,c_9212])).

tff(c_9292,plain,(
    k3_subset_1(k2_struct_0('#skF_1'),k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'))) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_342,c_141,c_120,c_491,c_9261])).

tff(c_565,plain,(
    ! [A_72,B_73] :
      ( m1_subset_1(k2_pre_topc(A_72,B_73),k1_zfmisc_1(u1_struct_0(A_72)))
      | ~ m1_subset_1(B_73,k1_zfmisc_1(u1_struct_0(A_72)))
      | ~ l1_pre_topc(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_18,plain,(
    ! [A_15,B_16] :
      ( k3_subset_1(A_15,k3_subset_1(A_15,B_16)) = B_16
      | ~ m1_subset_1(B_16,k1_zfmisc_1(A_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_3822,plain,(
    ! [A_162,B_163] :
      ( k3_subset_1(u1_struct_0(A_162),k3_subset_1(u1_struct_0(A_162),k2_pre_topc(A_162,B_163))) = k2_pre_topc(A_162,B_163)
      | ~ m1_subset_1(B_163,k1_zfmisc_1(u1_struct_0(A_162)))
      | ~ l1_pre_topc(A_162) ) ),
    inference(resolution,[status(thm)],[c_565,c_18])).

tff(c_3858,plain,(
    ! [B_163] :
      ( k3_subset_1(k2_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1',B_163))) = k2_pre_topc('#skF_1',B_163)
      | ~ m1_subset_1(B_163,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_140,c_3822])).

tff(c_3868,plain,(
    ! [B_163] :
      ( k3_subset_1(k2_struct_0('#skF_1'),k3_subset_1(k2_struct_0('#skF_1'),k2_pre_topc('#skF_1',B_163))) = k2_pre_topc('#skF_1',B_163)
      | ~ m1_subset_1(B_163,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_140,c_140,c_3858])).

tff(c_9326,plain,
    ( k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = k3_subset_1(k2_struct_0('#skF_1'),k1_xboole_0)
    | ~ m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_9292,c_3868])).

tff(c_9364,plain,(
    k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2236,c_54,c_9326])).

tff(c_9366,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3067,c_9364])).

tff(c_9367,plain,(
    v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_2174])).

tff(c_1240,plain,(
    ! [B_103,A_104] :
      ( v2_tops_1(B_103,A_104)
      | ~ v1_tops_1(k3_subset_1(u1_struct_0(A_104),B_103),A_104)
      | ~ m1_subset_1(B_103,k1_zfmisc_1(u1_struct_0(A_104)))
      | ~ l1_pre_topc(A_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_1254,plain,(
    ! [B_103] :
      ( v2_tops_1(B_103,'#skF_1')
      | ~ v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),B_103),'#skF_1')
      | ~ m1_subset_1(B_103,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_140,c_1240])).

tff(c_1261,plain,(
    ! [B_103] :
      ( v2_tops_1(B_103,'#skF_1')
      | ~ v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),B_103),'#skF_1')
      | ~ m1_subset_1(B_103,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_140,c_1254])).

tff(c_9371,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_9367,c_1261])).

tff(c_9374,plain,(
    v2_tops_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_9371])).

tff(c_9376,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_157,c_9374])).

tff(c_9378,plain,(
    k1_tops_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_9392,plain,(
    ! [A_240] :
      ( u1_struct_0(A_240) = k2_struct_0(A_240)
      | ~ l1_pre_topc(A_240) ) ),
    inference(resolution,[status(thm)],[c_30,c_115])).

tff(c_9396,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_9392])).

tff(c_9397,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9396,c_42])).

tff(c_9379,plain,(
    ! [A_237,B_238] : k4_xboole_0(A_237,k2_xboole_0(A_237,B_238)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_9384,plain,(
    ! [A_237] : r1_tarski(k1_xboole_0,A_237) ),
    inference(superposition,[status(thm),theory(equality)],[c_9379,c_8])).

tff(c_9553,plain,(
    ! [A_253,B_254] :
      ( k3_subset_1(A_253,k3_subset_1(A_253,B_254)) = B_254
      | ~ m1_subset_1(B_254,k1_zfmisc_1(A_253)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_9812,plain,(
    ! [B_266,A_267] :
      ( k3_subset_1(B_266,k3_subset_1(B_266,A_267)) = A_267
      | ~ r1_tarski(A_267,B_266) ) ),
    inference(resolution,[status(thm)],[c_24,c_9553])).

tff(c_9836,plain,(
    ! [A_17] :
      ( k3_subset_1(A_17,A_17) = k1_xboole_0
      | ~ r1_tarski(k1_xboole_0,A_17) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_9812])).

tff(c_9851,plain,(
    ! [A_17] : k3_subset_1(A_17,A_17) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_9384,c_9836])).

tff(c_9377,plain,(
    v2_tops_1('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_10347,plain,(
    ! [A_292,B_293] :
      ( v1_tops_1(k3_subset_1(u1_struct_0(A_292),B_293),A_292)
      | ~ v2_tops_1(B_293,A_292)
      | ~ m1_subset_1(B_293,k1_zfmisc_1(u1_struct_0(A_292)))
      | ~ l1_pre_topc(A_292) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_10358,plain,(
    ! [B_293] :
      ( v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),B_293),'#skF_1')
      | ~ v2_tops_1(B_293,'#skF_1')
      | ~ m1_subset_1(B_293,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9396,c_10347])).

tff(c_10364,plain,(
    ! [B_293] :
      ( v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),B_293),'#skF_1')
      | ~ v2_tops_1(B_293,'#skF_1')
      | ~ m1_subset_1(B_293,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_9396,c_10358])).

tff(c_9634,plain,(
    ! [A_258,B_259] :
      ( k4_xboole_0(A_258,B_259) = k3_subset_1(A_258,B_259)
      | ~ m1_subset_1(B_259,k1_zfmisc_1(A_258)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_9642,plain,(
    k4_xboole_0(k2_struct_0('#skF_1'),'#skF_2') = k3_subset_1(k2_struct_0('#skF_1'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_9397,c_9634])).

tff(c_9741,plain,(
    r1_tarski(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k2_struct_0('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_9642,c_8])).

tff(c_9559,plain,(
    k3_subset_1(k2_struct_0('#skF_1'),k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_9397,c_9553])).

tff(c_11004,plain,(
    ! [A_311,B_312] :
      ( k3_subset_1(u1_struct_0(A_311),k2_pre_topc(A_311,k3_subset_1(u1_struct_0(A_311),B_312))) = k1_tops_1(A_311,B_312)
      | ~ m1_subset_1(B_312,k1_zfmisc_1(u1_struct_0(A_311)))
      | ~ l1_pre_topc(A_311) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_11039,plain,(
    ! [B_312] :
      ( k3_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),B_312))) = k1_tops_1('#skF_1',B_312)
      | ~ m1_subset_1(B_312,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9396,c_11004])).

tff(c_11126,plain,(
    ! [B_315] :
      ( k3_subset_1(k2_struct_0('#skF_1'),k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),B_315))) = k1_tops_1('#skF_1',B_315)
      | ~ m1_subset_1(B_315,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_9396,c_9396,c_11039])).

tff(c_11158,plain,
    ( k3_subset_1(k2_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2')) = k1_tops_1('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'))
    | ~ m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_9559,c_11126])).

tff(c_11320,plain,(
    ~ m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_11158])).

tff(c_11323,plain,(
    ~ r1_tarski(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_24,c_11320])).

tff(c_11327,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_9741,c_11323])).

tff(c_11329,plain,(
    m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_11158])).

tff(c_9985,plain,(
    ! [B_275,A_276] :
      ( v1_tops_1(B_275,A_276)
      | k2_pre_topc(A_276,B_275) != k2_struct_0(A_276)
      | ~ m1_subset_1(B_275,k1_zfmisc_1(u1_struct_0(A_276)))
      | ~ l1_pre_topc(A_276) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_9995,plain,(
    ! [B_275] :
      ( v1_tops_1(B_275,'#skF_1')
      | k2_pre_topc('#skF_1',B_275) != k2_struct_0('#skF_1')
      | ~ m1_subset_1(B_275,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9396,c_9985])).

tff(c_9999,plain,(
    ! [B_275] :
      ( v1_tops_1(B_275,'#skF_1')
      | k2_pre_topc('#skF_1',B_275) != k2_struct_0('#skF_1')
      | ~ m1_subset_1(B_275,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_9995])).

tff(c_11345,plain,
    ( v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) != k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_11329,c_9999])).

tff(c_12066,plain,(
    k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) != k2_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_11345])).

tff(c_10106,plain,(
    ! [A_281,B_282] :
      ( k2_pre_topc(A_281,B_282) = k2_struct_0(A_281)
      | ~ v1_tops_1(B_282,A_281)
      | ~ m1_subset_1(B_282,k1_zfmisc_1(u1_struct_0(A_281)))
      | ~ l1_pre_topc(A_281) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_10116,plain,(
    ! [B_282] :
      ( k2_pre_topc('#skF_1',B_282) = k2_struct_0('#skF_1')
      | ~ v1_tops_1(B_282,'#skF_1')
      | ~ m1_subset_1(B_282,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9396,c_10106])).

tff(c_10174,plain,(
    ! [B_285] :
      ( k2_pre_topc('#skF_1',B_285) = k2_struct_0('#skF_1')
      | ~ v1_tops_1(B_285,'#skF_1')
      | ~ m1_subset_1(B_285,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_10116])).

tff(c_11215,plain,(
    ! [A_318] :
      ( k2_pre_topc('#skF_1',A_318) = k2_struct_0('#skF_1')
      | ~ v1_tops_1(A_318,'#skF_1')
      | ~ r1_tarski(A_318,k2_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_24,c_10174])).

tff(c_12106,plain,(
    ! [B_342] :
      ( k2_pre_topc('#skF_1',k4_xboole_0(k2_struct_0('#skF_1'),B_342)) = k2_struct_0('#skF_1')
      | ~ v1_tops_1(k4_xboole_0(k2_struct_0('#skF_1'),B_342),'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_8,c_11215])).

tff(c_12131,plain,
    ( k2_pre_topc('#skF_1',k4_xboole_0(k2_struct_0('#skF_1'),'#skF_2')) = k2_struct_0('#skF_1')
    | ~ v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_9642,c_12106])).

tff(c_12145,plain,
    ( k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = k2_struct_0('#skF_1')
    | ~ v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9642,c_12131])).

tff(c_12146,plain,(
    ~ v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_12066,c_12145])).

tff(c_12151,plain,
    ( ~ v2_tops_1('#skF_2','#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_10364,c_12146])).

tff(c_12155,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_9397,c_9377,c_12151])).

tff(c_12157,plain,(
    k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = k2_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_11345])).

tff(c_11049,plain,(
    ! [B_312] :
      ( k3_subset_1(k2_struct_0('#skF_1'),k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),B_312))) = k1_tops_1('#skF_1',B_312)
      | ~ m1_subset_1(B_312,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_9396,c_9396,c_11039])).

tff(c_12182,plain,
    ( k3_subset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_1')) = k1_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_12157,c_11049])).

tff(c_12197,plain,(
    k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_9397,c_9851,c_12182])).

tff(c_12199,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_9378,c_12197])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n025.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 11:29:35 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.23/3.03  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.23/3.05  
% 8.23/3.05  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.23/3.05  %$ v2_tops_1 > v1_tops_1 > r1_tarski > m1_subset_1 > l1_struct_0 > l1_pre_topc > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_2 > #skF_1
% 8.23/3.05  
% 8.23/3.05  %Foreground sorts:
% 8.23/3.05  
% 8.23/3.05  
% 8.23/3.05  %Background operators:
% 8.23/3.05  
% 8.23/3.05  
% 8.23/3.05  %Foreground operators:
% 8.23/3.05  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.23/3.05  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 8.23/3.05  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.23/3.05  tff(v2_tops_1, type, v2_tops_1: ($i * $i) > $o).
% 8.23/3.05  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 8.23/3.05  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 8.23/3.05  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.23/3.05  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 8.23/3.05  tff(v1_tops_1, type, v1_tops_1: ($i * $i) > $o).
% 8.23/3.05  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 8.23/3.05  tff('#skF_2', type, '#skF_2': $i).
% 8.23/3.05  tff('#skF_1', type, '#skF_1': $i).
% 8.23/3.05  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.23/3.05  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 8.23/3.05  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.23/3.05  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.23/3.05  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 8.23/3.05  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.23/3.05  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 8.23/3.05  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 8.23/3.05  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 8.23/3.05  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 8.23/3.05  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 8.23/3.05  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.23/3.05  
% 8.23/3.07  tff(f_104, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (k1_tops_1(A, B) = k1_xboole_0)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t84_tops_1)).
% 8.23/3.07  tff(f_69, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 8.23/3.07  tff(f_59, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 8.23/3.07  tff(f_45, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 8.23/3.07  tff(f_35, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 8.23/3.07  tff(f_55, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 8.23/3.07  tff(f_85, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) <=> (k2_pre_topc(A, B) = k2_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tops_1)).
% 8.23/3.07  tff(f_49, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 8.23/3.07  tff(f_76, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k3_subset_1(u1_struct_0(A), k2_pre_topc(A, k3_subset_1(u1_struct_0(A), B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tops_1)).
% 8.23/3.07  tff(f_39, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_subset_1)).
% 8.23/3.07  tff(f_41, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 8.23/3.07  tff(f_51, axiom, (![A]: (k2_subset_1(A) = k3_subset_1(A, k1_subset_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_subset_1)).
% 8.23/3.07  tff(f_65, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 8.23/3.07  tff(f_94, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> v1_tops_1(k3_subset_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tops_1)).
% 8.23/3.07  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 8.23/3.07  tff(c_52, plain, (v2_tops_1('#skF_2', '#skF_1') | k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_104])).
% 8.23/3.07  tff(c_120, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_52])).
% 8.23/3.07  tff(c_46, plain, (k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0 | ~v2_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_104])).
% 8.23/3.07  tff(c_157, plain, (~v2_tops_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_120, c_46])).
% 8.23/3.07  tff(c_44, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_104])).
% 8.23/3.07  tff(c_30, plain, (![A_23]: (l1_struct_0(A_23) | ~l1_pre_topc(A_23))), inference(cnfTransformation, [status(thm)], [f_69])).
% 8.23/3.07  tff(c_115, plain, (![A_42]: (u1_struct_0(A_42)=k2_struct_0(A_42) | ~l1_struct_0(A_42))), inference(cnfTransformation, [status(thm)], [f_59])).
% 8.23/3.07  tff(c_136, plain, (![A_46]: (u1_struct_0(A_46)=k2_struct_0(A_46) | ~l1_pre_topc(A_46))), inference(resolution, [status(thm)], [c_30, c_115])).
% 8.23/3.07  tff(c_140, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_44, c_136])).
% 8.23/3.07  tff(c_42, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_104])).
% 8.23/3.07  tff(c_141, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_140, c_42])).
% 8.23/3.07  tff(c_311, plain, (![A_59, B_60]: (k4_xboole_0(A_59, B_60)=k3_subset_1(A_59, B_60) | ~m1_subset_1(B_60, k1_zfmisc_1(A_59)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.23/3.07  tff(c_318, plain, (k4_xboole_0(k2_struct_0('#skF_1'), '#skF_2')=k3_subset_1(k2_struct_0('#skF_1'), '#skF_2')), inference(resolution, [status(thm)], [c_141, c_311])).
% 8.23/3.07  tff(c_8, plain, (![A_7, B_8]: (r1_tarski(k4_xboole_0(A_7, B_8), A_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 8.23/3.07  tff(c_342, plain, (r1_tarski(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), k2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_318, c_8])).
% 8.23/3.07  tff(c_24, plain, (![A_18, B_19]: (m1_subset_1(A_18, k1_zfmisc_1(B_19)) | ~r1_tarski(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_55])).
% 8.23/3.07  tff(c_904, plain, (![B_88, A_89]: (v1_tops_1(B_88, A_89) | k2_pre_topc(A_89, B_88)!=k2_struct_0(A_89) | ~m1_subset_1(B_88, k1_zfmisc_1(u1_struct_0(A_89))) | ~l1_pre_topc(A_89))), inference(cnfTransformation, [status(thm)], [f_85])).
% 8.23/3.07  tff(c_2001, plain, (![A_126, A_127]: (v1_tops_1(A_126, A_127) | k2_pre_topc(A_127, A_126)!=k2_struct_0(A_127) | ~l1_pre_topc(A_127) | ~r1_tarski(A_126, u1_struct_0(A_127)))), inference(resolution, [status(thm)], [c_24, c_904])).
% 8.23/3.07  tff(c_2023, plain, (![A_126]: (v1_tops_1(A_126, '#skF_1') | k2_pre_topc('#skF_1', A_126)!=k2_struct_0('#skF_1') | ~l1_pre_topc('#skF_1') | ~r1_tarski(A_126, k2_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_140, c_2001])).
% 8.23/3.07  tff(c_2135, plain, (![A_131]: (v1_tops_1(A_131, '#skF_1') | k2_pre_topc('#skF_1', A_131)!=k2_struct_0('#skF_1') | ~r1_tarski(A_131, k2_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_2023])).
% 8.23/3.07  tff(c_2174, plain, (v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))!=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_342, c_2135])).
% 8.23/3.07  tff(c_3067, plain, (k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))!=k2_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_2174])).
% 8.23/3.07  tff(c_486, plain, (![A_68, B_69]: (k3_subset_1(A_68, k3_subset_1(A_68, B_69))=B_69 | ~m1_subset_1(B_69, k1_zfmisc_1(A_68)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 8.23/3.07  tff(c_491, plain, (k3_subset_1(k2_struct_0('#skF_1'), k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))='#skF_2'), inference(resolution, [status(thm)], [c_141, c_486])).
% 8.23/3.07  tff(c_1379, plain, (![A_110, B_111]: (k3_subset_1(u1_struct_0(A_110), k2_pre_topc(A_110, k3_subset_1(u1_struct_0(A_110), B_111)))=k1_tops_1(A_110, B_111) | ~m1_subset_1(B_111, k1_zfmisc_1(u1_struct_0(A_110))) | ~l1_pre_topc(A_110))), inference(cnfTransformation, [status(thm)], [f_76])).
% 8.23/3.07  tff(c_1414, plain, (![B_111]: (k3_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), B_111)))=k1_tops_1('#skF_1', B_111) | ~m1_subset_1(B_111, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_140, c_1379])).
% 8.23/3.07  tff(c_1451, plain, (![B_112]: (k3_subset_1(k2_struct_0('#skF_1'), k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), B_112)))=k1_tops_1('#skF_1', B_112) | ~m1_subset_1(B_112, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_140, c_140, c_1414])).
% 8.23/3.07  tff(c_1483, plain, (k3_subset_1(k2_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2')) | ~m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_491, c_1451])).
% 8.23/3.07  tff(c_2226, plain, (~m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_1483])).
% 8.23/3.07  tff(c_2230, plain, (~r1_tarski(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_24, c_2226])).
% 8.23/3.07  tff(c_2234, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_342, c_2230])).
% 8.23/3.07  tff(c_2236, plain, (m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_1483])).
% 8.23/3.07  tff(c_12, plain, (![A_11]: (k1_subset_1(A_11)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.23/3.07  tff(c_14, plain, (![A_12]: (k2_subset_1(A_12)=A_12)), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.23/3.07  tff(c_20, plain, (![A_17]: (k3_subset_1(A_17, k1_subset_1(A_17))=k2_subset_1(A_17))), inference(cnfTransformation, [status(thm)], [f_51])).
% 8.23/3.07  tff(c_53, plain, (![A_17]: (k3_subset_1(A_17, k1_subset_1(A_17))=A_17)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_20])).
% 8.23/3.07  tff(c_54, plain, (![A_17]: (k3_subset_1(A_17, k1_xboole_0)=A_17)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_53])).
% 8.23/3.07  tff(c_492, plain, (![B_19, A_18]: (k3_subset_1(B_19, k3_subset_1(B_19, A_18))=A_18 | ~r1_tarski(A_18, B_19))), inference(resolution, [status(thm)], [c_24, c_486])).
% 8.23/3.07  tff(c_8914, plain, (![A_232, A_233]: (k3_subset_1(u1_struct_0(A_232), k2_pre_topc(A_232, A_233))=k1_tops_1(A_232, k3_subset_1(u1_struct_0(A_232), A_233)) | ~m1_subset_1(k3_subset_1(u1_struct_0(A_232), A_233), k1_zfmisc_1(u1_struct_0(A_232))) | ~l1_pre_topc(A_232) | ~r1_tarski(A_233, u1_struct_0(A_232)))), inference(superposition, [status(thm), theory('equality')], [c_492, c_1379])).
% 8.23/3.07  tff(c_8941, plain, (![A_233]: (k3_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', A_233))=k1_tops_1('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), A_233)) | ~m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'), A_233), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~r1_tarski(A_233, u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_140, c_8914])).
% 8.23/3.07  tff(c_9212, plain, (![A_236]: (k3_subset_1(k2_struct_0('#skF_1'), k2_pre_topc('#skF_1', A_236))=k1_tops_1('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), A_236)) | ~m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'), A_236), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~r1_tarski(A_236, k2_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_140, c_44, c_140, c_140, c_140, c_8941])).
% 8.23/3.07  tff(c_9261, plain, (k3_subset_1(k2_struct_0('#skF_1'), k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2')))=k1_tops_1('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~r1_tarski(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), k2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_491, c_9212])).
% 8.23/3.07  tff(c_9292, plain, (k3_subset_1(k2_struct_0('#skF_1'), k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2')))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_342, c_141, c_120, c_491, c_9261])).
% 8.23/3.07  tff(c_565, plain, (![A_72, B_73]: (m1_subset_1(k2_pre_topc(A_72, B_73), k1_zfmisc_1(u1_struct_0(A_72))) | ~m1_subset_1(B_73, k1_zfmisc_1(u1_struct_0(A_72))) | ~l1_pre_topc(A_72))), inference(cnfTransformation, [status(thm)], [f_65])).
% 8.23/3.07  tff(c_18, plain, (![A_15, B_16]: (k3_subset_1(A_15, k3_subset_1(A_15, B_16))=B_16 | ~m1_subset_1(B_16, k1_zfmisc_1(A_15)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 8.23/3.07  tff(c_3822, plain, (![A_162, B_163]: (k3_subset_1(u1_struct_0(A_162), k3_subset_1(u1_struct_0(A_162), k2_pre_topc(A_162, B_163)))=k2_pre_topc(A_162, B_163) | ~m1_subset_1(B_163, k1_zfmisc_1(u1_struct_0(A_162))) | ~l1_pre_topc(A_162))), inference(resolution, [status(thm)], [c_565, c_18])).
% 8.23/3.07  tff(c_3858, plain, (![B_163]: (k3_subset_1(k2_struct_0('#skF_1'), k3_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', B_163)))=k2_pre_topc('#skF_1', B_163) | ~m1_subset_1(B_163, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_140, c_3822])).
% 8.23/3.07  tff(c_3868, plain, (![B_163]: (k3_subset_1(k2_struct_0('#skF_1'), k3_subset_1(k2_struct_0('#skF_1'), k2_pre_topc('#skF_1', B_163)))=k2_pre_topc('#skF_1', B_163) | ~m1_subset_1(B_163, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_140, c_140, c_3858])).
% 8.23/3.07  tff(c_9326, plain, (k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))=k3_subset_1(k2_struct_0('#skF_1'), k1_xboole_0) | ~m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_9292, c_3868])).
% 8.23/3.07  tff(c_9364, plain, (k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2236, c_54, c_9326])).
% 8.23/3.07  tff(c_9366, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3067, c_9364])).
% 8.23/3.07  tff(c_9367, plain, (v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(splitRight, [status(thm)], [c_2174])).
% 8.23/3.07  tff(c_1240, plain, (![B_103, A_104]: (v2_tops_1(B_103, A_104) | ~v1_tops_1(k3_subset_1(u1_struct_0(A_104), B_103), A_104) | ~m1_subset_1(B_103, k1_zfmisc_1(u1_struct_0(A_104))) | ~l1_pre_topc(A_104))), inference(cnfTransformation, [status(thm)], [f_94])).
% 8.23/3.07  tff(c_1254, plain, (![B_103]: (v2_tops_1(B_103, '#skF_1') | ~v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), B_103), '#skF_1') | ~m1_subset_1(B_103, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_140, c_1240])).
% 8.23/3.07  tff(c_1261, plain, (![B_103]: (v2_tops_1(B_103, '#skF_1') | ~v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), B_103), '#skF_1') | ~m1_subset_1(B_103, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_140, c_1254])).
% 8.23/3.07  tff(c_9371, plain, (v2_tops_1('#skF_2', '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_9367, c_1261])).
% 8.23/3.07  tff(c_9374, plain, (v2_tops_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_141, c_9371])).
% 8.23/3.07  tff(c_9376, plain, $false, inference(negUnitSimplification, [status(thm)], [c_157, c_9374])).
% 8.23/3.07  tff(c_9378, plain, (k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_52])).
% 8.23/3.07  tff(c_9392, plain, (![A_240]: (u1_struct_0(A_240)=k2_struct_0(A_240) | ~l1_pre_topc(A_240))), inference(resolution, [status(thm)], [c_30, c_115])).
% 8.23/3.07  tff(c_9396, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_44, c_9392])).
% 8.23/3.07  tff(c_9397, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_9396, c_42])).
% 8.23/3.07  tff(c_9379, plain, (![A_237, B_238]: (k4_xboole_0(A_237, k2_xboole_0(A_237, B_238))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 8.23/3.07  tff(c_9384, plain, (![A_237]: (r1_tarski(k1_xboole_0, A_237))), inference(superposition, [status(thm), theory('equality')], [c_9379, c_8])).
% 8.23/3.07  tff(c_9553, plain, (![A_253, B_254]: (k3_subset_1(A_253, k3_subset_1(A_253, B_254))=B_254 | ~m1_subset_1(B_254, k1_zfmisc_1(A_253)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 8.23/3.07  tff(c_9812, plain, (![B_266, A_267]: (k3_subset_1(B_266, k3_subset_1(B_266, A_267))=A_267 | ~r1_tarski(A_267, B_266))), inference(resolution, [status(thm)], [c_24, c_9553])).
% 8.23/3.07  tff(c_9836, plain, (![A_17]: (k3_subset_1(A_17, A_17)=k1_xboole_0 | ~r1_tarski(k1_xboole_0, A_17))), inference(superposition, [status(thm), theory('equality')], [c_54, c_9812])).
% 8.23/3.07  tff(c_9851, plain, (![A_17]: (k3_subset_1(A_17, A_17)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_9384, c_9836])).
% 8.23/3.07  tff(c_9377, plain, (v2_tops_1('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_52])).
% 8.23/3.07  tff(c_10347, plain, (![A_292, B_293]: (v1_tops_1(k3_subset_1(u1_struct_0(A_292), B_293), A_292) | ~v2_tops_1(B_293, A_292) | ~m1_subset_1(B_293, k1_zfmisc_1(u1_struct_0(A_292))) | ~l1_pre_topc(A_292))), inference(cnfTransformation, [status(thm)], [f_94])).
% 8.23/3.07  tff(c_10358, plain, (![B_293]: (v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), B_293), '#skF_1') | ~v2_tops_1(B_293, '#skF_1') | ~m1_subset_1(B_293, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_9396, c_10347])).
% 8.23/3.07  tff(c_10364, plain, (![B_293]: (v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), B_293), '#skF_1') | ~v2_tops_1(B_293, '#skF_1') | ~m1_subset_1(B_293, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_9396, c_10358])).
% 8.23/3.07  tff(c_9634, plain, (![A_258, B_259]: (k4_xboole_0(A_258, B_259)=k3_subset_1(A_258, B_259) | ~m1_subset_1(B_259, k1_zfmisc_1(A_258)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.23/3.07  tff(c_9642, plain, (k4_xboole_0(k2_struct_0('#skF_1'), '#skF_2')=k3_subset_1(k2_struct_0('#skF_1'), '#skF_2')), inference(resolution, [status(thm)], [c_9397, c_9634])).
% 8.23/3.07  tff(c_9741, plain, (r1_tarski(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), k2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_9642, c_8])).
% 8.23/3.07  tff(c_9559, plain, (k3_subset_1(k2_struct_0('#skF_1'), k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))='#skF_2'), inference(resolution, [status(thm)], [c_9397, c_9553])).
% 8.23/3.07  tff(c_11004, plain, (![A_311, B_312]: (k3_subset_1(u1_struct_0(A_311), k2_pre_topc(A_311, k3_subset_1(u1_struct_0(A_311), B_312)))=k1_tops_1(A_311, B_312) | ~m1_subset_1(B_312, k1_zfmisc_1(u1_struct_0(A_311))) | ~l1_pre_topc(A_311))), inference(cnfTransformation, [status(thm)], [f_76])).
% 8.23/3.07  tff(c_11039, plain, (![B_312]: (k3_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), B_312)))=k1_tops_1('#skF_1', B_312) | ~m1_subset_1(B_312, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_9396, c_11004])).
% 8.23/3.07  tff(c_11126, plain, (![B_315]: (k3_subset_1(k2_struct_0('#skF_1'), k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), B_315)))=k1_tops_1('#skF_1', B_315) | ~m1_subset_1(B_315, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_9396, c_9396, c_11039])).
% 8.23/3.07  tff(c_11158, plain, (k3_subset_1(k2_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2')) | ~m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_9559, c_11126])).
% 8.23/3.07  tff(c_11320, plain, (~m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_11158])).
% 8.23/3.07  tff(c_11323, plain, (~r1_tarski(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_24, c_11320])).
% 8.23/3.07  tff(c_11327, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_9741, c_11323])).
% 8.23/3.07  tff(c_11329, plain, (m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_11158])).
% 8.23/3.07  tff(c_9985, plain, (![B_275, A_276]: (v1_tops_1(B_275, A_276) | k2_pre_topc(A_276, B_275)!=k2_struct_0(A_276) | ~m1_subset_1(B_275, k1_zfmisc_1(u1_struct_0(A_276))) | ~l1_pre_topc(A_276))), inference(cnfTransformation, [status(thm)], [f_85])).
% 8.23/3.07  tff(c_9995, plain, (![B_275]: (v1_tops_1(B_275, '#skF_1') | k2_pre_topc('#skF_1', B_275)!=k2_struct_0('#skF_1') | ~m1_subset_1(B_275, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_9396, c_9985])).
% 8.23/3.07  tff(c_9999, plain, (![B_275]: (v1_tops_1(B_275, '#skF_1') | k2_pre_topc('#skF_1', B_275)!=k2_struct_0('#skF_1') | ~m1_subset_1(B_275, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_9995])).
% 8.23/3.07  tff(c_11345, plain, (v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))!=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_11329, c_9999])).
% 8.23/3.07  tff(c_12066, plain, (k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))!=k2_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_11345])).
% 8.23/3.07  tff(c_10106, plain, (![A_281, B_282]: (k2_pre_topc(A_281, B_282)=k2_struct_0(A_281) | ~v1_tops_1(B_282, A_281) | ~m1_subset_1(B_282, k1_zfmisc_1(u1_struct_0(A_281))) | ~l1_pre_topc(A_281))), inference(cnfTransformation, [status(thm)], [f_85])).
% 8.23/3.07  tff(c_10116, plain, (![B_282]: (k2_pre_topc('#skF_1', B_282)=k2_struct_0('#skF_1') | ~v1_tops_1(B_282, '#skF_1') | ~m1_subset_1(B_282, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_9396, c_10106])).
% 8.23/3.07  tff(c_10174, plain, (![B_285]: (k2_pre_topc('#skF_1', B_285)=k2_struct_0('#skF_1') | ~v1_tops_1(B_285, '#skF_1') | ~m1_subset_1(B_285, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_10116])).
% 8.23/3.07  tff(c_11215, plain, (![A_318]: (k2_pre_topc('#skF_1', A_318)=k2_struct_0('#skF_1') | ~v1_tops_1(A_318, '#skF_1') | ~r1_tarski(A_318, k2_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_24, c_10174])).
% 8.23/3.07  tff(c_12106, plain, (![B_342]: (k2_pre_topc('#skF_1', k4_xboole_0(k2_struct_0('#skF_1'), B_342))=k2_struct_0('#skF_1') | ~v1_tops_1(k4_xboole_0(k2_struct_0('#skF_1'), B_342), '#skF_1'))), inference(resolution, [status(thm)], [c_8, c_11215])).
% 8.23/3.07  tff(c_12131, plain, (k2_pre_topc('#skF_1', k4_xboole_0(k2_struct_0('#skF_1'), '#skF_2'))=k2_struct_0('#skF_1') | ~v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_9642, c_12106])).
% 8.23/3.07  tff(c_12145, plain, (k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))=k2_struct_0('#skF_1') | ~v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_9642, c_12131])).
% 8.23/3.07  tff(c_12146, plain, (~v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_12066, c_12145])).
% 8.23/3.07  tff(c_12151, plain, (~v2_tops_1('#skF_2', '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_10364, c_12146])).
% 8.23/3.07  tff(c_12155, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_9397, c_9377, c_12151])).
% 8.23/3.07  tff(c_12157, plain, (k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))=k2_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_11345])).
% 8.23/3.07  tff(c_11049, plain, (![B_312]: (k3_subset_1(k2_struct_0('#skF_1'), k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), B_312)))=k1_tops_1('#skF_1', B_312) | ~m1_subset_1(B_312, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_9396, c_9396, c_11039])).
% 8.23/3.07  tff(c_12182, plain, (k3_subset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_1'))=k1_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_12157, c_11049])).
% 8.23/3.07  tff(c_12197, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_9397, c_9851, c_12182])).
% 8.23/3.07  tff(c_12199, plain, $false, inference(negUnitSimplification, [status(thm)], [c_9378, c_12197])).
% 8.23/3.07  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.23/3.07  
% 8.23/3.07  Inference rules
% 8.23/3.07  ----------------------
% 8.23/3.07  #Ref     : 0
% 8.23/3.07  #Sup     : 2911
% 8.23/3.07  #Fact    : 0
% 8.23/3.07  #Define  : 0
% 8.23/3.07  #Split   : 25
% 8.23/3.07  #Chain   : 0
% 8.23/3.07  #Close   : 0
% 8.23/3.07  
% 8.23/3.07  Ordering : KBO
% 8.23/3.07  
% 8.23/3.07  Simplification rules
% 8.23/3.07  ----------------------
% 8.23/3.07  #Subsume      : 215
% 8.23/3.07  #Demod        : 4718
% 8.23/3.07  #Tautology    : 1806
% 8.23/3.07  #SimpNegUnit  : 114
% 8.23/3.07  #BackRed      : 46
% 8.23/3.07  
% 8.23/3.07  #Partial instantiations: 0
% 8.23/3.07  #Strategies tried      : 1
% 8.23/3.07  
% 8.23/3.07  Timing (in seconds)
% 8.23/3.07  ----------------------
% 8.23/3.07  Preprocessing        : 0.32
% 8.23/3.07  Parsing              : 0.17
% 8.23/3.07  CNF conversion       : 0.02
% 8.23/3.07  Main loop            : 1.96
% 8.23/3.07  Inferencing          : 0.54
% 8.23/3.07  Reduction            : 0.93
% 8.23/3.07  Demodulation         : 0.75
% 8.23/3.07  BG Simplification    : 0.06
% 8.23/3.07  Subsumption          : 0.30
% 8.23/3.07  Abstraction          : 0.10
% 8.23/3.07  MUC search           : 0.00
% 8.23/3.07  Cooper               : 0.00
% 8.23/3.07  Total                : 2.32
% 8.23/3.08  Index Insertion      : 0.00
% 8.23/3.08  Index Deletion       : 0.00
% 8.23/3.08  Index Matching       : 0.00
% 8.23/3.08  BG Taut test         : 0.00
%------------------------------------------------------------------------------
