%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:09 EST 2020

% Result     : Theorem 14.34s
% Output     : CNFRefutation 14.53s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 487 expanded)
%              Number of leaves         :   33 ( 174 expanded)
%              Depth                    :   13
%              Number of atoms          :  187 (1070 expanded)
%              Number of equality atoms :   43 ( 228 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k4_xboole_0 > k3_subset_1 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k2_tops_1,type,(
    k2_tops_1: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_138,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v3_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_tops_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_126,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).

tff(f_83,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(B,k2_pre_topc(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_pre_topc)).

tff(f_70,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k7_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_subset_1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_98,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

tff(f_91,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k1_tops_1(A,B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).

tff(f_105,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_119,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( v3_pre_topc(B,A)
                  & r1_tarski(B,C) )
               => r1_tarski(B,k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_tops_1)).

tff(c_48,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),'#skF_2') != k2_tops_1('#skF_1','#skF_2')
    | ~ v3_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_81,plain,(
    ~ v3_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_44,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_42,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_422,plain,(
    ! [A_91,B_92,C_93] :
      ( k7_subset_1(A_91,B_92,C_93) = k4_xboole_0(B_92,C_93)
      | ~ m1_subset_1(B_92,k1_zfmisc_1(A_91)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_434,plain,(
    ! [C_93] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_93) = k4_xboole_0('#skF_2',C_93) ),
    inference(resolution,[status(thm)],[c_42,c_422])).

tff(c_1884,plain,(
    ! [A_143,B_144] :
      ( k7_subset_1(u1_struct_0(A_143),B_144,k2_tops_1(A_143,B_144)) = k1_tops_1(A_143,B_144)
      | ~ m1_subset_1(B_144,k1_zfmisc_1(u1_struct_0(A_143)))
      | ~ l1_pre_topc(A_143) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_1911,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_1884])).

tff(c_1939,plain,(
    k4_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_434,c_1911])).

tff(c_1251,plain,(
    ! [B_124,A_125] :
      ( r1_tarski(B_124,k2_pre_topc(A_125,B_124))
      | ~ m1_subset_1(B_124,k1_zfmisc_1(u1_struct_0(A_125)))
      | ~ l1_pre_topc(A_125) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_1272,plain,
    ( r1_tarski('#skF_2',k2_pre_topc('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_1251])).

tff(c_1293,plain,(
    r1_tarski('#skF_2',k2_pre_topc('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_1272])).

tff(c_26,plain,(
    ! [A_24,B_25] :
      ( m1_subset_1(A_24,k1_zfmisc_1(B_25))
      | ~ r1_tarski(A_24,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_1680,plain,(
    ! [B_134,A_135,C_136] :
      ( k7_subset_1(B_134,A_135,C_136) = k4_xboole_0(A_135,C_136)
      | ~ r1_tarski(A_135,B_134) ) ),
    inference(resolution,[status(thm)],[c_26,c_422])).

tff(c_1788,plain,(
    ! [C_139] : k7_subset_1(k2_pre_topc('#skF_1','#skF_2'),'#skF_2',C_139) = k4_xboole_0('#skF_2',C_139) ),
    inference(resolution,[status(thm)],[c_1293,c_1680])).

tff(c_395,plain,(
    ! [A_85,B_86,C_87] :
      ( m1_subset_1(k7_subset_1(A_85,B_86,C_87),k1_zfmisc_1(A_85))
      | ~ m1_subset_1(B_86,k1_zfmisc_1(A_85)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_24,plain,(
    ! [A_24,B_25] :
      ( r1_tarski(A_24,B_25)
      | ~ m1_subset_1(A_24,k1_zfmisc_1(B_25)) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_409,plain,(
    ! [A_85,B_86,C_87] :
      ( r1_tarski(k7_subset_1(A_85,B_86,C_87),A_85)
      | ~ m1_subset_1(B_86,k1_zfmisc_1(A_85)) ) ),
    inference(resolution,[status(thm)],[c_395,c_24])).

tff(c_1794,plain,(
    ! [C_139] :
      ( r1_tarski(k4_xboole_0('#skF_2',C_139),k2_pre_topc('#skF_1','#skF_2'))
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_pre_topc('#skF_1','#skF_2'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1788,c_409])).

tff(c_22661,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_pre_topc('#skF_1','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_1794])).

tff(c_22664,plain,(
    ~ r1_tarski('#skF_2',k2_pre_topc('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_26,c_22661])).

tff(c_22668,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1293,c_22664])).

tff(c_22720,plain,(
    ! [C_477] : r1_tarski(k4_xboole_0('#skF_2',C_477),k2_pre_topc('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_1794])).

tff(c_22745,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_2'),k2_pre_topc('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1939,c_22720])).

tff(c_1080,plain,(
    ! [A_120,B_121] :
      ( m1_subset_1(k2_pre_topc(A_120,B_121),k1_zfmisc_1(u1_struct_0(A_120)))
      | ~ m1_subset_1(B_121,k1_zfmisc_1(u1_struct_0(A_120)))
      | ~ l1_pre_topc(A_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_54,plain,
    ( v3_pre_topc('#skF_2','#skF_1')
    | k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),'#skF_2') = k2_tops_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_120,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),'#skF_2') = k2_tops_1('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_81,c_54])).

tff(c_410,plain,(
    ! [A_88,B_89,C_90] :
      ( r1_tarski(k7_subset_1(A_88,B_89,C_90),A_88)
      | ~ m1_subset_1(B_89,k1_zfmisc_1(A_88)) ) ),
    inference(resolution,[status(thm)],[c_395,c_24])).

tff(c_418,plain,
    ( r1_tarski(k2_tops_1('#skF_1','#skF_2'),u1_struct_0('#skF_1'))
    | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_120,c_410])).

tff(c_592,plain,(
    ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_418])).

tff(c_1092,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_1080,c_592])).

tff(c_1114,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_1092])).

tff(c_1116,plain,(
    m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_418])).

tff(c_20,plain,(
    ! [A_17,B_18,C_19] :
      ( k7_subset_1(A_17,B_18,C_19) = k4_xboole_0(B_18,C_19)
      | ~ m1_subset_1(B_18,k1_zfmisc_1(A_17)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_7808,plain,(
    ! [C_282] : k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),C_282) = k4_xboole_0(k2_pre_topc('#skF_1','#skF_2'),C_282) ),
    inference(resolution,[status(thm)],[c_1116,c_20])).

tff(c_7840,plain,(
    k4_xboole_0(k2_pre_topc('#skF_1','#skF_2'),'#skF_2') = k2_tops_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_7808,c_120])).

tff(c_84,plain,(
    ! [A_61,B_62] :
      ( k4_xboole_0(A_61,B_62) = k3_subset_1(A_61,B_62)
      | ~ m1_subset_1(B_62,k1_zfmisc_1(A_61)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_91,plain,(
    ! [B_25,A_24] :
      ( k4_xboole_0(B_25,A_24) = k3_subset_1(B_25,A_24)
      | ~ r1_tarski(A_24,B_25) ) ),
    inference(resolution,[status(thm)],[c_26,c_84])).

tff(c_1299,plain,(
    k4_xboole_0(k2_pre_topc('#skF_1','#skF_2'),'#skF_2') = k3_subset_1(k2_pre_topc('#skF_1','#skF_2'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_1293,c_91])).

tff(c_7905,plain,(
    k3_subset_1(k2_pre_topc('#skF_1','#skF_2'),'#skF_2') = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7840,c_1299])).

tff(c_172,plain,(
    ! [A_72,B_73] :
      ( k3_subset_1(A_72,k3_subset_1(A_72,B_73)) = B_73
      | ~ m1_subset_1(B_73,k1_zfmisc_1(A_72)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_180,plain,(
    ! [B_25,A_24] :
      ( k3_subset_1(B_25,k3_subset_1(B_25,A_24)) = A_24
      | ~ r1_tarski(A_24,B_25) ) ),
    inference(resolution,[status(thm)],[c_26,c_172])).

tff(c_7970,plain,
    ( k3_subset_1(k2_pre_topc('#skF_1','#skF_2'),k2_tops_1('#skF_1','#skF_2')) = '#skF_2'
    | ~ r1_tarski('#skF_2',k2_pre_topc('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_7905,c_180])).

tff(c_7981,plain,(
    k3_subset_1(k2_pre_topc('#skF_1','#skF_2'),k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1293,c_7970])).

tff(c_34,plain,(
    ! [A_33,B_35] :
      ( k7_subset_1(u1_struct_0(A_33),k2_pre_topc(A_33,B_35),k1_tops_1(A_33,B_35)) = k2_tops_1(A_33,B_35)
      | ~ m1_subset_1(B_35,k1_zfmisc_1(u1_struct_0(A_33)))
      | ~ l1_pre_topc(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_7831,plain,
    ( k4_xboole_0(k2_pre_topc('#skF_1','#skF_2'),k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_7808,c_34])).

tff(c_7867,plain,(
    k4_xboole_0(k2_pre_topc('#skF_1','#skF_2'),k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_7831])).

tff(c_22773,plain,(
    k4_xboole_0(k2_pre_topc('#skF_1','#skF_2'),k1_tops_1('#skF_1','#skF_2')) = k3_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_22745,c_91])).

tff(c_22779,plain,(
    k3_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7867,c_22773])).

tff(c_23366,plain,
    ( k3_subset_1(k2_pre_topc('#skF_1','#skF_2'),k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2')
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),k2_pre_topc('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_22779,c_180])).

tff(c_23391,plain,(
    k1_tops_1('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22745,c_7981,c_23366])).

tff(c_46,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_435,plain,(
    ! [C_94] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_94) = k4_xboole_0('#skF_2',C_94) ),
    inference(resolution,[status(thm)],[c_42,c_422])).

tff(c_14,plain,(
    ! [A_9,B_10,C_11] :
      ( m1_subset_1(k7_subset_1(A_9,B_10,C_11),k1_zfmisc_1(A_9))
      | ~ m1_subset_1(B_10,k1_zfmisc_1(A_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_444,plain,(
    ! [C_94] :
      ( m1_subset_1(k4_xboole_0('#skF_2',C_94),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_435,c_14])).

tff(c_452,plain,(
    ! [C_94] : m1_subset_1(k4_xboole_0('#skF_2',C_94),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_444])).

tff(c_1803,plain,(
    ! [A_140,B_141] :
      ( v3_pre_topc(k1_tops_1(A_140,B_141),A_140)
      | ~ m1_subset_1(B_141,k1_zfmisc_1(u1_struct_0(A_140)))
      | ~ l1_pre_topc(A_140)
      | ~ v2_pre_topc(A_140) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_1819,plain,(
    ! [C_94] :
      ( v3_pre_topc(k1_tops_1('#skF_1',k4_xboole_0('#skF_2',C_94)),'#skF_1')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_452,c_1803])).

tff(c_1852,plain,(
    ! [C_94] : v3_pre_topc(k1_tops_1('#skF_1',k4_xboole_0('#skF_2',C_94)),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_1819])).

tff(c_1942,plain,(
    v3_pre_topc(k1_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2')),'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1939,c_1852])).

tff(c_23453,plain,(
    v3_pre_topc('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_23391,c_23391,c_1942])).

tff(c_23520,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_81,c_23453])).

tff(c_23521,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),'#skF_2') != k2_tops_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_24101,plain,(
    ! [A_524,B_525] :
      ( r1_tarski(k1_tops_1(A_524,B_525),B_525)
      | ~ m1_subset_1(B_525,k1_zfmisc_1(u1_struct_0(A_524)))
      | ~ l1_pre_topc(A_524) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_24120,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_24101])).

tff(c_24138,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_24120])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_24145,plain,
    ( k1_tops_1('#skF_1','#skF_2') = '#skF_2'
    | ~ r1_tarski('#skF_2',k1_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_24138,c_2])).

tff(c_24146,plain,(
    ~ r1_tarski('#skF_2',k1_tops_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_24145])).

tff(c_23522,plain,(
    v3_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_25351,plain,(
    ! [B_561,A_562,C_563] :
      ( r1_tarski(B_561,k1_tops_1(A_562,C_563))
      | ~ r1_tarski(B_561,C_563)
      | ~ v3_pre_topc(B_561,A_562)
      | ~ m1_subset_1(C_563,k1_zfmisc_1(u1_struct_0(A_562)))
      | ~ m1_subset_1(B_561,k1_zfmisc_1(u1_struct_0(A_562)))
      | ~ l1_pre_topc(A_562) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_25377,plain,(
    ! [B_561] :
      ( r1_tarski(B_561,k1_tops_1('#skF_1','#skF_2'))
      | ~ r1_tarski(B_561,'#skF_2')
      | ~ v3_pre_topc(B_561,'#skF_1')
      | ~ m1_subset_1(B_561,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_42,c_25351])).

tff(c_26068,plain,(
    ! [B_583] :
      ( r1_tarski(B_583,k1_tops_1('#skF_1','#skF_2'))
      | ~ r1_tarski(B_583,'#skF_2')
      | ~ v3_pre_topc(B_583,'#skF_1')
      | ~ m1_subset_1(B_583,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_25377])).

tff(c_26112,plain,
    ( r1_tarski('#skF_2',k1_tops_1('#skF_1','#skF_2'))
    | ~ r1_tarski('#skF_2','#skF_2')
    | ~ v3_pre_topc('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_26068])).

tff(c_26141,plain,(
    r1_tarski('#skF_2',k1_tops_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_23522,c_6,c_26112])).

tff(c_26143,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24146,c_26141])).

tff(c_26144,plain,(
    k1_tops_1('#skF_1','#skF_2') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_24145])).

tff(c_27015,plain,(
    ! [A_618,B_619] :
      ( k7_subset_1(u1_struct_0(A_618),k2_pre_topc(A_618,B_619),k1_tops_1(A_618,B_619)) = k2_tops_1(A_618,B_619)
      | ~ m1_subset_1(B_619,k1_zfmisc_1(u1_struct_0(A_618)))
      | ~ l1_pre_topc(A_618) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_27030,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),'#skF_2') = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_26144,c_27015])).

tff(c_27034,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),'#skF_2') = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_27030])).

tff(c_27036,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_23521,c_27034])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.32  % Computer   : n018.cluster.edu
% 0.14/0.32  % Model      : x86_64 x86_64
% 0.14/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.32  % Memory     : 8042.1875MB
% 0.14/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.32  % CPULimit   : 60
% 0.14/0.32  % DateTime   : Tue Dec  1 18:43:57 EST 2020
% 0.14/0.32  % CPUTime    : 
% 0.14/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 14.34/6.77  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.34/6.78  
% 14.34/6.78  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.34/6.79  %$ v3_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k4_xboole_0 > k3_subset_1 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1
% 14.34/6.79  
% 14.34/6.79  %Foreground sorts:
% 14.34/6.79  
% 14.34/6.79  
% 14.34/6.79  %Background operators:
% 14.34/6.79  
% 14.34/6.79  
% 14.34/6.79  %Foreground operators:
% 14.34/6.79  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 14.34/6.79  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 14.34/6.79  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 14.34/6.79  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 14.34/6.79  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 14.34/6.79  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 14.34/6.79  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 14.34/6.79  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 14.34/6.79  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 14.34/6.79  tff('#skF_2', type, '#skF_2': $i).
% 14.34/6.79  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 14.34/6.79  tff('#skF_1', type, '#skF_1': $i).
% 14.34/6.79  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 14.34/6.79  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 14.34/6.79  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 14.34/6.79  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 14.34/6.79  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 14.34/6.79  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 14.34/6.79  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 14.34/6.79  
% 14.53/6.81  tff(f_138, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t76_tops_1)).
% 14.53/6.81  tff(f_59, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 14.53/6.81  tff(f_126, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_tops_1)).
% 14.53/6.81  tff(f_83, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(B, k2_pre_topc(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_pre_topc)).
% 14.53/6.81  tff(f_70, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 14.53/6.81  tff(f_45, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k7_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_subset_1)).
% 14.53/6.81  tff(f_76, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 14.53/6.81  tff(f_37, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 14.53/6.81  tff(f_55, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 14.53/6.81  tff(f_98, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l78_tops_1)).
% 14.53/6.81  tff(f_91, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k1_tops_1(A, B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_tops_1)).
% 14.53/6.81  tff(f_105, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tops_1)).
% 14.53/6.81  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 14.53/6.81  tff(f_119, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & r1_tarski(B, C)) => r1_tarski(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_tops_1)).
% 14.53/6.81  tff(c_48, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')!=k2_tops_1('#skF_1', '#skF_2') | ~v3_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_138])).
% 14.53/6.81  tff(c_81, plain, (~v3_pre_topc('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_48])).
% 14.53/6.81  tff(c_44, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_138])).
% 14.53/6.81  tff(c_42, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_138])).
% 14.53/6.81  tff(c_422, plain, (![A_91, B_92, C_93]: (k7_subset_1(A_91, B_92, C_93)=k4_xboole_0(B_92, C_93) | ~m1_subset_1(B_92, k1_zfmisc_1(A_91)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 14.53/6.81  tff(c_434, plain, (![C_93]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_93)=k4_xboole_0('#skF_2', C_93))), inference(resolution, [status(thm)], [c_42, c_422])).
% 14.53/6.81  tff(c_1884, plain, (![A_143, B_144]: (k7_subset_1(u1_struct_0(A_143), B_144, k2_tops_1(A_143, B_144))=k1_tops_1(A_143, B_144) | ~m1_subset_1(B_144, k1_zfmisc_1(u1_struct_0(A_143))) | ~l1_pre_topc(A_143))), inference(cnfTransformation, [status(thm)], [f_126])).
% 14.53/6.81  tff(c_1911, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_42, c_1884])).
% 14.53/6.81  tff(c_1939, plain, (k4_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_434, c_1911])).
% 14.53/6.81  tff(c_1251, plain, (![B_124, A_125]: (r1_tarski(B_124, k2_pre_topc(A_125, B_124)) | ~m1_subset_1(B_124, k1_zfmisc_1(u1_struct_0(A_125))) | ~l1_pre_topc(A_125))), inference(cnfTransformation, [status(thm)], [f_83])).
% 14.53/6.81  tff(c_1272, plain, (r1_tarski('#skF_2', k2_pre_topc('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_42, c_1251])).
% 14.53/6.81  tff(c_1293, plain, (r1_tarski('#skF_2', k2_pre_topc('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_1272])).
% 14.53/6.81  tff(c_26, plain, (![A_24, B_25]: (m1_subset_1(A_24, k1_zfmisc_1(B_25)) | ~r1_tarski(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_70])).
% 14.53/6.81  tff(c_1680, plain, (![B_134, A_135, C_136]: (k7_subset_1(B_134, A_135, C_136)=k4_xboole_0(A_135, C_136) | ~r1_tarski(A_135, B_134))), inference(resolution, [status(thm)], [c_26, c_422])).
% 14.53/6.81  tff(c_1788, plain, (![C_139]: (k7_subset_1(k2_pre_topc('#skF_1', '#skF_2'), '#skF_2', C_139)=k4_xboole_0('#skF_2', C_139))), inference(resolution, [status(thm)], [c_1293, c_1680])).
% 14.53/6.81  tff(c_395, plain, (![A_85, B_86, C_87]: (m1_subset_1(k7_subset_1(A_85, B_86, C_87), k1_zfmisc_1(A_85)) | ~m1_subset_1(B_86, k1_zfmisc_1(A_85)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 14.53/6.81  tff(c_24, plain, (![A_24, B_25]: (r1_tarski(A_24, B_25) | ~m1_subset_1(A_24, k1_zfmisc_1(B_25)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 14.53/6.81  tff(c_409, plain, (![A_85, B_86, C_87]: (r1_tarski(k7_subset_1(A_85, B_86, C_87), A_85) | ~m1_subset_1(B_86, k1_zfmisc_1(A_85)))), inference(resolution, [status(thm)], [c_395, c_24])).
% 14.53/6.81  tff(c_1794, plain, (![C_139]: (r1_tarski(k4_xboole_0('#skF_2', C_139), k2_pre_topc('#skF_1', '#skF_2')) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_pre_topc('#skF_1', '#skF_2'))))), inference(superposition, [status(thm), theory('equality')], [c_1788, c_409])).
% 14.53/6.81  tff(c_22661, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(k2_pre_topc('#skF_1', '#skF_2')))), inference(splitLeft, [status(thm)], [c_1794])).
% 14.53/6.81  tff(c_22664, plain, (~r1_tarski('#skF_2', k2_pre_topc('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_26, c_22661])).
% 14.53/6.81  tff(c_22668, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1293, c_22664])).
% 14.53/6.81  tff(c_22720, plain, (![C_477]: (r1_tarski(k4_xboole_0('#skF_2', C_477), k2_pre_topc('#skF_1', '#skF_2')))), inference(splitRight, [status(thm)], [c_1794])).
% 14.53/6.81  tff(c_22745, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1939, c_22720])).
% 14.53/6.81  tff(c_1080, plain, (![A_120, B_121]: (m1_subset_1(k2_pre_topc(A_120, B_121), k1_zfmisc_1(u1_struct_0(A_120))) | ~m1_subset_1(B_121, k1_zfmisc_1(u1_struct_0(A_120))) | ~l1_pre_topc(A_120))), inference(cnfTransformation, [status(thm)], [f_76])).
% 14.53/6.81  tff(c_54, plain, (v3_pre_topc('#skF_2', '#skF_1') | k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')=k2_tops_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_138])).
% 14.53/6.81  tff(c_120, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')=k2_tops_1('#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_81, c_54])).
% 14.53/6.81  tff(c_410, plain, (![A_88, B_89, C_90]: (r1_tarski(k7_subset_1(A_88, B_89, C_90), A_88) | ~m1_subset_1(B_89, k1_zfmisc_1(A_88)))), inference(resolution, [status(thm)], [c_395, c_24])).
% 14.53/6.81  tff(c_418, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), u1_struct_0('#skF_1')) | ~m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_120, c_410])).
% 14.53/6.81  tff(c_592, plain, (~m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_418])).
% 14.53/6.81  tff(c_1092, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_1080, c_592])).
% 14.53/6.81  tff(c_1114, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_1092])).
% 14.53/6.81  tff(c_1116, plain, (m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_418])).
% 14.53/6.81  tff(c_20, plain, (![A_17, B_18, C_19]: (k7_subset_1(A_17, B_18, C_19)=k4_xboole_0(B_18, C_19) | ~m1_subset_1(B_18, k1_zfmisc_1(A_17)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 14.53/6.81  tff(c_7808, plain, (![C_282]: (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), C_282)=k4_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), C_282))), inference(resolution, [status(thm)], [c_1116, c_20])).
% 14.53/6.81  tff(c_7840, plain, (k4_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')=k2_tops_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_7808, c_120])).
% 14.53/6.81  tff(c_84, plain, (![A_61, B_62]: (k4_xboole_0(A_61, B_62)=k3_subset_1(A_61, B_62) | ~m1_subset_1(B_62, k1_zfmisc_1(A_61)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 14.53/6.81  tff(c_91, plain, (![B_25, A_24]: (k4_xboole_0(B_25, A_24)=k3_subset_1(B_25, A_24) | ~r1_tarski(A_24, B_25))), inference(resolution, [status(thm)], [c_26, c_84])).
% 14.53/6.81  tff(c_1299, plain, (k4_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')=k3_subset_1(k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')), inference(resolution, [status(thm)], [c_1293, c_91])).
% 14.53/6.81  tff(c_7905, plain, (k3_subset_1(k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_7840, c_1299])).
% 14.53/6.81  tff(c_172, plain, (![A_72, B_73]: (k3_subset_1(A_72, k3_subset_1(A_72, B_73))=B_73 | ~m1_subset_1(B_73, k1_zfmisc_1(A_72)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 14.53/6.81  tff(c_180, plain, (![B_25, A_24]: (k3_subset_1(B_25, k3_subset_1(B_25, A_24))=A_24 | ~r1_tarski(A_24, B_25))), inference(resolution, [status(thm)], [c_26, c_172])).
% 14.53/6.81  tff(c_7970, plain, (k3_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k2_tops_1('#skF_1', '#skF_2'))='#skF_2' | ~r1_tarski('#skF_2', k2_pre_topc('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_7905, c_180])).
% 14.53/6.81  tff(c_7981, plain, (k3_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1293, c_7970])).
% 14.53/6.81  tff(c_34, plain, (![A_33, B_35]: (k7_subset_1(u1_struct_0(A_33), k2_pre_topc(A_33, B_35), k1_tops_1(A_33, B_35))=k2_tops_1(A_33, B_35) | ~m1_subset_1(B_35, k1_zfmisc_1(u1_struct_0(A_33))) | ~l1_pre_topc(A_33))), inference(cnfTransformation, [status(thm)], [f_98])).
% 14.53/6.81  tff(c_7831, plain, (k4_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_7808, c_34])).
% 14.53/6.81  tff(c_7867, plain, (k4_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_7831])).
% 14.53/6.81  tff(c_22773, plain, (k4_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), k1_tops_1('#skF_1', '#skF_2'))=k3_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_22745, c_91])).
% 14.53/6.81  tff(c_22779, plain, (k3_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_7867, c_22773])).
% 14.53/6.81  tff(c_23366, plain, (k3_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2') | ~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_22779, c_180])).
% 14.53/6.81  tff(c_23391, plain, (k1_tops_1('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_22745, c_7981, c_23366])).
% 14.53/6.81  tff(c_46, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_138])).
% 14.53/6.81  tff(c_435, plain, (![C_94]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_94)=k4_xboole_0('#skF_2', C_94))), inference(resolution, [status(thm)], [c_42, c_422])).
% 14.53/6.81  tff(c_14, plain, (![A_9, B_10, C_11]: (m1_subset_1(k7_subset_1(A_9, B_10, C_11), k1_zfmisc_1(A_9)) | ~m1_subset_1(B_10, k1_zfmisc_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 14.53/6.81  tff(c_444, plain, (![C_94]: (m1_subset_1(k4_xboole_0('#skF_2', C_94), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_435, c_14])).
% 14.53/6.81  tff(c_452, plain, (![C_94]: (m1_subset_1(k4_xboole_0('#skF_2', C_94), k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_444])).
% 14.53/6.81  tff(c_1803, plain, (![A_140, B_141]: (v3_pre_topc(k1_tops_1(A_140, B_141), A_140) | ~m1_subset_1(B_141, k1_zfmisc_1(u1_struct_0(A_140))) | ~l1_pre_topc(A_140) | ~v2_pre_topc(A_140))), inference(cnfTransformation, [status(thm)], [f_91])).
% 14.53/6.81  tff(c_1819, plain, (![C_94]: (v3_pre_topc(k1_tops_1('#skF_1', k4_xboole_0('#skF_2', C_94)), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_452, c_1803])).
% 14.53/6.81  tff(c_1852, plain, (![C_94]: (v3_pre_topc(k1_tops_1('#skF_1', k4_xboole_0('#skF_2', C_94)), '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_1819])).
% 14.53/6.81  tff(c_1942, plain, (v3_pre_topc(k1_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2')), '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1939, c_1852])).
% 14.53/6.81  tff(c_23453, plain, (v3_pre_topc('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_23391, c_23391, c_1942])).
% 14.53/6.81  tff(c_23520, plain, $false, inference(negUnitSimplification, [status(thm)], [c_81, c_23453])).
% 14.53/6.81  tff(c_23521, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')!=k2_tops_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_48])).
% 14.53/6.81  tff(c_24101, plain, (![A_524, B_525]: (r1_tarski(k1_tops_1(A_524, B_525), B_525) | ~m1_subset_1(B_525, k1_zfmisc_1(u1_struct_0(A_524))) | ~l1_pre_topc(A_524))), inference(cnfTransformation, [status(thm)], [f_105])).
% 14.53/6.81  tff(c_24120, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_42, c_24101])).
% 14.53/6.81  tff(c_24138, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_24120])).
% 14.53/6.81  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 14.53/6.81  tff(c_24145, plain, (k1_tops_1('#skF_1', '#skF_2')='#skF_2' | ~r1_tarski('#skF_2', k1_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_24138, c_2])).
% 14.53/6.81  tff(c_24146, plain, (~r1_tarski('#skF_2', k1_tops_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_24145])).
% 14.53/6.81  tff(c_23522, plain, (v3_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_48])).
% 14.53/6.81  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 14.53/6.81  tff(c_25351, plain, (![B_561, A_562, C_563]: (r1_tarski(B_561, k1_tops_1(A_562, C_563)) | ~r1_tarski(B_561, C_563) | ~v3_pre_topc(B_561, A_562) | ~m1_subset_1(C_563, k1_zfmisc_1(u1_struct_0(A_562))) | ~m1_subset_1(B_561, k1_zfmisc_1(u1_struct_0(A_562))) | ~l1_pre_topc(A_562))), inference(cnfTransformation, [status(thm)], [f_119])).
% 14.53/6.81  tff(c_25377, plain, (![B_561]: (r1_tarski(B_561, k1_tops_1('#skF_1', '#skF_2')) | ~r1_tarski(B_561, '#skF_2') | ~v3_pre_topc(B_561, '#skF_1') | ~m1_subset_1(B_561, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_42, c_25351])).
% 14.53/6.81  tff(c_26068, plain, (![B_583]: (r1_tarski(B_583, k1_tops_1('#skF_1', '#skF_2')) | ~r1_tarski(B_583, '#skF_2') | ~v3_pre_topc(B_583, '#skF_1') | ~m1_subset_1(B_583, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_25377])).
% 14.53/6.81  tff(c_26112, plain, (r1_tarski('#skF_2', k1_tops_1('#skF_1', '#skF_2')) | ~r1_tarski('#skF_2', '#skF_2') | ~v3_pre_topc('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_42, c_26068])).
% 14.53/6.81  tff(c_26141, plain, (r1_tarski('#skF_2', k1_tops_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_23522, c_6, c_26112])).
% 14.53/6.81  tff(c_26143, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24146, c_26141])).
% 14.53/6.81  tff(c_26144, plain, (k1_tops_1('#skF_1', '#skF_2')='#skF_2'), inference(splitRight, [status(thm)], [c_24145])).
% 14.53/6.81  tff(c_27015, plain, (![A_618, B_619]: (k7_subset_1(u1_struct_0(A_618), k2_pre_topc(A_618, B_619), k1_tops_1(A_618, B_619))=k2_tops_1(A_618, B_619) | ~m1_subset_1(B_619, k1_zfmisc_1(u1_struct_0(A_618))) | ~l1_pre_topc(A_618))), inference(cnfTransformation, [status(thm)], [f_98])).
% 14.53/6.81  tff(c_27030, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')=k2_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_26144, c_27015])).
% 14.53/6.81  tff(c_27034, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_27030])).
% 14.53/6.81  tff(c_27036, plain, $false, inference(negUnitSimplification, [status(thm)], [c_23521, c_27034])).
% 14.53/6.81  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.53/6.81  
% 14.53/6.81  Inference rules
% 14.53/6.81  ----------------------
% 14.53/6.81  #Ref     : 0
% 14.53/6.81  #Sup     : 6624
% 14.53/6.81  #Fact    : 0
% 14.53/6.81  #Define  : 0
% 14.53/6.81  #Split   : 27
% 14.53/6.81  #Chain   : 0
% 14.53/6.81  #Close   : 0
% 14.53/6.81  
% 14.53/6.81  Ordering : KBO
% 14.53/6.81  
% 14.53/6.81  Simplification rules
% 14.53/6.81  ----------------------
% 14.53/6.81  #Subsume      : 241
% 14.53/6.81  #Demod        : 5700
% 14.53/6.81  #Tautology    : 2054
% 14.53/6.81  #SimpNegUnit  : 9
% 14.53/6.81  #BackRed      : 85
% 14.53/6.81  
% 14.53/6.81  #Partial instantiations: 0
% 14.53/6.81  #Strategies tried      : 1
% 14.53/6.81  
% 14.53/6.81  Timing (in seconds)
% 14.53/6.81  ----------------------
% 14.53/6.81  Preprocessing        : 0.35
% 14.53/6.81  Parsing              : 0.19
% 14.53/6.81  CNF conversion       : 0.02
% 14.53/6.81  Main loop            : 5.70
% 14.53/6.81  Inferencing          : 1.10
% 14.53/6.81  Reduction            : 2.92
% 14.53/6.81  Demodulation         : 2.48
% 14.53/6.81  BG Simplification    : 0.15
% 14.53/6.81  Subsumption          : 1.19
% 14.53/6.81  Abstraction          : 0.25
% 14.53/6.81  MUC search           : 0.00
% 14.53/6.81  Cooper               : 0.00
% 14.53/6.81  Total                : 6.10
% 14.53/6.81  Index Insertion      : 0.00
% 14.53/6.81  Index Deletion       : 0.00
% 14.53/6.81  Index Matching       : 0.00
% 14.53/6.81  BG Taut test         : 0.00
%------------------------------------------------------------------------------
