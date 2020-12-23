%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:44 EST 2020

% Result     : Theorem 12.04s
% Output     : CNFRefutation 12.04s
% Verified   : 
% Statistics : Number of formulae       :  153 ( 720 expanded)
%              Number of leaves         :   41 ( 262 expanded)
%              Depth                    :   12
%              Number of atoms          :  273 (1461 expanded)
%              Number of equality atoms :   87 ( 428 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tops_1 > v1_tops_1 > r2_hidden > r1_tarski > m1_subset_1 > l1_struct_0 > l1_pre_topc > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_109,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v2_tops_1(B,A)
            <=> k1_tops_1(A,B) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_tops_1)).

tff(f_74,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_64,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_50,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_36,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_90,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_tops_1(B,A)
          <=> k2_pre_topc(A,B) = k2_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tops_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_81,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k3_subset_1(u1_struct_0(A),k2_pre_topc(A,k3_subset_1(u1_struct_0(A),B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_1)).

tff(f_40,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_42,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_56,axiom,(
    ! [A] : k2_subset_1(A) = k3_subset_1(A,k1_subset_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_subset_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_99,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> v1_tops_1(k3_subset_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_46,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(c_50,plain,
    ( k1_tops_1('#skF_2','#skF_3') != k1_xboole_0
    | ~ v2_tops_1('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_100,plain,(
    ~ v2_tops_1('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_48,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_34,plain,(
    ! [A_24] :
      ( l1_struct_0(A_24)
      | ~ l1_pre_topc(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_85,plain,(
    ! [A_39] :
      ( u1_struct_0(A_39) = k2_struct_0(A_39)
      | ~ l1_struct_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_90,plain,(
    ! [A_40] :
      ( u1_struct_0(A_40) = k2_struct_0(A_40)
      | ~ l1_pre_topc(A_40) ) ),
    inference(resolution,[status(thm)],[c_34,c_85])).

tff(c_94,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_90])).

tff(c_46,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_95,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_46])).

tff(c_162,plain,(
    ! [A_60,B_61] :
      ( m1_subset_1(k3_subset_1(A_60,B_61),k1_zfmisc_1(A_60))
      | ~ m1_subset_1(B_61,k1_zfmisc_1(A_60)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_26,plain,(
    ! [A_19,B_20] :
      ( r1_tarski(A_19,B_20)
      | ~ m1_subset_1(A_19,k1_zfmisc_1(B_20)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_239,plain,(
    ! [A_68,B_69] :
      ( r1_tarski(k3_subset_1(A_68,B_69),A_68)
      | ~ m1_subset_1(B_69,k1_zfmisc_1(A_68)) ) ),
    inference(resolution,[status(thm)],[c_162,c_26])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( k4_xboole_0(A_6,B_7) = k1_xboole_0
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_610,plain,(
    ! [A_90,B_91] :
      ( k4_xboole_0(k3_subset_1(A_90,B_91),A_90) = k1_xboole_0
      | ~ m1_subset_1(B_91,k1_zfmisc_1(A_90)) ) ),
    inference(resolution,[status(thm)],[c_239,c_10])).

tff(c_633,plain,(
    k4_xboole_0(k3_subset_1(k2_struct_0('#skF_2'),'#skF_3'),k2_struct_0('#skF_2')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_95,c_610])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( r1_tarski(A_6,B_7)
      | k4_xboole_0(A_6,B_7) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_28,plain,(
    ! [A_19,B_20] :
      ( m1_subset_1(A_19,k1_zfmisc_1(B_20))
      | ~ r1_tarski(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_788,plain,(
    ! [A_98,B_99] :
      ( k2_pre_topc(A_98,B_99) = k2_struct_0(A_98)
      | ~ v1_tops_1(B_99,A_98)
      | ~ m1_subset_1(B_99,k1_zfmisc_1(u1_struct_0(A_98)))
      | ~ l1_pre_topc(A_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_810,plain,(
    ! [B_99] :
      ( k2_pre_topc('#skF_2',B_99) = k2_struct_0('#skF_2')
      | ~ v1_tops_1(B_99,'#skF_2')
      | ~ m1_subset_1(B_99,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_94,c_788])).

tff(c_820,plain,(
    ! [B_101] :
      ( k2_pre_topc('#skF_2',B_101) = k2_struct_0('#skF_2')
      | ~ v1_tops_1(B_101,'#skF_2')
      | ~ m1_subset_1(B_101,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_810])).

tff(c_1270,plain,(
    ! [A_124] :
      ( k2_pre_topc('#skF_2',A_124) = k2_struct_0('#skF_2')
      | ~ v1_tops_1(A_124,'#skF_2')
      | ~ r1_tarski(A_124,k2_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_28,c_820])).

tff(c_2310,plain,(
    ! [A_151] :
      ( k2_pre_topc('#skF_2',A_151) = k2_struct_0('#skF_2')
      | ~ v1_tops_1(A_151,'#skF_2')
      | k4_xboole_0(A_151,k2_struct_0('#skF_2')) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_1270])).

tff(c_2355,plain,
    ( k2_pre_topc('#skF_2',k3_subset_1(k2_struct_0('#skF_2'),'#skF_3')) = k2_struct_0('#skF_2')
    | ~ v1_tops_1(k3_subset_1(k2_struct_0('#skF_2'),'#skF_3'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_633,c_2310])).

tff(c_2362,plain,(
    ~ v1_tops_1(k3_subset_1(k2_struct_0('#skF_2'),'#skF_3'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_2355])).

tff(c_649,plain,(
    ! [B_92,A_93] :
      ( v1_tops_1(B_92,A_93)
      | k2_pre_topc(A_93,B_92) != k2_struct_0(A_93)
      | ~ m1_subset_1(B_92,k1_zfmisc_1(u1_struct_0(A_93)))
      | ~ l1_pre_topc(A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_671,plain,(
    ! [B_92] :
      ( v1_tops_1(B_92,'#skF_2')
      | k2_pre_topc('#skF_2',B_92) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(B_92,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_94,c_649])).

tff(c_756,plain,(
    ! [B_97] :
      ( v1_tops_1(B_97,'#skF_2')
      | k2_pre_topc('#skF_2',B_97) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(B_97,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_671])).

tff(c_1238,plain,(
    ! [A_123] :
      ( v1_tops_1(A_123,'#skF_2')
      | k2_pre_topc('#skF_2',A_123) != k2_struct_0('#skF_2')
      | ~ r1_tarski(A_123,k2_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_28,c_756])).

tff(c_2232,plain,(
    ! [A_148] :
      ( v1_tops_1(A_148,'#skF_2')
      | k2_pre_topc('#skF_2',A_148) != k2_struct_0('#skF_2')
      | k4_xboole_0(A_148,k2_struct_0('#skF_2')) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_1238])).

tff(c_2273,plain,
    ( v1_tops_1(k3_subset_1(k2_struct_0('#skF_2'),'#skF_3'),'#skF_2')
    | k2_pre_topc('#skF_2',k3_subset_1(k2_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_633,c_2232])).

tff(c_2449,plain,(
    k2_pre_topc('#skF_2',k3_subset_1(k2_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_2362,c_2273])).

tff(c_20,plain,(
    ! [A_14,B_15] :
      ( m1_subset_1(k3_subset_1(A_14,B_15),k1_zfmisc_1(A_14))
      | ~ m1_subset_1(B_15,k1_zfmisc_1(A_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_267,plain,(
    ! [A_72,B_73] :
      ( k3_subset_1(A_72,k3_subset_1(A_72,B_73)) = B_73
      | ~ m1_subset_1(B_73,k1_zfmisc_1(A_72)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_283,plain,(
    k3_subset_1(k2_struct_0('#skF_2'),k3_subset_1(k2_struct_0('#skF_2'),'#skF_3')) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_95,c_267])).

tff(c_1176,plain,(
    ! [A_121,B_122] :
      ( k3_subset_1(u1_struct_0(A_121),k2_pre_topc(A_121,k3_subset_1(u1_struct_0(A_121),B_122))) = k1_tops_1(A_121,B_122)
      | ~ m1_subset_1(B_122,k1_zfmisc_1(u1_struct_0(A_121)))
      | ~ l1_pre_topc(A_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_1220,plain,(
    ! [B_122] :
      ( k3_subset_1(k2_struct_0('#skF_2'),k2_pre_topc('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),B_122))) = k1_tops_1('#skF_2',B_122)
      | ~ m1_subset_1(B_122,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_94,c_1176])).

tff(c_2083,plain,(
    ! [B_145] :
      ( k3_subset_1(k2_struct_0('#skF_2'),k2_pre_topc('#skF_2',k3_subset_1(k2_struct_0('#skF_2'),B_145))) = k1_tops_1('#skF_2',B_145)
      | ~ m1_subset_1(B_145,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_94,c_94,c_1220])).

tff(c_2136,plain,
    ( k3_subset_1(k2_struct_0('#skF_2'),k2_pre_topc('#skF_2','#skF_3')) = k1_tops_1('#skF_2',k3_subset_1(k2_struct_0('#skF_2'),'#skF_3'))
    | ~ m1_subset_1(k3_subset_1(k2_struct_0('#skF_2'),'#skF_3'),k1_zfmisc_1(k2_struct_0('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_283,c_2083])).

tff(c_6816,plain,(
    ~ m1_subset_1(k3_subset_1(k2_struct_0('#skF_2'),'#skF_3'),k1_zfmisc_1(k2_struct_0('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_2136])).

tff(c_6822,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_20,c_6816])).

tff(c_6831,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_6822])).

tff(c_6833,plain,(
    m1_subset_1(k3_subset_1(k2_struct_0('#skF_2'),'#skF_3'),k1_zfmisc_1(k2_struct_0('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_2136])).

tff(c_14,plain,(
    ! [A_10] : k1_subset_1(A_10) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_16,plain,(
    ! [A_11] : k2_subset_1(A_11) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_24,plain,(
    ! [A_18] : k3_subset_1(A_18,k1_subset_1(A_18)) = k2_subset_1(A_18) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_57,plain,(
    ! [A_18] : k3_subset_1(A_18,k1_subset_1(A_18)) = A_18 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_24])).

tff(c_58,plain,(
    ! [A_18] : k3_subset_1(A_18,k1_xboole_0) = A_18 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_57])).

tff(c_6879,plain,(
    r1_tarski(k3_subset_1(k2_struct_0('#skF_2'),'#skF_3'),k2_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_6833,c_26])).

tff(c_56,plain,
    ( v2_tops_1('#skF_3','#skF_2')
    | k1_tops_1('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_125,plain,(
    k1_tops_1('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_56])).

tff(c_282,plain,(
    ! [B_20,A_19] :
      ( k3_subset_1(B_20,k3_subset_1(B_20,A_19)) = A_19
      | ~ r1_tarski(A_19,B_20) ) ),
    inference(resolution,[status(thm)],[c_28,c_267])).

tff(c_19639,plain,(
    ! [A_418,A_419] :
      ( k3_subset_1(u1_struct_0(A_418),k2_pre_topc(A_418,A_419)) = k1_tops_1(A_418,k3_subset_1(u1_struct_0(A_418),A_419))
      | ~ m1_subset_1(k3_subset_1(u1_struct_0(A_418),A_419),k1_zfmisc_1(u1_struct_0(A_418)))
      | ~ l1_pre_topc(A_418)
      | ~ r1_tarski(A_419,u1_struct_0(A_418)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_282,c_1176])).

tff(c_19725,plain,(
    ! [A_419] :
      ( k3_subset_1(u1_struct_0('#skF_2'),k2_pre_topc('#skF_2',A_419)) = k1_tops_1('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),A_419))
      | ~ m1_subset_1(k3_subset_1(k2_struct_0('#skF_2'),A_419),k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ r1_tarski(A_419,u1_struct_0('#skF_2')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_94,c_19639])).

tff(c_22949,plain,(
    ! [A_470] :
      ( k3_subset_1(k2_struct_0('#skF_2'),k2_pre_topc('#skF_2',A_470)) = k1_tops_1('#skF_2',k3_subset_1(k2_struct_0('#skF_2'),A_470))
      | ~ m1_subset_1(k3_subset_1(k2_struct_0('#skF_2'),A_470),k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ r1_tarski(A_470,k2_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_48,c_94,c_94,c_94,c_19725])).

tff(c_23015,plain,
    ( k3_subset_1(k2_struct_0('#skF_2'),k2_pre_topc('#skF_2',k3_subset_1(k2_struct_0('#skF_2'),'#skF_3'))) = k1_tops_1('#skF_2',k3_subset_1(k2_struct_0('#skF_2'),k3_subset_1(k2_struct_0('#skF_2'),'#skF_3')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_struct_0('#skF_2')))
    | ~ r1_tarski(k3_subset_1(k2_struct_0('#skF_2'),'#skF_3'),k2_struct_0('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_283,c_22949])).

tff(c_23061,plain,(
    k3_subset_1(k2_struct_0('#skF_2'),k2_pre_topc('#skF_2',k3_subset_1(k2_struct_0('#skF_2'),'#skF_3'))) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6879,c_95,c_125,c_283,c_23015])).

tff(c_478,plain,(
    ! [A_83,B_84] :
      ( m1_subset_1(k2_pre_topc(A_83,B_84),k1_zfmisc_1(u1_struct_0(A_83)))
      | ~ m1_subset_1(B_84,k1_zfmisc_1(u1_struct_0(A_83)))
      | ~ l1_pre_topc(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_22,plain,(
    ! [A_16,B_17] :
      ( k3_subset_1(A_16,k3_subset_1(A_16,B_17)) = B_17
      | ~ m1_subset_1(B_17,k1_zfmisc_1(A_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_3781,plain,(
    ! [A_198,B_199] :
      ( k3_subset_1(u1_struct_0(A_198),k3_subset_1(u1_struct_0(A_198),k2_pre_topc(A_198,B_199))) = k2_pre_topc(A_198,B_199)
      | ~ m1_subset_1(B_199,k1_zfmisc_1(u1_struct_0(A_198)))
      | ~ l1_pre_topc(A_198) ) ),
    inference(resolution,[status(thm)],[c_478,c_22])).

tff(c_3856,plain,(
    ! [B_199] :
      ( k3_subset_1(u1_struct_0('#skF_2'),k3_subset_1(k2_struct_0('#skF_2'),k2_pre_topc('#skF_2',B_199))) = k2_pre_topc('#skF_2',B_199)
      | ~ m1_subset_1(B_199,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_94,c_3781])).

tff(c_3874,plain,(
    ! [B_199] :
      ( k3_subset_1(k2_struct_0('#skF_2'),k3_subset_1(k2_struct_0('#skF_2'),k2_pre_topc('#skF_2',B_199))) = k2_pre_topc('#skF_2',B_199)
      | ~ m1_subset_1(B_199,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_94,c_94,c_3856])).

tff(c_23138,plain,
    ( k2_pre_topc('#skF_2',k3_subset_1(k2_struct_0('#skF_2'),'#skF_3')) = k3_subset_1(k2_struct_0('#skF_2'),k1_xboole_0)
    | ~ m1_subset_1(k3_subset_1(k2_struct_0('#skF_2'),'#skF_3'),k1_zfmisc_1(k2_struct_0('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_23061,c_3874])).

tff(c_23235,plain,(
    k2_pre_topc('#skF_2',k3_subset_1(k2_struct_0('#skF_2'),'#skF_3')) = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6833,c_58,c_23138])).

tff(c_23237,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2449,c_23235])).

tff(c_23239,plain,(
    v1_tops_1(k3_subset_1(k2_struct_0('#skF_2'),'#skF_3'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_2355])).

tff(c_865,plain,(
    ! [B_103,A_104] :
      ( v2_tops_1(B_103,A_104)
      | ~ v1_tops_1(k3_subset_1(u1_struct_0(A_104),B_103),A_104)
      | ~ m1_subset_1(B_103,k1_zfmisc_1(u1_struct_0(A_104)))
      | ~ l1_pre_topc(A_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_876,plain,(
    ! [B_103] :
      ( v2_tops_1(B_103,'#skF_2')
      | ~ v1_tops_1(k3_subset_1(k2_struct_0('#skF_2'),B_103),'#skF_2')
      | ~ m1_subset_1(B_103,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_94,c_865])).

tff(c_884,plain,(
    ! [B_103] :
      ( v2_tops_1(B_103,'#skF_2')
      | ~ v1_tops_1(k3_subset_1(k2_struct_0('#skF_2'),B_103),'#skF_2')
      | ~ m1_subset_1(B_103,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_94,c_876])).

tff(c_23242,plain,
    ( v2_tops_1('#skF_3','#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_23239,c_884])).

tff(c_23245,plain,(
    v2_tops_1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_23242])).

tff(c_23247,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_23245])).

tff(c_23248,plain,(
    k1_tops_1('#skF_2','#skF_3') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_23286,plain,(
    ! [A_483,B_484] :
      ( r2_hidden('#skF_1'(A_483,B_484),A_483)
      | r1_tarski(A_483,B_484) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_23292,plain,(
    ! [A_485] : r1_tarski(A_485,A_485) ),
    inference(resolution,[status(thm)],[c_23286,c_4])).

tff(c_23296,plain,(
    ! [A_485] : k4_xboole_0(A_485,A_485) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_23292,c_10])).

tff(c_23291,plain,(
    ! [A_483] : r1_tarski(A_483,A_483) ),
    inference(resolution,[status(thm)],[c_23286,c_4])).

tff(c_23389,plain,(
    ! [A_498,B_499] :
      ( k4_xboole_0(A_498,B_499) = k3_subset_1(A_498,B_499)
      | ~ m1_subset_1(B_499,k1_zfmisc_1(A_498)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_23449,plain,(
    ! [B_502,A_503] :
      ( k4_xboole_0(B_502,A_503) = k3_subset_1(B_502,A_503)
      | ~ r1_tarski(A_503,B_502) ) ),
    inference(resolution,[status(thm)],[c_28,c_23389])).

tff(c_23452,plain,(
    ! [A_483] : k4_xboole_0(A_483,A_483) = k3_subset_1(A_483,A_483) ),
    inference(resolution,[status(thm)],[c_23291,c_23449])).

tff(c_23460,plain,(
    ! [A_483] : k3_subset_1(A_483,A_483) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_23296,c_23452])).

tff(c_23249,plain,(
    v2_tops_1('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_23995,plain,(
    ! [A_531,B_532] :
      ( v1_tops_1(k3_subset_1(u1_struct_0(A_531),B_532),A_531)
      | ~ v2_tops_1(B_532,A_531)
      | ~ m1_subset_1(B_532,k1_zfmisc_1(u1_struct_0(A_531)))
      | ~ l1_pre_topc(A_531) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_24006,plain,(
    ! [B_532] :
      ( v1_tops_1(k3_subset_1(k2_struct_0('#skF_2'),B_532),'#skF_2')
      | ~ v2_tops_1(B_532,'#skF_2')
      | ~ m1_subset_1(B_532,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_94,c_23995])).

tff(c_24014,plain,(
    ! [B_532] :
      ( v1_tops_1(k3_subset_1(k2_struct_0('#skF_2'),B_532),'#skF_2')
      | ~ v2_tops_1(B_532,'#skF_2')
      | ~ m1_subset_1(B_532,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_94,c_24006])).

tff(c_23371,plain,(
    ! [A_496,B_497] :
      ( m1_subset_1(k3_subset_1(A_496,B_497),k1_zfmisc_1(A_496))
      | ~ m1_subset_1(B_497,k1_zfmisc_1(A_496)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_23625,plain,(
    ! [A_514,B_515] :
      ( r1_tarski(k3_subset_1(A_514,B_515),A_514)
      | ~ m1_subset_1(B_515,k1_zfmisc_1(A_514)) ) ),
    inference(resolution,[status(thm)],[c_23371,c_26])).

tff(c_23653,plain,(
    ! [A_516,B_517] :
      ( k4_xboole_0(k3_subset_1(A_516,B_517),A_516) = k1_xboole_0
      | ~ m1_subset_1(B_517,k1_zfmisc_1(A_516)) ) ),
    inference(resolution,[status(thm)],[c_23625,c_10])).

tff(c_23676,plain,(
    k4_xboole_0(k3_subset_1(k2_struct_0('#skF_2'),'#skF_3'),k2_struct_0('#skF_2')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_95,c_23653])).

tff(c_23870,plain,(
    ! [B_525,A_526] :
      ( v1_tops_1(B_525,A_526)
      | k2_pre_topc(A_526,B_525) != k2_struct_0(A_526)
      | ~ m1_subset_1(B_525,k1_zfmisc_1(u1_struct_0(A_526)))
      | ~ l1_pre_topc(A_526) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_23892,plain,(
    ! [B_525] :
      ( v1_tops_1(B_525,'#skF_2')
      | k2_pre_topc('#skF_2',B_525) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(B_525,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_94,c_23870])).

tff(c_23928,plain,(
    ! [B_528] :
      ( v1_tops_1(B_528,'#skF_2')
      | k2_pre_topc('#skF_2',B_528) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(B_528,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_23892])).

tff(c_24576,plain,(
    ! [A_558] :
      ( v1_tops_1(A_558,'#skF_2')
      | k2_pre_topc('#skF_2',A_558) != k2_struct_0('#skF_2')
      | ~ r1_tarski(A_558,k2_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_28,c_23928])).

tff(c_25567,plain,(
    ! [A_582] :
      ( v1_tops_1(A_582,'#skF_2')
      | k2_pre_topc('#skF_2',A_582) != k2_struct_0('#skF_2')
      | k4_xboole_0(A_582,k2_struct_0('#skF_2')) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_24576])).

tff(c_25612,plain,
    ( v1_tops_1(k3_subset_1(k2_struct_0('#skF_2'),'#skF_3'),'#skF_2')
    | k2_pre_topc('#skF_2',k3_subset_1(k2_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_23676,c_25567])).

tff(c_25620,plain,(
    k2_pre_topc('#skF_2',k3_subset_1(k2_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_25612])).

tff(c_23677,plain,(
    ! [A_518,B_519] :
      ( k2_pre_topc(A_518,B_519) = k2_struct_0(A_518)
      | ~ v1_tops_1(B_519,A_518)
      | ~ m1_subset_1(B_519,k1_zfmisc_1(u1_struct_0(A_518)))
      | ~ l1_pre_topc(A_518) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_23699,plain,(
    ! [B_519] :
      ( k2_pre_topc('#skF_2',B_519) = k2_struct_0('#skF_2')
      | ~ v1_tops_1(B_519,'#skF_2')
      | ~ m1_subset_1(B_519,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_94,c_23677])).

tff(c_23781,plain,(
    ! [B_523] :
      ( k2_pre_topc('#skF_2',B_523) = k2_struct_0('#skF_2')
      | ~ v1_tops_1(B_523,'#skF_2')
      | ~ m1_subset_1(B_523,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_23699])).

tff(c_24608,plain,(
    ! [A_559] :
      ( k2_pre_topc('#skF_2',A_559) = k2_struct_0('#skF_2')
      | ~ v1_tops_1(A_559,'#skF_2')
      | ~ r1_tarski(A_559,k2_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_28,c_23781])).

tff(c_25622,plain,(
    ! [A_583] :
      ( k2_pre_topc('#skF_2',A_583) = k2_struct_0('#skF_2')
      | ~ v1_tops_1(A_583,'#skF_2')
      | k4_xboole_0(A_583,k2_struct_0('#skF_2')) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_24608])).

tff(c_25648,plain,
    ( k2_pre_topc('#skF_2',k3_subset_1(k2_struct_0('#skF_2'),'#skF_3')) = k2_struct_0('#skF_2')
    | ~ v1_tops_1(k3_subset_1(k2_struct_0('#skF_2'),'#skF_3'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_23676,c_25622])).

tff(c_25673,plain,(
    ~ v1_tops_1(k3_subset_1(k2_struct_0('#skF_2'),'#skF_3'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_25620,c_25648])).

tff(c_25709,plain,
    ( ~ v2_tops_1('#skF_3','#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_24014,c_25673])).

tff(c_25713,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_23249,c_25709])).

tff(c_25715,plain,(
    k2_pre_topc('#skF_2',k3_subset_1(k2_struct_0('#skF_2'),'#skF_3')) = k2_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_25612])).

tff(c_24165,plain,(
    ! [A_544,B_545] :
      ( k3_subset_1(u1_struct_0(A_544),k2_pre_topc(A_544,k3_subset_1(u1_struct_0(A_544),B_545))) = k1_tops_1(A_544,B_545)
      | ~ m1_subset_1(B_545,k1_zfmisc_1(u1_struct_0(A_544)))
      | ~ l1_pre_topc(A_544) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_24206,plain,(
    ! [B_545] :
      ( k3_subset_1(k2_struct_0('#skF_2'),k2_pre_topc('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),B_545))) = k1_tops_1('#skF_2',B_545)
      | ~ m1_subset_1(B_545,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_94,c_24165])).

tff(c_24219,plain,(
    ! [B_545] :
      ( k3_subset_1(k2_struct_0('#skF_2'),k2_pre_topc('#skF_2',k3_subset_1(k2_struct_0('#skF_2'),B_545))) = k1_tops_1('#skF_2',B_545)
      | ~ m1_subset_1(B_545,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_94,c_94,c_24206])).

tff(c_25736,plain,
    ( k3_subset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_2')) = k1_tops_1('#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_struct_0('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_25715,c_24219])).

tff(c_25752,plain,(
    k1_tops_1('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_23460,c_25736])).

tff(c_25754,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_23248,c_25752])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.32  % Computer   : n021.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % DateTime   : Tue Dec  1 12:00:34 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 12.04/4.97  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.04/4.98  
% 12.04/4.98  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.04/4.98  %$ v2_tops_1 > v1_tops_1 > r2_hidden > r1_tarski > m1_subset_1 > l1_struct_0 > l1_pre_topc > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 12.04/4.98  
% 12.04/4.98  %Foreground sorts:
% 12.04/4.98  
% 12.04/4.98  
% 12.04/4.98  %Background operators:
% 12.04/4.98  
% 12.04/4.98  
% 12.04/4.98  %Foreground operators:
% 12.04/4.98  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 12.04/4.98  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 12.04/4.98  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 12.04/4.98  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 12.04/4.98  tff(v2_tops_1, type, v2_tops_1: ($i * $i) > $o).
% 12.04/4.98  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 12.04/4.98  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 12.04/4.98  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 12.04/4.98  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 12.04/4.98  tff(v1_tops_1, type, v1_tops_1: ($i * $i) > $o).
% 12.04/4.98  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 12.04/4.98  tff('#skF_2', type, '#skF_2': $i).
% 12.04/4.98  tff('#skF_3', type, '#skF_3': $i).
% 12.04/4.98  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 12.04/4.98  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 12.04/4.98  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 12.04/4.98  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 12.04/4.98  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 12.04/4.98  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 12.04/4.98  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 12.04/4.98  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 12.04/4.98  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 12.04/4.98  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 12.04/4.98  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 12.04/4.98  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 12.04/4.98  
% 12.04/5.00  tff(f_109, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (k1_tops_1(A, B) = k1_xboole_0)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t84_tops_1)).
% 12.04/5.00  tff(f_74, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 12.04/5.00  tff(f_64, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 12.04/5.00  tff(f_50, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 12.04/5.00  tff(f_60, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 12.04/5.00  tff(f_36, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 12.04/5.00  tff(f_90, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) <=> (k2_pre_topc(A, B) = k2_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tops_1)).
% 12.04/5.00  tff(f_54, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 12.04/5.00  tff(f_81, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k3_subset_1(u1_struct_0(A), k2_pre_topc(A, k3_subset_1(u1_struct_0(A), B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tops_1)).
% 12.04/5.00  tff(f_40, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_subset_1)).
% 12.04/5.00  tff(f_42, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 12.04/5.00  tff(f_56, axiom, (![A]: (k2_subset_1(A) = k3_subset_1(A, k1_subset_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_subset_1)).
% 12.04/5.00  tff(f_70, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 12.04/5.00  tff(f_99, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> v1_tops_1(k3_subset_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tops_1)).
% 12.04/5.00  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 12.04/5.00  tff(f_46, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 12.04/5.00  tff(c_50, plain, (k1_tops_1('#skF_2', '#skF_3')!=k1_xboole_0 | ~v2_tops_1('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_109])).
% 12.04/5.00  tff(c_100, plain, (~v2_tops_1('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_50])).
% 12.04/5.00  tff(c_48, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_109])).
% 12.04/5.00  tff(c_34, plain, (![A_24]: (l1_struct_0(A_24) | ~l1_pre_topc(A_24))), inference(cnfTransformation, [status(thm)], [f_74])).
% 12.04/5.00  tff(c_85, plain, (![A_39]: (u1_struct_0(A_39)=k2_struct_0(A_39) | ~l1_struct_0(A_39))), inference(cnfTransformation, [status(thm)], [f_64])).
% 12.04/5.00  tff(c_90, plain, (![A_40]: (u1_struct_0(A_40)=k2_struct_0(A_40) | ~l1_pre_topc(A_40))), inference(resolution, [status(thm)], [c_34, c_85])).
% 12.04/5.00  tff(c_94, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_48, c_90])).
% 12.04/5.00  tff(c_46, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_109])).
% 12.04/5.00  tff(c_95, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_46])).
% 12.04/5.01  tff(c_162, plain, (![A_60, B_61]: (m1_subset_1(k3_subset_1(A_60, B_61), k1_zfmisc_1(A_60)) | ~m1_subset_1(B_61, k1_zfmisc_1(A_60)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 12.04/5.01  tff(c_26, plain, (![A_19, B_20]: (r1_tarski(A_19, B_20) | ~m1_subset_1(A_19, k1_zfmisc_1(B_20)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 12.04/5.01  tff(c_239, plain, (![A_68, B_69]: (r1_tarski(k3_subset_1(A_68, B_69), A_68) | ~m1_subset_1(B_69, k1_zfmisc_1(A_68)))), inference(resolution, [status(thm)], [c_162, c_26])).
% 12.04/5.01  tff(c_10, plain, (![A_6, B_7]: (k4_xboole_0(A_6, B_7)=k1_xboole_0 | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 12.04/5.01  tff(c_610, plain, (![A_90, B_91]: (k4_xboole_0(k3_subset_1(A_90, B_91), A_90)=k1_xboole_0 | ~m1_subset_1(B_91, k1_zfmisc_1(A_90)))), inference(resolution, [status(thm)], [c_239, c_10])).
% 12.04/5.01  tff(c_633, plain, (k4_xboole_0(k3_subset_1(k2_struct_0('#skF_2'), '#skF_3'), k2_struct_0('#skF_2'))=k1_xboole_0), inference(resolution, [status(thm)], [c_95, c_610])).
% 12.04/5.01  tff(c_8, plain, (![A_6, B_7]: (r1_tarski(A_6, B_7) | k4_xboole_0(A_6, B_7)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_36])).
% 12.04/5.01  tff(c_28, plain, (![A_19, B_20]: (m1_subset_1(A_19, k1_zfmisc_1(B_20)) | ~r1_tarski(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_60])).
% 12.04/5.01  tff(c_788, plain, (![A_98, B_99]: (k2_pre_topc(A_98, B_99)=k2_struct_0(A_98) | ~v1_tops_1(B_99, A_98) | ~m1_subset_1(B_99, k1_zfmisc_1(u1_struct_0(A_98))) | ~l1_pre_topc(A_98))), inference(cnfTransformation, [status(thm)], [f_90])).
% 12.04/5.01  tff(c_810, plain, (![B_99]: (k2_pre_topc('#skF_2', B_99)=k2_struct_0('#skF_2') | ~v1_tops_1(B_99, '#skF_2') | ~m1_subset_1(B_99, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_94, c_788])).
% 12.04/5.01  tff(c_820, plain, (![B_101]: (k2_pre_topc('#skF_2', B_101)=k2_struct_0('#skF_2') | ~v1_tops_1(B_101, '#skF_2') | ~m1_subset_1(B_101, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_810])).
% 12.04/5.01  tff(c_1270, plain, (![A_124]: (k2_pre_topc('#skF_2', A_124)=k2_struct_0('#skF_2') | ~v1_tops_1(A_124, '#skF_2') | ~r1_tarski(A_124, k2_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_28, c_820])).
% 12.04/5.01  tff(c_2310, plain, (![A_151]: (k2_pre_topc('#skF_2', A_151)=k2_struct_0('#skF_2') | ~v1_tops_1(A_151, '#skF_2') | k4_xboole_0(A_151, k2_struct_0('#skF_2'))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_1270])).
% 12.04/5.01  tff(c_2355, plain, (k2_pre_topc('#skF_2', k3_subset_1(k2_struct_0('#skF_2'), '#skF_3'))=k2_struct_0('#skF_2') | ~v1_tops_1(k3_subset_1(k2_struct_0('#skF_2'), '#skF_3'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_633, c_2310])).
% 12.04/5.01  tff(c_2362, plain, (~v1_tops_1(k3_subset_1(k2_struct_0('#skF_2'), '#skF_3'), '#skF_2')), inference(splitLeft, [status(thm)], [c_2355])).
% 12.04/5.01  tff(c_649, plain, (![B_92, A_93]: (v1_tops_1(B_92, A_93) | k2_pre_topc(A_93, B_92)!=k2_struct_0(A_93) | ~m1_subset_1(B_92, k1_zfmisc_1(u1_struct_0(A_93))) | ~l1_pre_topc(A_93))), inference(cnfTransformation, [status(thm)], [f_90])).
% 12.04/5.01  tff(c_671, plain, (![B_92]: (v1_tops_1(B_92, '#skF_2') | k2_pre_topc('#skF_2', B_92)!=k2_struct_0('#skF_2') | ~m1_subset_1(B_92, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_94, c_649])).
% 12.04/5.01  tff(c_756, plain, (![B_97]: (v1_tops_1(B_97, '#skF_2') | k2_pre_topc('#skF_2', B_97)!=k2_struct_0('#skF_2') | ~m1_subset_1(B_97, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_671])).
% 12.04/5.01  tff(c_1238, plain, (![A_123]: (v1_tops_1(A_123, '#skF_2') | k2_pre_topc('#skF_2', A_123)!=k2_struct_0('#skF_2') | ~r1_tarski(A_123, k2_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_28, c_756])).
% 12.04/5.01  tff(c_2232, plain, (![A_148]: (v1_tops_1(A_148, '#skF_2') | k2_pre_topc('#skF_2', A_148)!=k2_struct_0('#skF_2') | k4_xboole_0(A_148, k2_struct_0('#skF_2'))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_1238])).
% 12.04/5.01  tff(c_2273, plain, (v1_tops_1(k3_subset_1(k2_struct_0('#skF_2'), '#skF_3'), '#skF_2') | k2_pre_topc('#skF_2', k3_subset_1(k2_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_633, c_2232])).
% 12.04/5.01  tff(c_2449, plain, (k2_pre_topc('#skF_2', k3_subset_1(k2_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_2362, c_2273])).
% 12.04/5.01  tff(c_20, plain, (![A_14, B_15]: (m1_subset_1(k3_subset_1(A_14, B_15), k1_zfmisc_1(A_14)) | ~m1_subset_1(B_15, k1_zfmisc_1(A_14)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 12.04/5.01  tff(c_267, plain, (![A_72, B_73]: (k3_subset_1(A_72, k3_subset_1(A_72, B_73))=B_73 | ~m1_subset_1(B_73, k1_zfmisc_1(A_72)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 12.04/5.01  tff(c_283, plain, (k3_subset_1(k2_struct_0('#skF_2'), k3_subset_1(k2_struct_0('#skF_2'), '#skF_3'))='#skF_3'), inference(resolution, [status(thm)], [c_95, c_267])).
% 12.04/5.01  tff(c_1176, plain, (![A_121, B_122]: (k3_subset_1(u1_struct_0(A_121), k2_pre_topc(A_121, k3_subset_1(u1_struct_0(A_121), B_122)))=k1_tops_1(A_121, B_122) | ~m1_subset_1(B_122, k1_zfmisc_1(u1_struct_0(A_121))) | ~l1_pre_topc(A_121))), inference(cnfTransformation, [status(thm)], [f_81])).
% 12.04/5.01  tff(c_1220, plain, (![B_122]: (k3_subset_1(k2_struct_0('#skF_2'), k2_pre_topc('#skF_2', k3_subset_1(u1_struct_0('#skF_2'), B_122)))=k1_tops_1('#skF_2', B_122) | ~m1_subset_1(B_122, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_94, c_1176])).
% 12.04/5.01  tff(c_2083, plain, (![B_145]: (k3_subset_1(k2_struct_0('#skF_2'), k2_pre_topc('#skF_2', k3_subset_1(k2_struct_0('#skF_2'), B_145)))=k1_tops_1('#skF_2', B_145) | ~m1_subset_1(B_145, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_94, c_94, c_1220])).
% 12.04/5.01  tff(c_2136, plain, (k3_subset_1(k2_struct_0('#skF_2'), k2_pre_topc('#skF_2', '#skF_3'))=k1_tops_1('#skF_2', k3_subset_1(k2_struct_0('#skF_2'), '#skF_3')) | ~m1_subset_1(k3_subset_1(k2_struct_0('#skF_2'), '#skF_3'), k1_zfmisc_1(k2_struct_0('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_283, c_2083])).
% 12.04/5.01  tff(c_6816, plain, (~m1_subset_1(k3_subset_1(k2_struct_0('#skF_2'), '#skF_3'), k1_zfmisc_1(k2_struct_0('#skF_2')))), inference(splitLeft, [status(thm)], [c_2136])).
% 12.04/5.01  tff(c_6822, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(k2_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_20, c_6816])).
% 12.04/5.01  tff(c_6831, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_95, c_6822])).
% 12.04/5.01  tff(c_6833, plain, (m1_subset_1(k3_subset_1(k2_struct_0('#skF_2'), '#skF_3'), k1_zfmisc_1(k2_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_2136])).
% 12.04/5.01  tff(c_14, plain, (![A_10]: (k1_subset_1(A_10)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_40])).
% 12.04/5.01  tff(c_16, plain, (![A_11]: (k2_subset_1(A_11)=A_11)), inference(cnfTransformation, [status(thm)], [f_42])).
% 12.04/5.01  tff(c_24, plain, (![A_18]: (k3_subset_1(A_18, k1_subset_1(A_18))=k2_subset_1(A_18))), inference(cnfTransformation, [status(thm)], [f_56])).
% 12.04/5.01  tff(c_57, plain, (![A_18]: (k3_subset_1(A_18, k1_subset_1(A_18))=A_18)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_24])).
% 12.04/5.01  tff(c_58, plain, (![A_18]: (k3_subset_1(A_18, k1_xboole_0)=A_18)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_57])).
% 12.04/5.01  tff(c_6879, plain, (r1_tarski(k3_subset_1(k2_struct_0('#skF_2'), '#skF_3'), k2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_6833, c_26])).
% 12.04/5.01  tff(c_56, plain, (v2_tops_1('#skF_3', '#skF_2') | k1_tops_1('#skF_2', '#skF_3')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_109])).
% 12.04/5.01  tff(c_125, plain, (k1_tops_1('#skF_2', '#skF_3')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_100, c_56])).
% 12.04/5.01  tff(c_282, plain, (![B_20, A_19]: (k3_subset_1(B_20, k3_subset_1(B_20, A_19))=A_19 | ~r1_tarski(A_19, B_20))), inference(resolution, [status(thm)], [c_28, c_267])).
% 12.04/5.01  tff(c_19639, plain, (![A_418, A_419]: (k3_subset_1(u1_struct_0(A_418), k2_pre_topc(A_418, A_419))=k1_tops_1(A_418, k3_subset_1(u1_struct_0(A_418), A_419)) | ~m1_subset_1(k3_subset_1(u1_struct_0(A_418), A_419), k1_zfmisc_1(u1_struct_0(A_418))) | ~l1_pre_topc(A_418) | ~r1_tarski(A_419, u1_struct_0(A_418)))), inference(superposition, [status(thm), theory('equality')], [c_282, c_1176])).
% 12.04/5.01  tff(c_19725, plain, (![A_419]: (k3_subset_1(u1_struct_0('#skF_2'), k2_pre_topc('#skF_2', A_419))=k1_tops_1('#skF_2', k3_subset_1(u1_struct_0('#skF_2'), A_419)) | ~m1_subset_1(k3_subset_1(k2_struct_0('#skF_2'), A_419), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~r1_tarski(A_419, u1_struct_0('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_94, c_19639])).
% 12.04/5.01  tff(c_22949, plain, (![A_470]: (k3_subset_1(k2_struct_0('#skF_2'), k2_pre_topc('#skF_2', A_470))=k1_tops_1('#skF_2', k3_subset_1(k2_struct_0('#skF_2'), A_470)) | ~m1_subset_1(k3_subset_1(k2_struct_0('#skF_2'), A_470), k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~r1_tarski(A_470, k2_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_48, c_94, c_94, c_94, c_19725])).
% 12.04/5.01  tff(c_23015, plain, (k3_subset_1(k2_struct_0('#skF_2'), k2_pre_topc('#skF_2', k3_subset_1(k2_struct_0('#skF_2'), '#skF_3')))=k1_tops_1('#skF_2', k3_subset_1(k2_struct_0('#skF_2'), k3_subset_1(k2_struct_0('#skF_2'), '#skF_3'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~r1_tarski(k3_subset_1(k2_struct_0('#skF_2'), '#skF_3'), k2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_283, c_22949])).
% 12.04/5.01  tff(c_23061, plain, (k3_subset_1(k2_struct_0('#skF_2'), k2_pre_topc('#skF_2', k3_subset_1(k2_struct_0('#skF_2'), '#skF_3')))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_6879, c_95, c_125, c_283, c_23015])).
% 12.04/5.01  tff(c_478, plain, (![A_83, B_84]: (m1_subset_1(k2_pre_topc(A_83, B_84), k1_zfmisc_1(u1_struct_0(A_83))) | ~m1_subset_1(B_84, k1_zfmisc_1(u1_struct_0(A_83))) | ~l1_pre_topc(A_83))), inference(cnfTransformation, [status(thm)], [f_70])).
% 12.04/5.01  tff(c_22, plain, (![A_16, B_17]: (k3_subset_1(A_16, k3_subset_1(A_16, B_17))=B_17 | ~m1_subset_1(B_17, k1_zfmisc_1(A_16)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 12.04/5.01  tff(c_3781, plain, (![A_198, B_199]: (k3_subset_1(u1_struct_0(A_198), k3_subset_1(u1_struct_0(A_198), k2_pre_topc(A_198, B_199)))=k2_pre_topc(A_198, B_199) | ~m1_subset_1(B_199, k1_zfmisc_1(u1_struct_0(A_198))) | ~l1_pre_topc(A_198))), inference(resolution, [status(thm)], [c_478, c_22])).
% 12.04/5.01  tff(c_3856, plain, (![B_199]: (k3_subset_1(u1_struct_0('#skF_2'), k3_subset_1(k2_struct_0('#skF_2'), k2_pre_topc('#skF_2', B_199)))=k2_pre_topc('#skF_2', B_199) | ~m1_subset_1(B_199, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_94, c_3781])).
% 12.04/5.01  tff(c_3874, plain, (![B_199]: (k3_subset_1(k2_struct_0('#skF_2'), k3_subset_1(k2_struct_0('#skF_2'), k2_pre_topc('#skF_2', B_199)))=k2_pre_topc('#skF_2', B_199) | ~m1_subset_1(B_199, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_94, c_94, c_3856])).
% 12.04/5.01  tff(c_23138, plain, (k2_pre_topc('#skF_2', k3_subset_1(k2_struct_0('#skF_2'), '#skF_3'))=k3_subset_1(k2_struct_0('#skF_2'), k1_xboole_0) | ~m1_subset_1(k3_subset_1(k2_struct_0('#skF_2'), '#skF_3'), k1_zfmisc_1(k2_struct_0('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_23061, c_3874])).
% 12.04/5.01  tff(c_23235, plain, (k2_pre_topc('#skF_2', k3_subset_1(k2_struct_0('#skF_2'), '#skF_3'))=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_6833, c_58, c_23138])).
% 12.04/5.01  tff(c_23237, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2449, c_23235])).
% 12.04/5.01  tff(c_23239, plain, (v1_tops_1(k3_subset_1(k2_struct_0('#skF_2'), '#skF_3'), '#skF_2')), inference(splitRight, [status(thm)], [c_2355])).
% 12.04/5.01  tff(c_865, plain, (![B_103, A_104]: (v2_tops_1(B_103, A_104) | ~v1_tops_1(k3_subset_1(u1_struct_0(A_104), B_103), A_104) | ~m1_subset_1(B_103, k1_zfmisc_1(u1_struct_0(A_104))) | ~l1_pre_topc(A_104))), inference(cnfTransformation, [status(thm)], [f_99])).
% 12.04/5.01  tff(c_876, plain, (![B_103]: (v2_tops_1(B_103, '#skF_2') | ~v1_tops_1(k3_subset_1(k2_struct_0('#skF_2'), B_103), '#skF_2') | ~m1_subset_1(B_103, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_94, c_865])).
% 12.04/5.01  tff(c_884, plain, (![B_103]: (v2_tops_1(B_103, '#skF_2') | ~v1_tops_1(k3_subset_1(k2_struct_0('#skF_2'), B_103), '#skF_2') | ~m1_subset_1(B_103, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_94, c_876])).
% 12.04/5.01  tff(c_23242, plain, (v2_tops_1('#skF_3', '#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_23239, c_884])).
% 12.04/5.01  tff(c_23245, plain, (v2_tops_1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_95, c_23242])).
% 12.04/5.01  tff(c_23247, plain, $false, inference(negUnitSimplification, [status(thm)], [c_100, c_23245])).
% 12.04/5.01  tff(c_23248, plain, (k1_tops_1('#skF_2', '#skF_3')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_50])).
% 12.04/5.01  tff(c_23286, plain, (![A_483, B_484]: (r2_hidden('#skF_1'(A_483, B_484), A_483) | r1_tarski(A_483, B_484))), inference(cnfTransformation, [status(thm)], [f_32])).
% 12.04/5.01  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 12.04/5.01  tff(c_23292, plain, (![A_485]: (r1_tarski(A_485, A_485))), inference(resolution, [status(thm)], [c_23286, c_4])).
% 12.04/5.01  tff(c_23296, plain, (![A_485]: (k4_xboole_0(A_485, A_485)=k1_xboole_0)), inference(resolution, [status(thm)], [c_23292, c_10])).
% 12.04/5.01  tff(c_23291, plain, (![A_483]: (r1_tarski(A_483, A_483))), inference(resolution, [status(thm)], [c_23286, c_4])).
% 12.04/5.01  tff(c_23389, plain, (![A_498, B_499]: (k4_xboole_0(A_498, B_499)=k3_subset_1(A_498, B_499) | ~m1_subset_1(B_499, k1_zfmisc_1(A_498)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 12.04/5.01  tff(c_23449, plain, (![B_502, A_503]: (k4_xboole_0(B_502, A_503)=k3_subset_1(B_502, A_503) | ~r1_tarski(A_503, B_502))), inference(resolution, [status(thm)], [c_28, c_23389])).
% 12.04/5.01  tff(c_23452, plain, (![A_483]: (k4_xboole_0(A_483, A_483)=k3_subset_1(A_483, A_483))), inference(resolution, [status(thm)], [c_23291, c_23449])).
% 12.04/5.01  tff(c_23460, plain, (![A_483]: (k3_subset_1(A_483, A_483)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_23296, c_23452])).
% 12.04/5.01  tff(c_23249, plain, (v2_tops_1('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_50])).
% 12.04/5.01  tff(c_23995, plain, (![A_531, B_532]: (v1_tops_1(k3_subset_1(u1_struct_0(A_531), B_532), A_531) | ~v2_tops_1(B_532, A_531) | ~m1_subset_1(B_532, k1_zfmisc_1(u1_struct_0(A_531))) | ~l1_pre_topc(A_531))), inference(cnfTransformation, [status(thm)], [f_99])).
% 12.04/5.01  tff(c_24006, plain, (![B_532]: (v1_tops_1(k3_subset_1(k2_struct_0('#skF_2'), B_532), '#skF_2') | ~v2_tops_1(B_532, '#skF_2') | ~m1_subset_1(B_532, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_94, c_23995])).
% 12.04/5.01  tff(c_24014, plain, (![B_532]: (v1_tops_1(k3_subset_1(k2_struct_0('#skF_2'), B_532), '#skF_2') | ~v2_tops_1(B_532, '#skF_2') | ~m1_subset_1(B_532, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_94, c_24006])).
% 12.04/5.01  tff(c_23371, plain, (![A_496, B_497]: (m1_subset_1(k3_subset_1(A_496, B_497), k1_zfmisc_1(A_496)) | ~m1_subset_1(B_497, k1_zfmisc_1(A_496)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 12.04/5.01  tff(c_23625, plain, (![A_514, B_515]: (r1_tarski(k3_subset_1(A_514, B_515), A_514) | ~m1_subset_1(B_515, k1_zfmisc_1(A_514)))), inference(resolution, [status(thm)], [c_23371, c_26])).
% 12.04/5.01  tff(c_23653, plain, (![A_516, B_517]: (k4_xboole_0(k3_subset_1(A_516, B_517), A_516)=k1_xboole_0 | ~m1_subset_1(B_517, k1_zfmisc_1(A_516)))), inference(resolution, [status(thm)], [c_23625, c_10])).
% 12.04/5.01  tff(c_23676, plain, (k4_xboole_0(k3_subset_1(k2_struct_0('#skF_2'), '#skF_3'), k2_struct_0('#skF_2'))=k1_xboole_0), inference(resolution, [status(thm)], [c_95, c_23653])).
% 12.04/5.01  tff(c_23870, plain, (![B_525, A_526]: (v1_tops_1(B_525, A_526) | k2_pre_topc(A_526, B_525)!=k2_struct_0(A_526) | ~m1_subset_1(B_525, k1_zfmisc_1(u1_struct_0(A_526))) | ~l1_pre_topc(A_526))), inference(cnfTransformation, [status(thm)], [f_90])).
% 12.04/5.01  tff(c_23892, plain, (![B_525]: (v1_tops_1(B_525, '#skF_2') | k2_pre_topc('#skF_2', B_525)!=k2_struct_0('#skF_2') | ~m1_subset_1(B_525, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_94, c_23870])).
% 12.04/5.01  tff(c_23928, plain, (![B_528]: (v1_tops_1(B_528, '#skF_2') | k2_pre_topc('#skF_2', B_528)!=k2_struct_0('#skF_2') | ~m1_subset_1(B_528, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_23892])).
% 12.04/5.01  tff(c_24576, plain, (![A_558]: (v1_tops_1(A_558, '#skF_2') | k2_pre_topc('#skF_2', A_558)!=k2_struct_0('#skF_2') | ~r1_tarski(A_558, k2_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_28, c_23928])).
% 12.04/5.01  tff(c_25567, plain, (![A_582]: (v1_tops_1(A_582, '#skF_2') | k2_pre_topc('#skF_2', A_582)!=k2_struct_0('#skF_2') | k4_xboole_0(A_582, k2_struct_0('#skF_2'))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_24576])).
% 12.04/5.01  tff(c_25612, plain, (v1_tops_1(k3_subset_1(k2_struct_0('#skF_2'), '#skF_3'), '#skF_2') | k2_pre_topc('#skF_2', k3_subset_1(k2_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_23676, c_25567])).
% 12.04/5.01  tff(c_25620, plain, (k2_pre_topc('#skF_2', k3_subset_1(k2_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_25612])).
% 12.04/5.01  tff(c_23677, plain, (![A_518, B_519]: (k2_pre_topc(A_518, B_519)=k2_struct_0(A_518) | ~v1_tops_1(B_519, A_518) | ~m1_subset_1(B_519, k1_zfmisc_1(u1_struct_0(A_518))) | ~l1_pre_topc(A_518))), inference(cnfTransformation, [status(thm)], [f_90])).
% 12.04/5.01  tff(c_23699, plain, (![B_519]: (k2_pre_topc('#skF_2', B_519)=k2_struct_0('#skF_2') | ~v1_tops_1(B_519, '#skF_2') | ~m1_subset_1(B_519, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_94, c_23677])).
% 12.04/5.01  tff(c_23781, plain, (![B_523]: (k2_pre_topc('#skF_2', B_523)=k2_struct_0('#skF_2') | ~v1_tops_1(B_523, '#skF_2') | ~m1_subset_1(B_523, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_23699])).
% 12.04/5.01  tff(c_24608, plain, (![A_559]: (k2_pre_topc('#skF_2', A_559)=k2_struct_0('#skF_2') | ~v1_tops_1(A_559, '#skF_2') | ~r1_tarski(A_559, k2_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_28, c_23781])).
% 12.04/5.01  tff(c_25622, plain, (![A_583]: (k2_pre_topc('#skF_2', A_583)=k2_struct_0('#skF_2') | ~v1_tops_1(A_583, '#skF_2') | k4_xboole_0(A_583, k2_struct_0('#skF_2'))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_24608])).
% 12.04/5.01  tff(c_25648, plain, (k2_pre_topc('#skF_2', k3_subset_1(k2_struct_0('#skF_2'), '#skF_3'))=k2_struct_0('#skF_2') | ~v1_tops_1(k3_subset_1(k2_struct_0('#skF_2'), '#skF_3'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_23676, c_25622])).
% 12.04/5.01  tff(c_25673, plain, (~v1_tops_1(k3_subset_1(k2_struct_0('#skF_2'), '#skF_3'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_25620, c_25648])).
% 12.04/5.01  tff(c_25709, plain, (~v2_tops_1('#skF_3', '#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_24014, c_25673])).
% 12.04/5.01  tff(c_25713, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_95, c_23249, c_25709])).
% 12.04/5.01  tff(c_25715, plain, (k2_pre_topc('#skF_2', k3_subset_1(k2_struct_0('#skF_2'), '#skF_3'))=k2_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_25612])).
% 12.04/5.01  tff(c_24165, plain, (![A_544, B_545]: (k3_subset_1(u1_struct_0(A_544), k2_pre_topc(A_544, k3_subset_1(u1_struct_0(A_544), B_545)))=k1_tops_1(A_544, B_545) | ~m1_subset_1(B_545, k1_zfmisc_1(u1_struct_0(A_544))) | ~l1_pre_topc(A_544))), inference(cnfTransformation, [status(thm)], [f_81])).
% 12.04/5.01  tff(c_24206, plain, (![B_545]: (k3_subset_1(k2_struct_0('#skF_2'), k2_pre_topc('#skF_2', k3_subset_1(u1_struct_0('#skF_2'), B_545)))=k1_tops_1('#skF_2', B_545) | ~m1_subset_1(B_545, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_94, c_24165])).
% 12.04/5.01  tff(c_24219, plain, (![B_545]: (k3_subset_1(k2_struct_0('#skF_2'), k2_pre_topc('#skF_2', k3_subset_1(k2_struct_0('#skF_2'), B_545)))=k1_tops_1('#skF_2', B_545) | ~m1_subset_1(B_545, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_94, c_94, c_24206])).
% 12.04/5.01  tff(c_25736, plain, (k3_subset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_2'))=k1_tops_1('#skF_2', '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_struct_0('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_25715, c_24219])).
% 12.04/5.01  tff(c_25752, plain, (k1_tops_1('#skF_2', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_95, c_23460, c_25736])).
% 12.04/5.01  tff(c_25754, plain, $false, inference(negUnitSimplification, [status(thm)], [c_23248, c_25752])).
% 12.04/5.01  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.04/5.01  
% 12.04/5.01  Inference rules
% 12.04/5.01  ----------------------
% 12.04/5.01  #Ref     : 3
% 12.04/5.01  #Sup     : 6111
% 12.04/5.01  #Fact    : 0
% 12.04/5.01  #Define  : 0
% 12.04/5.01  #Split   : 34
% 12.04/5.01  #Chain   : 0
% 12.04/5.01  #Close   : 0
% 12.04/5.01  
% 12.04/5.01  Ordering : KBO
% 12.04/5.01  
% 12.04/5.01  Simplification rules
% 12.04/5.01  ----------------------
% 12.04/5.01  #Subsume      : 1856
% 12.04/5.01  #Demod        : 3823
% 12.04/5.01  #Tautology    : 1861
% 12.04/5.01  #SimpNegUnit  : 356
% 12.04/5.01  #BackRed      : 8
% 12.04/5.01  
% 12.04/5.01  #Partial instantiations: 0
% 12.04/5.01  #Strategies tried      : 1
% 12.04/5.01  
% 12.04/5.01  Timing (in seconds)
% 12.04/5.01  ----------------------
% 12.04/5.01  Preprocessing        : 0.33
% 12.04/5.01  Parsing              : 0.18
% 12.04/5.01  CNF conversion       : 0.02
% 12.04/5.01  Main loop            : 3.92
% 12.04/5.01  Inferencing          : 0.94
% 12.04/5.01  Reduction            : 1.52
% 12.04/5.01  Demodulation         : 1.12
% 12.04/5.01  BG Simplification    : 0.10
% 12.04/5.01  Subsumption          : 1.11
% 12.04/5.01  Abstraction          : 0.15
% 12.04/5.01  MUC search           : 0.00
% 12.04/5.01  Cooper               : 0.00
% 12.04/5.01  Total                : 4.29
% 12.04/5.01  Index Insertion      : 0.00
% 12.04/5.01  Index Deletion       : 0.00
% 12.04/5.01  Index Matching       : 0.00
% 12.04/5.01  BG Taut test         : 0.00
%------------------------------------------------------------------------------
