%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:28 EST 2020

% Result     : Theorem 6.27s
% Output     : CNFRefutation 6.51s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 169 expanded)
%              Number of leaves         :   38 (  73 expanded)
%              Depth                    :   11
%              Number of atoms          :  149 ( 323 expanded)
%              Number of equality atoms :   66 ( 108 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k2_tops_1,type,(
    k2_tops_1: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_118,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tops_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_78,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v4_pre_topc(B,A)
             => k2_pre_topc(A,B) = B )
            & ( ( v2_pre_topc(A)
                & k2_pre_topc(A,B) = B )
             => v4_pre_topc(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).

tff(f_31,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_37,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k4_subset_1(A,B,k3_subset_1(A,B)) = k2_subset_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_subset_1)).

tff(f_106,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_84,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).

tff(f_99,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

tff(c_40,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_4564,plain,(
    ! [A_280,B_281,C_282] :
      ( k7_subset_1(A_280,B_281,C_282) = k4_xboole_0(B_281,C_282)
      | ~ m1_subset_1(B_281,k1_zfmisc_1(A_280)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_4573,plain,(
    ! [C_282] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_282) = k4_xboole_0('#skF_2',C_282) ),
    inference(resolution,[status(thm)],[c_40,c_4564])).

tff(c_52,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_107,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_46,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_181,plain,(
    ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_42,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_44,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_1265,plain,(
    ! [B_127,A_128] :
      ( v4_pre_topc(B_127,A_128)
      | k2_pre_topc(A_128,B_127) != B_127
      | ~ v2_pre_topc(A_128)
      | ~ m1_subset_1(B_127,k1_zfmisc_1(u1_struct_0(A_128)))
      | ~ l1_pre_topc(A_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1287,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2'
    | ~ v2_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_1265])).

tff(c_1295,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_44,c_1287])).

tff(c_1296,plain,(
    k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_181,c_1295])).

tff(c_254,plain,(
    ! [A_69,B_70,C_71] :
      ( k7_subset_1(A_69,B_70,C_71) = k4_xboole_0(B_70,C_71)
      | ~ m1_subset_1(B_70,k1_zfmisc_1(A_69)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_264,plain,(
    ! [C_72] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_72) = k4_xboole_0('#skF_2',C_72) ),
    inference(resolution,[status(thm)],[c_40,c_254])).

tff(c_270,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_264,c_107])).

tff(c_6,plain,(
    ! [A_5,B_6] : r1_tarski(k4_xboole_0(A_5,B_6),A_5) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_126,plain,(
    ! [A_53,B_54] : k4_xboole_0(A_53,k4_xboole_0(A_53,B_54)) = k3_xboole_0(A_53,B_54) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_8,plain,(
    ! [A_7,B_8] : k2_xboole_0(A_7,k4_xboole_0(B_8,A_7)) = k2_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_135,plain,(
    ! [A_53,B_54] : k2_xboole_0(k4_xboole_0(A_53,B_54),k3_xboole_0(A_53,B_54)) = k2_xboole_0(k4_xboole_0(A_53,B_54),A_53) ),
    inference(superposition,[status(thm),theory(equality)],[c_126,c_8])).

tff(c_819,plain,(
    ! [A_109,B_110] : k2_xboole_0(k4_xboole_0(A_109,B_110),k3_xboole_0(A_109,B_110)) = k2_xboole_0(A_109,k4_xboole_0(A_109,B_110)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_135])).

tff(c_861,plain,(
    ! [A_109,B_110] : k2_xboole_0(k3_xboole_0(A_109,B_110),k4_xboole_0(A_109,B_110)) = k2_xboole_0(A_109,k4_xboole_0(A_109,B_110)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_819])).

tff(c_138,plain,(
    ! [A_53,B_54] : r1_tarski(k3_xboole_0(A_53,B_54),A_53) ),
    inference(superposition,[status(thm),theory(equality)],[c_126,c_6])).

tff(c_26,plain,(
    ! [A_24,B_25] :
      ( m1_subset_1(A_24,k1_zfmisc_1(B_25))
      | ~ r1_tarski(A_24,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1026,plain,(
    ! [A_115,B_116,C_117] :
      ( k4_subset_1(A_115,B_116,C_117) = k2_xboole_0(B_116,C_117)
      | ~ m1_subset_1(C_117,k1_zfmisc_1(A_115))
      | ~ m1_subset_1(B_116,k1_zfmisc_1(A_115)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1555,plain,(
    ! [B_144,B_145,A_146] :
      ( k4_subset_1(B_144,B_145,A_146) = k2_xboole_0(B_145,A_146)
      | ~ m1_subset_1(B_145,k1_zfmisc_1(B_144))
      | ~ r1_tarski(A_146,B_144) ) ),
    inference(resolution,[status(thm)],[c_26,c_1026])).

tff(c_1647,plain,(
    ! [B_149,A_150,A_151] :
      ( k4_subset_1(B_149,A_150,A_151) = k2_xboole_0(A_150,A_151)
      | ~ r1_tarski(A_151,B_149)
      | ~ r1_tarski(A_150,B_149) ) ),
    inference(resolution,[status(thm)],[c_26,c_1555])).

tff(c_2198,plain,(
    ! [A_170,A_171,B_172] :
      ( k4_subset_1(A_170,A_171,k3_xboole_0(A_170,B_172)) = k2_xboole_0(A_171,k3_xboole_0(A_170,B_172))
      | ~ r1_tarski(A_171,A_170) ) ),
    inference(resolution,[status(thm)],[c_138,c_1647])).

tff(c_10,plain,(
    ! [A_9,B_10] : k4_xboole_0(A_9,k4_xboole_0(A_9,B_10)) = k3_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_154,plain,(
    ! [A_59,B_60] :
      ( k4_xboole_0(A_59,B_60) = k3_subset_1(A_59,B_60)
      | ~ m1_subset_1(B_60,k1_zfmisc_1(A_59)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_182,plain,(
    ! [B_63,A_64] :
      ( k4_xboole_0(B_63,A_64) = k3_subset_1(B_63,A_64)
      | ~ r1_tarski(A_64,B_63) ) ),
    inference(resolution,[status(thm)],[c_26,c_154])).

tff(c_197,plain,(
    ! [A_5,B_6] : k4_xboole_0(A_5,k4_xboole_0(A_5,B_6)) = k3_subset_1(A_5,k4_xboole_0(A_5,B_6)) ),
    inference(resolution,[status(thm)],[c_6,c_182])).

tff(c_204,plain,(
    ! [A_5,B_6] : k3_subset_1(A_5,k4_xboole_0(A_5,B_6)) = k3_xboole_0(A_5,B_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_197])).

tff(c_12,plain,(
    ! [A_11] : k2_subset_1(A_11) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_22,plain,(
    ! [A_22,B_23] :
      ( k4_subset_1(A_22,B_23,k3_subset_1(A_22,B_23)) = k2_subset_1(A_22)
      | ~ m1_subset_1(B_23,k1_zfmisc_1(A_22)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_357,plain,(
    ! [A_80,B_81] :
      ( k4_subset_1(A_80,B_81,k3_subset_1(A_80,B_81)) = A_80
      | ~ m1_subset_1(B_81,k1_zfmisc_1(A_80)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_22])).

tff(c_367,plain,(
    ! [B_82,A_83] :
      ( k4_subset_1(B_82,A_83,k3_subset_1(B_82,A_83)) = B_82
      | ~ r1_tarski(A_83,B_82) ) ),
    inference(resolution,[status(thm)],[c_26,c_357])).

tff(c_376,plain,(
    ! [A_5,B_6] :
      ( k4_subset_1(A_5,k4_xboole_0(A_5,B_6),k3_xboole_0(A_5,B_6)) = A_5
      | ~ r1_tarski(k4_xboole_0(A_5,B_6),A_5) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_204,c_367])).

tff(c_380,plain,(
    ! [A_5,B_6] : k4_subset_1(A_5,k4_xboole_0(A_5,B_6),k3_xboole_0(A_5,B_6)) = A_5 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_376])).

tff(c_2219,plain,(
    ! [A_170,B_172] :
      ( k2_xboole_0(k4_xboole_0(A_170,B_172),k3_xboole_0(A_170,B_172)) = A_170
      | ~ r1_tarski(k4_xboole_0(A_170,B_172),A_170) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2198,c_380])).

tff(c_2280,plain,(
    ! [A_173,B_174] : k2_xboole_0(A_173,k4_xboole_0(A_173,B_174)) = A_173 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_861,c_2,c_2219])).

tff(c_2311,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_270,c_2280])).

tff(c_1370,plain,(
    ! [A_130,B_131] :
      ( k4_subset_1(u1_struct_0(A_130),B_131,k2_tops_1(A_130,B_131)) = k2_pre_topc(A_130,B_131)
      | ~ m1_subset_1(B_131,k1_zfmisc_1(u1_struct_0(A_130)))
      | ~ l1_pre_topc(A_130) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_1386,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_1370])).

tff(c_1394,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_1386])).

tff(c_32,plain,(
    ! [A_29,B_30] :
      ( m1_subset_1(k2_tops_1(A_29,B_30),k1_zfmisc_1(u1_struct_0(A_29)))
      | ~ m1_subset_1(B_30,k1_zfmisc_1(u1_struct_0(A_29)))
      | ~ l1_pre_topc(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_4237,plain,(
    ! [A_246,B_247,B_248] :
      ( k4_subset_1(u1_struct_0(A_246),B_247,k2_tops_1(A_246,B_248)) = k2_xboole_0(B_247,k2_tops_1(A_246,B_248))
      | ~ m1_subset_1(B_247,k1_zfmisc_1(u1_struct_0(A_246)))
      | ~ m1_subset_1(B_248,k1_zfmisc_1(u1_struct_0(A_246)))
      | ~ l1_pre_topc(A_246) ) ),
    inference(resolution,[status(thm)],[c_32,c_1026])).

tff(c_4253,plain,(
    ! [B_248] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_248)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_248))
      | ~ m1_subset_1(B_248,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_40,c_4237])).

tff(c_4264,plain,(
    ! [B_249] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_249)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_249))
      | ~ m1_subset_1(B_249,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_4253])).

tff(c_4287,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_40,c_4264])).

tff(c_4296,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2311,c_1394,c_4287])).

tff(c_4298,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1296,c_4296])).

tff(c_4299,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_4351,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_4299])).

tff(c_4352,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_4383,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4352,c_46])).

tff(c_4574,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4573,c_4383])).

tff(c_4994,plain,(
    ! [A_319,B_320] :
      ( k2_pre_topc(A_319,B_320) = B_320
      | ~ v4_pre_topc(B_320,A_319)
      | ~ m1_subset_1(B_320,k1_zfmisc_1(u1_struct_0(A_319)))
      | ~ l1_pre_topc(A_319) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_5008,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = '#skF_2'
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_4994])).

tff(c_5014,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_4352,c_5008])).

tff(c_5758,plain,(
    ! [A_364,B_365] :
      ( k7_subset_1(u1_struct_0(A_364),k2_pre_topc(A_364,B_365),k1_tops_1(A_364,B_365)) = k2_tops_1(A_364,B_365)
      | ~ m1_subset_1(B_365,k1_zfmisc_1(u1_struct_0(A_364)))
      | ~ l1_pre_topc(A_364) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_5767,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_5014,c_5758])).

tff(c_5771,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_4573,c_5767])).

tff(c_5773,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4574,c_5771])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 15:53:14 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.27/2.27  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.27/2.28  
% 6.27/2.28  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.27/2.28  %$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > #skF_2 > #skF_1
% 6.27/2.28  
% 6.27/2.28  %Foreground sorts:
% 6.27/2.28  
% 6.27/2.28  
% 6.27/2.28  %Background operators:
% 6.27/2.28  
% 6.27/2.28  
% 6.27/2.28  %Foreground operators:
% 6.27/2.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.27/2.28  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.27/2.28  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 6.27/2.28  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 6.27/2.28  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 6.27/2.28  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.27/2.28  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 6.27/2.28  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 6.27/2.28  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 6.27/2.28  tff('#skF_2', type, '#skF_2': $i).
% 6.27/2.28  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 6.27/2.28  tff('#skF_1', type, '#skF_1': $i).
% 6.27/2.28  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.27/2.28  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 6.27/2.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.27/2.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.27/2.28  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 6.27/2.28  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.27/2.28  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.27/2.28  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 6.27/2.28  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 6.27/2.28  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 6.27/2.28  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.27/2.28  
% 6.51/2.30  tff(f_118, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_tops_1)).
% 6.51/2.30  tff(f_55, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 6.51/2.30  tff(f_78, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 6.51/2.30  tff(f_31, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 6.51/2.30  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 6.51/2.30  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 6.51/2.30  tff(f_33, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 6.51/2.30  tff(f_63, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 6.51/2.30  tff(f_51, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 6.51/2.30  tff(f_41, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 6.51/2.30  tff(f_37, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 6.51/2.30  tff(f_59, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k4_subset_1(A, B, k3_subset_1(A, B)) = k2_subset_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_subset_1)).
% 6.51/2.30  tff(f_106, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tops_1)).
% 6.51/2.30  tff(f_84, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 6.51/2.30  tff(f_99, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l78_tops_1)).
% 6.51/2.30  tff(c_40, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_118])).
% 6.51/2.30  tff(c_4564, plain, (![A_280, B_281, C_282]: (k7_subset_1(A_280, B_281, C_282)=k4_xboole_0(B_281, C_282) | ~m1_subset_1(B_281, k1_zfmisc_1(A_280)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 6.51/2.30  tff(c_4573, plain, (![C_282]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_282)=k4_xboole_0('#skF_2', C_282))), inference(resolution, [status(thm)], [c_40, c_4564])).
% 6.51/2.30  tff(c_52, plain, (v4_pre_topc('#skF_2', '#skF_1') | k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_118])).
% 6.51/2.30  tff(c_107, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_52])).
% 6.51/2.30  tff(c_46, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_118])).
% 6.51/2.30  tff(c_181, plain, (~v4_pre_topc('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_46])).
% 6.51/2.30  tff(c_42, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_118])).
% 6.51/2.30  tff(c_44, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_118])).
% 6.51/2.30  tff(c_1265, plain, (![B_127, A_128]: (v4_pre_topc(B_127, A_128) | k2_pre_topc(A_128, B_127)!=B_127 | ~v2_pre_topc(A_128) | ~m1_subset_1(B_127, k1_zfmisc_1(u1_struct_0(A_128))) | ~l1_pre_topc(A_128))), inference(cnfTransformation, [status(thm)], [f_78])).
% 6.51/2.30  tff(c_1287, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2' | ~v2_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_40, c_1265])).
% 6.51/2.30  tff(c_1295, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_44, c_1287])).
% 6.51/2.30  tff(c_1296, plain, (k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_181, c_1295])).
% 6.51/2.30  tff(c_254, plain, (![A_69, B_70, C_71]: (k7_subset_1(A_69, B_70, C_71)=k4_xboole_0(B_70, C_71) | ~m1_subset_1(B_70, k1_zfmisc_1(A_69)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 6.51/2.30  tff(c_264, plain, (![C_72]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_72)=k4_xboole_0('#skF_2', C_72))), inference(resolution, [status(thm)], [c_40, c_254])).
% 6.51/2.30  tff(c_270, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_264, c_107])).
% 6.51/2.30  tff(c_6, plain, (![A_5, B_6]: (r1_tarski(k4_xboole_0(A_5, B_6), A_5))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.51/2.30  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.51/2.30  tff(c_126, plain, (![A_53, B_54]: (k4_xboole_0(A_53, k4_xboole_0(A_53, B_54))=k3_xboole_0(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.51/2.30  tff(c_8, plain, (![A_7, B_8]: (k2_xboole_0(A_7, k4_xboole_0(B_8, A_7))=k2_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.51/2.30  tff(c_135, plain, (![A_53, B_54]: (k2_xboole_0(k4_xboole_0(A_53, B_54), k3_xboole_0(A_53, B_54))=k2_xboole_0(k4_xboole_0(A_53, B_54), A_53))), inference(superposition, [status(thm), theory('equality')], [c_126, c_8])).
% 6.51/2.30  tff(c_819, plain, (![A_109, B_110]: (k2_xboole_0(k4_xboole_0(A_109, B_110), k3_xboole_0(A_109, B_110))=k2_xboole_0(A_109, k4_xboole_0(A_109, B_110)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_135])).
% 6.51/2.30  tff(c_861, plain, (![A_109, B_110]: (k2_xboole_0(k3_xboole_0(A_109, B_110), k4_xboole_0(A_109, B_110))=k2_xboole_0(A_109, k4_xboole_0(A_109, B_110)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_819])).
% 6.51/2.30  tff(c_138, plain, (![A_53, B_54]: (r1_tarski(k3_xboole_0(A_53, B_54), A_53))), inference(superposition, [status(thm), theory('equality')], [c_126, c_6])).
% 6.51/2.30  tff(c_26, plain, (![A_24, B_25]: (m1_subset_1(A_24, k1_zfmisc_1(B_25)) | ~r1_tarski(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_63])).
% 6.51/2.30  tff(c_1026, plain, (![A_115, B_116, C_117]: (k4_subset_1(A_115, B_116, C_117)=k2_xboole_0(B_116, C_117) | ~m1_subset_1(C_117, k1_zfmisc_1(A_115)) | ~m1_subset_1(B_116, k1_zfmisc_1(A_115)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.51/2.30  tff(c_1555, plain, (![B_144, B_145, A_146]: (k4_subset_1(B_144, B_145, A_146)=k2_xboole_0(B_145, A_146) | ~m1_subset_1(B_145, k1_zfmisc_1(B_144)) | ~r1_tarski(A_146, B_144))), inference(resolution, [status(thm)], [c_26, c_1026])).
% 6.51/2.30  tff(c_1647, plain, (![B_149, A_150, A_151]: (k4_subset_1(B_149, A_150, A_151)=k2_xboole_0(A_150, A_151) | ~r1_tarski(A_151, B_149) | ~r1_tarski(A_150, B_149))), inference(resolution, [status(thm)], [c_26, c_1555])).
% 6.51/2.30  tff(c_2198, plain, (![A_170, A_171, B_172]: (k4_subset_1(A_170, A_171, k3_xboole_0(A_170, B_172))=k2_xboole_0(A_171, k3_xboole_0(A_170, B_172)) | ~r1_tarski(A_171, A_170))), inference(resolution, [status(thm)], [c_138, c_1647])).
% 6.51/2.30  tff(c_10, plain, (![A_9, B_10]: (k4_xboole_0(A_9, k4_xboole_0(A_9, B_10))=k3_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.51/2.30  tff(c_154, plain, (![A_59, B_60]: (k4_xboole_0(A_59, B_60)=k3_subset_1(A_59, B_60) | ~m1_subset_1(B_60, k1_zfmisc_1(A_59)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.51/2.30  tff(c_182, plain, (![B_63, A_64]: (k4_xboole_0(B_63, A_64)=k3_subset_1(B_63, A_64) | ~r1_tarski(A_64, B_63))), inference(resolution, [status(thm)], [c_26, c_154])).
% 6.51/2.30  tff(c_197, plain, (![A_5, B_6]: (k4_xboole_0(A_5, k4_xboole_0(A_5, B_6))=k3_subset_1(A_5, k4_xboole_0(A_5, B_6)))), inference(resolution, [status(thm)], [c_6, c_182])).
% 6.51/2.30  tff(c_204, plain, (![A_5, B_6]: (k3_subset_1(A_5, k4_xboole_0(A_5, B_6))=k3_xboole_0(A_5, B_6))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_197])).
% 6.51/2.30  tff(c_12, plain, (![A_11]: (k2_subset_1(A_11)=A_11)), inference(cnfTransformation, [status(thm)], [f_37])).
% 6.51/2.30  tff(c_22, plain, (![A_22, B_23]: (k4_subset_1(A_22, B_23, k3_subset_1(A_22, B_23))=k2_subset_1(A_22) | ~m1_subset_1(B_23, k1_zfmisc_1(A_22)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.51/2.30  tff(c_357, plain, (![A_80, B_81]: (k4_subset_1(A_80, B_81, k3_subset_1(A_80, B_81))=A_80 | ~m1_subset_1(B_81, k1_zfmisc_1(A_80)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_22])).
% 6.51/2.30  tff(c_367, plain, (![B_82, A_83]: (k4_subset_1(B_82, A_83, k3_subset_1(B_82, A_83))=B_82 | ~r1_tarski(A_83, B_82))), inference(resolution, [status(thm)], [c_26, c_357])).
% 6.51/2.30  tff(c_376, plain, (![A_5, B_6]: (k4_subset_1(A_5, k4_xboole_0(A_5, B_6), k3_xboole_0(A_5, B_6))=A_5 | ~r1_tarski(k4_xboole_0(A_5, B_6), A_5))), inference(superposition, [status(thm), theory('equality')], [c_204, c_367])).
% 6.51/2.30  tff(c_380, plain, (![A_5, B_6]: (k4_subset_1(A_5, k4_xboole_0(A_5, B_6), k3_xboole_0(A_5, B_6))=A_5)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_376])).
% 6.51/2.30  tff(c_2219, plain, (![A_170, B_172]: (k2_xboole_0(k4_xboole_0(A_170, B_172), k3_xboole_0(A_170, B_172))=A_170 | ~r1_tarski(k4_xboole_0(A_170, B_172), A_170))), inference(superposition, [status(thm), theory('equality')], [c_2198, c_380])).
% 6.51/2.30  tff(c_2280, plain, (![A_173, B_174]: (k2_xboole_0(A_173, k4_xboole_0(A_173, B_174))=A_173)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_861, c_2, c_2219])).
% 6.51/2.30  tff(c_2311, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_270, c_2280])).
% 6.51/2.30  tff(c_1370, plain, (![A_130, B_131]: (k4_subset_1(u1_struct_0(A_130), B_131, k2_tops_1(A_130, B_131))=k2_pre_topc(A_130, B_131) | ~m1_subset_1(B_131, k1_zfmisc_1(u1_struct_0(A_130))) | ~l1_pre_topc(A_130))), inference(cnfTransformation, [status(thm)], [f_106])).
% 6.51/2.30  tff(c_1386, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_40, c_1370])).
% 6.51/2.30  tff(c_1394, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_1386])).
% 6.51/2.30  tff(c_32, plain, (![A_29, B_30]: (m1_subset_1(k2_tops_1(A_29, B_30), k1_zfmisc_1(u1_struct_0(A_29))) | ~m1_subset_1(B_30, k1_zfmisc_1(u1_struct_0(A_29))) | ~l1_pre_topc(A_29))), inference(cnfTransformation, [status(thm)], [f_84])).
% 6.51/2.30  tff(c_4237, plain, (![A_246, B_247, B_248]: (k4_subset_1(u1_struct_0(A_246), B_247, k2_tops_1(A_246, B_248))=k2_xboole_0(B_247, k2_tops_1(A_246, B_248)) | ~m1_subset_1(B_247, k1_zfmisc_1(u1_struct_0(A_246))) | ~m1_subset_1(B_248, k1_zfmisc_1(u1_struct_0(A_246))) | ~l1_pre_topc(A_246))), inference(resolution, [status(thm)], [c_32, c_1026])).
% 6.51/2.30  tff(c_4253, plain, (![B_248]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_248))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_248)) | ~m1_subset_1(B_248, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_40, c_4237])).
% 6.51/2.30  tff(c_4264, plain, (![B_249]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_249))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_249)) | ~m1_subset_1(B_249, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_4253])).
% 6.51/2.30  tff(c_4287, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_40, c_4264])).
% 6.51/2.30  tff(c_4296, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2311, c_1394, c_4287])).
% 6.51/2.30  tff(c_4298, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1296, c_4296])).
% 6.51/2.30  tff(c_4299, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_46])).
% 6.51/2.30  tff(c_4351, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_107, c_4299])).
% 6.51/2.30  tff(c_4352, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_52])).
% 6.51/2.30  tff(c_4383, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4352, c_46])).
% 6.51/2.30  tff(c_4574, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4573, c_4383])).
% 6.51/2.30  tff(c_4994, plain, (![A_319, B_320]: (k2_pre_topc(A_319, B_320)=B_320 | ~v4_pre_topc(B_320, A_319) | ~m1_subset_1(B_320, k1_zfmisc_1(u1_struct_0(A_319))) | ~l1_pre_topc(A_319))), inference(cnfTransformation, [status(thm)], [f_78])).
% 6.51/2.30  tff(c_5008, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2' | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_40, c_4994])).
% 6.51/2.30  tff(c_5014, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_4352, c_5008])).
% 6.51/2.30  tff(c_5758, plain, (![A_364, B_365]: (k7_subset_1(u1_struct_0(A_364), k2_pre_topc(A_364, B_365), k1_tops_1(A_364, B_365))=k2_tops_1(A_364, B_365) | ~m1_subset_1(B_365, k1_zfmisc_1(u1_struct_0(A_364))) | ~l1_pre_topc(A_364))), inference(cnfTransformation, [status(thm)], [f_99])).
% 6.51/2.30  tff(c_5767, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_5014, c_5758])).
% 6.51/2.30  tff(c_5771, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_4573, c_5767])).
% 6.51/2.30  tff(c_5773, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4574, c_5771])).
% 6.51/2.30  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.51/2.30  
% 6.51/2.30  Inference rules
% 6.51/2.30  ----------------------
% 6.51/2.30  #Ref     : 0
% 6.51/2.30  #Sup     : 1375
% 6.51/2.30  #Fact    : 0
% 6.51/2.30  #Define  : 0
% 6.51/2.30  #Split   : 3
% 6.51/2.30  #Chain   : 0
% 6.51/2.30  #Close   : 0
% 6.51/2.30  
% 6.51/2.30  Ordering : KBO
% 6.51/2.30  
% 6.51/2.30  Simplification rules
% 6.51/2.30  ----------------------
% 6.51/2.30  #Subsume      : 25
% 6.51/2.30  #Demod        : 1362
% 6.51/2.30  #Tautology    : 754
% 6.51/2.30  #SimpNegUnit  : 5
% 6.51/2.30  #BackRed      : 21
% 6.51/2.30  
% 6.51/2.30  #Partial instantiations: 0
% 6.51/2.30  #Strategies tried      : 1
% 6.51/2.30  
% 6.51/2.30  Timing (in seconds)
% 6.51/2.30  ----------------------
% 6.51/2.30  Preprocessing        : 0.33
% 6.51/2.30  Parsing              : 0.17
% 6.51/2.30  CNF conversion       : 0.02
% 6.51/2.30  Main loop            : 1.21
% 6.51/2.30  Inferencing          : 0.39
% 6.51/2.30  Reduction            : 0.51
% 6.51/2.30  Demodulation         : 0.41
% 6.51/2.30  BG Simplification    : 0.05
% 6.51/2.30  Subsumption          : 0.17
% 6.51/2.30  Abstraction          : 0.07
% 6.51/2.30  MUC search           : 0.00
% 6.51/2.30  Cooper               : 0.00
% 6.51/2.30  Total                : 1.58
% 6.51/2.31  Index Insertion      : 0.00
% 6.51/2.31  Index Deletion       : 0.00
% 6.51/2.31  Index Matching       : 0.00
% 6.51/2.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
