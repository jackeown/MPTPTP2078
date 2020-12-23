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
% DateTime   : Thu Dec  3 10:21:35 EST 2020

% Result     : Theorem 6.52s
% Output     : CNFRefutation 6.87s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 288 expanded)
%              Number of leaves         :   39 ( 114 expanded)
%              Depth                    :   10
%              Number of atoms          :  166 ( 612 expanded)
%              Number of equality atoms :   69 ( 163 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k2_tops_1,type,(
    k2_tops_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_123,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_tops_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_82,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v4_pre_topc(B,A)
             => k2_pre_topc(A,B) = B )
            & ( ( v2_pre_topc(A)
                & k2_pre_topc(A,B) = B )
             => v4_pre_topc(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).

tff(f_95,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_33,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_39,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_88,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_104,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_pre_topc(B,A)
           => r1_tarski(k2_tops_1(A,B),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_tops_1)).

tff(f_111,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tops_1)).

tff(c_44,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_5481,plain,(
    ! [A_242,B_243,C_244] :
      ( k7_subset_1(A_242,B_243,C_244) = k4_xboole_0(B_243,C_244)
      | ~ m1_subset_1(B_243,k1_zfmisc_1(A_242)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_5487,plain,(
    ! [C_244] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_244) = k4_xboole_0('#skF_2',C_244) ),
    inference(resolution,[status(thm)],[c_44,c_5481])).

tff(c_50,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_82,plain,(
    ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_46,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_48,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_2019,plain,(
    ! [B_128,A_129] :
      ( v4_pre_topc(B_128,A_129)
      | k2_pre_topc(A_129,B_128) != B_128
      | ~ v2_pre_topc(A_129)
      | ~ m1_subset_1(B_128,k1_zfmisc_1(u1_struct_0(A_129)))
      | ~ l1_pre_topc(A_129) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_2029,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2'
    | ~ v2_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_2019])).

tff(c_2034,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_48,c_2029])).

tff(c_2035,plain,(
    k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_2034])).

tff(c_2378,plain,(
    ! [A_138,B_139] :
      ( k4_subset_1(u1_struct_0(A_138),B_139,k2_tops_1(A_138,B_139)) = k2_pre_topc(A_138,B_139)
      | ~ m1_subset_1(B_139,k1_zfmisc_1(u1_struct_0(A_138)))
      | ~ l1_pre_topc(A_138) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_2385,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_2378])).

tff(c_2390,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_2385])).

tff(c_992,plain,(
    ! [A_96,B_97,C_98] :
      ( k7_subset_1(A_96,B_97,C_98) = k4_xboole_0(B_97,C_98)
      | ~ m1_subset_1(B_97,k1_zfmisc_1(A_96)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_999,plain,(
    ! [C_99] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_99) = k4_xboole_0('#skF_2',C_99) ),
    inference(resolution,[status(thm)],[c_44,c_992])).

tff(c_56,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_182,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_56])).

tff(c_1005,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_999,c_182])).

tff(c_8,plain,(
    ! [A_5] : k2_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_12,plain,(
    ! [A_8] : r1_tarski(k1_xboole_0,A_8) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_114,plain,(
    ! [A_55,B_56] :
      ( k4_xboole_0(A_55,B_56) = k1_xboole_0
      | ~ r1_tarski(A_55,B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_134,plain,(
    ! [A_8] : k4_xboole_0(k1_xboole_0,A_8) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12,c_114])).

tff(c_273,plain,(
    ! [A_63,B_64] : k5_xboole_0(A_63,k4_xboole_0(B_64,A_63)) = k2_xboole_0(A_63,B_64) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_291,plain,(
    ! [A_8] : k5_xboole_0(A_8,k1_xboole_0) = k2_xboole_0(A_8,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_134,c_273])).

tff(c_297,plain,(
    ! [A_8] : k5_xboole_0(A_8,k1_xboole_0) = A_8 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_291])).

tff(c_14,plain,(
    ! [A_9,B_10] : r1_tarski(k4_xboole_0(A_9,B_10),A_9) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_133,plain,(
    ! [A_9,B_10] : k4_xboole_0(k4_xboole_0(A_9,B_10),A_9) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14,c_114])).

tff(c_282,plain,(
    ! [A_9,B_10] : k2_xboole_0(A_9,k4_xboole_0(A_9,B_10)) = k5_xboole_0(A_9,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_133,c_273])).

tff(c_589,plain,(
    ! [A_9,B_10] : k2_xboole_0(A_9,k4_xboole_0(A_9,B_10)) = A_9 ),
    inference(demodulation,[status(thm),theory(equality)],[c_297,c_282])).

tff(c_1029,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_1005,c_589])).

tff(c_1311,plain,(
    ! [A_104,B_105] :
      ( m1_subset_1(k2_tops_1(A_104,B_105),k1_zfmisc_1(u1_struct_0(A_104)))
      | ~ m1_subset_1(B_105,k1_zfmisc_1(u1_struct_0(A_104)))
      | ~ l1_pre_topc(A_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_22,plain,(
    ! [A_16,B_17] :
      ( k3_subset_1(A_16,k3_subset_1(A_16,B_17)) = B_17
      | ~ m1_subset_1(B_17,k1_zfmisc_1(A_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1327,plain,(
    ! [A_104,B_105] :
      ( k3_subset_1(u1_struct_0(A_104),k3_subset_1(u1_struct_0(A_104),k2_tops_1(A_104,B_105))) = k2_tops_1(A_104,B_105)
      | ~ m1_subset_1(B_105,k1_zfmisc_1(u1_struct_0(A_104)))
      | ~ l1_pre_topc(A_104) ) ),
    inference(resolution,[status(thm)],[c_1311,c_22])).

tff(c_20,plain,(
    ! [A_14,B_15] :
      ( k4_xboole_0(A_14,B_15) = k3_subset_1(A_14,B_15)
      | ~ m1_subset_1(B_15,k1_zfmisc_1(A_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_4049,plain,(
    ! [A_188,B_189] :
      ( k4_xboole_0(u1_struct_0(A_188),k2_tops_1(A_188,B_189)) = k3_subset_1(u1_struct_0(A_188),k2_tops_1(A_188,B_189))
      | ~ m1_subset_1(B_189,k1_zfmisc_1(u1_struct_0(A_188)))
      | ~ l1_pre_topc(A_188) ) ),
    inference(resolution,[status(thm)],[c_1311,c_20])).

tff(c_4056,plain,
    ( k4_xboole_0(u1_struct_0('#skF_1'),k2_tops_1('#skF_1','#skF_2')) = k3_subset_1(u1_struct_0('#skF_1'),k2_tops_1('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_4049])).

tff(c_4061,plain,(
    k4_xboole_0(u1_struct_0('#skF_1'),k2_tops_1('#skF_1','#skF_2')) = k3_subset_1(u1_struct_0('#skF_1'),k2_tops_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_4056])).

tff(c_30,plain,(
    ! [A_24,B_25] :
      ( m1_subset_1(A_24,k1_zfmisc_1(B_25))
      | ~ r1_tarski(A_24,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_482,plain,(
    ! [A_74,B_75] :
      ( k4_xboole_0(A_74,B_75) = k3_subset_1(A_74,B_75)
      | ~ m1_subset_1(B_75,k1_zfmisc_1(A_74)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_627,plain,(
    ! [B_80,A_81] :
      ( k4_xboole_0(B_80,A_81) = k3_subset_1(B_80,A_81)
      | ~ r1_tarski(A_81,B_80) ) ),
    inference(resolution,[status(thm)],[c_30,c_482])).

tff(c_742,plain,(
    ! [A_88,B_89] : k4_xboole_0(A_88,k4_xboole_0(A_88,B_89)) = k3_subset_1(A_88,k4_xboole_0(A_88,B_89)) ),
    inference(resolution,[status(thm)],[c_14,c_627])).

tff(c_770,plain,(
    ! [A_88,B_89] : r1_tarski(k3_subset_1(A_88,k4_xboole_0(A_88,B_89)),A_88) ),
    inference(superposition,[status(thm),theory(equality)],[c_742,c_14])).

tff(c_4198,plain,(
    r1_tarski(k3_subset_1(u1_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),k2_tops_1('#skF_1','#skF_2'))),u1_struct_0('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_4061,c_770])).

tff(c_4790,plain,
    ( r1_tarski(k2_tops_1('#skF_1','#skF_2'),u1_struct_0('#skF_1'))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1327,c_4198])).

tff(c_4810,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_4790])).

tff(c_1574,plain,(
    ! [A_117,B_118,C_119] :
      ( k4_subset_1(A_117,B_118,C_119) = k2_xboole_0(B_118,C_119)
      | ~ m1_subset_1(C_119,k1_zfmisc_1(A_117))
      | ~ m1_subset_1(B_118,k1_zfmisc_1(A_117)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_2615,plain,(
    ! [B_147,B_148,A_149] :
      ( k4_subset_1(B_147,B_148,A_149) = k2_xboole_0(B_148,A_149)
      | ~ m1_subset_1(B_148,k1_zfmisc_1(B_147))
      | ~ r1_tarski(A_149,B_147) ) ),
    inference(resolution,[status(thm)],[c_30,c_1574])).

tff(c_2624,plain,(
    ! [A_149] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',A_149) = k2_xboole_0('#skF_2',A_149)
      | ~ r1_tarski(A_149,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_44,c_2615])).

tff(c_4823,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_4810,c_2624])).

tff(c_4848,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2390,c_1029,c_4823])).

tff(c_4850,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2035,c_4848])).

tff(c_4851,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_5513,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5487,c_4851])).

tff(c_4852,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_6137,plain,(
    ! [A_272,B_273] :
      ( r1_tarski(k2_tops_1(A_272,B_273),B_273)
      | ~ v4_pre_topc(B_273,A_272)
      | ~ m1_subset_1(B_273,k1_zfmisc_1(u1_struct_0(A_272)))
      | ~ l1_pre_topc(A_272) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_6144,plain,
    ( r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_6137])).

tff(c_6149,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_4852,c_6144])).

tff(c_5371,plain,(
    ! [A_237,B_238] :
      ( k4_xboole_0(A_237,B_238) = k3_subset_1(A_237,B_238)
      | ~ m1_subset_1(B_238,k1_zfmisc_1(A_237)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_5378,plain,(
    ! [B_25,A_24] :
      ( k4_xboole_0(B_25,A_24) = k3_subset_1(B_25,A_24)
      | ~ r1_tarski(A_24,B_25) ) ),
    inference(resolution,[status(thm)],[c_30,c_5371])).

tff(c_6162,plain,(
    k4_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k3_subset_1('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_6149,c_5378])).

tff(c_6907,plain,(
    ! [A_292,B_293] :
      ( k7_subset_1(u1_struct_0(A_292),B_293,k2_tops_1(A_292,B_293)) = k1_tops_1(A_292,B_293)
      | ~ m1_subset_1(B_293,k1_zfmisc_1(u1_struct_0(A_292)))
      | ~ l1_pre_topc(A_292) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_6914,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_6907])).

tff(c_6919,plain,(
    k3_subset_1('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_6162,c_5487,c_6914])).

tff(c_5327,plain,(
    ! [A_233,B_234] :
      ( k3_subset_1(A_233,k3_subset_1(A_233,B_234)) = B_234
      | ~ m1_subset_1(B_234,k1_zfmisc_1(A_233)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_5332,plain,(
    ! [B_25,A_24] :
      ( k3_subset_1(B_25,k3_subset_1(B_25,A_24)) = A_24
      | ~ r1_tarski(A_24,B_25) ) ),
    inference(resolution,[status(thm)],[c_30,c_5327])).

tff(c_6930,plain,
    ( k3_subset_1('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_6919,c_5332])).

tff(c_6934,plain,(
    k3_subset_1('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6149,c_6930])).

tff(c_6926,plain,(
    k4_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6919,c_6162])).

tff(c_5440,plain,(
    ! [B_239,A_240] :
      ( k4_xboole_0(B_239,A_240) = k3_subset_1(B_239,A_240)
      | ~ r1_tarski(A_240,B_239) ) ),
    inference(resolution,[status(thm)],[c_30,c_5371])).

tff(c_5466,plain,(
    ! [A_9,B_10] : k4_xboole_0(A_9,k4_xboole_0(A_9,B_10)) = k3_subset_1(A_9,k4_xboole_0(A_9,B_10)) ),
    inference(resolution,[status(thm)],[c_14,c_5440])).

tff(c_7062,plain,(
    k3_subset_1('#skF_2',k4_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2'))) = k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_6926,c_5466])).

tff(c_7086,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k3_subset_1('#skF_2',k1_tops_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6926,c_7062])).

tff(c_7244,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6934,c_7086])).

tff(c_7245,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5513,c_7244])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n009.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:19:56 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.52/2.48  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.52/2.50  
% 6.52/2.50  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.52/2.50  %$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1
% 6.52/2.50  
% 6.52/2.50  %Foreground sorts:
% 6.52/2.50  
% 6.52/2.50  
% 6.52/2.50  %Background operators:
% 6.52/2.50  
% 6.52/2.50  
% 6.52/2.50  %Foreground operators:
% 6.52/2.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.52/2.50  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.52/2.50  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 6.52/2.50  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.52/2.50  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 6.52/2.50  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 6.52/2.50  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.52/2.50  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 6.52/2.50  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 6.52/2.50  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 6.52/2.50  tff('#skF_2', type, '#skF_2': $i).
% 6.52/2.50  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 6.52/2.50  tff('#skF_1', type, '#skF_1': $i).
% 6.52/2.50  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.52/2.50  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 6.52/2.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.52/2.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.52/2.50  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 6.52/2.50  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.52/2.50  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.52/2.50  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 6.52/2.50  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 6.52/2.50  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.52/2.50  
% 6.87/2.52  tff(f_123, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_tops_1)).
% 6.87/2.52  tff(f_63, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 6.87/2.52  tff(f_82, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_pre_topc)).
% 6.87/2.52  tff(f_95, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_tops_1)).
% 6.87/2.52  tff(f_33, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 6.87/2.52  tff(f_39, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 6.87/2.52  tff(f_29, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 6.87/2.52  tff(f_45, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 6.87/2.52  tff(f_41, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 6.87/2.52  tff(f_88, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 6.87/2.52  tff(f_53, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 6.87/2.52  tff(f_49, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 6.87/2.52  tff(f_67, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 6.87/2.52  tff(f_59, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 6.87/2.52  tff(f_104, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => r1_tarski(k2_tops_1(A, B), B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_tops_1)).
% 6.87/2.52  tff(f_111, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_tops_1)).
% 6.87/2.52  tff(c_44, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_123])).
% 6.87/2.52  tff(c_5481, plain, (![A_242, B_243, C_244]: (k7_subset_1(A_242, B_243, C_244)=k4_xboole_0(B_243, C_244) | ~m1_subset_1(B_243, k1_zfmisc_1(A_242)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 6.87/2.52  tff(c_5487, plain, (![C_244]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_244)=k4_xboole_0('#skF_2', C_244))), inference(resolution, [status(thm)], [c_44, c_5481])).
% 6.87/2.52  tff(c_50, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_123])).
% 6.87/2.52  tff(c_82, plain, (~v4_pre_topc('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_50])).
% 6.87/2.52  tff(c_46, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_123])).
% 6.87/2.52  tff(c_48, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_123])).
% 6.87/2.52  tff(c_2019, plain, (![B_128, A_129]: (v4_pre_topc(B_128, A_129) | k2_pre_topc(A_129, B_128)!=B_128 | ~v2_pre_topc(A_129) | ~m1_subset_1(B_128, k1_zfmisc_1(u1_struct_0(A_129))) | ~l1_pre_topc(A_129))), inference(cnfTransformation, [status(thm)], [f_82])).
% 6.87/2.52  tff(c_2029, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2' | ~v2_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_44, c_2019])).
% 6.87/2.52  tff(c_2034, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_46, c_48, c_2029])).
% 6.87/2.52  tff(c_2035, plain, (k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_82, c_2034])).
% 6.87/2.52  tff(c_2378, plain, (![A_138, B_139]: (k4_subset_1(u1_struct_0(A_138), B_139, k2_tops_1(A_138, B_139))=k2_pre_topc(A_138, B_139) | ~m1_subset_1(B_139, k1_zfmisc_1(u1_struct_0(A_138))) | ~l1_pre_topc(A_138))), inference(cnfTransformation, [status(thm)], [f_95])).
% 6.87/2.52  tff(c_2385, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_44, c_2378])).
% 6.87/2.52  tff(c_2390, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_2385])).
% 6.87/2.52  tff(c_992, plain, (![A_96, B_97, C_98]: (k7_subset_1(A_96, B_97, C_98)=k4_xboole_0(B_97, C_98) | ~m1_subset_1(B_97, k1_zfmisc_1(A_96)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 6.87/2.52  tff(c_999, plain, (![C_99]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_99)=k4_xboole_0('#skF_2', C_99))), inference(resolution, [status(thm)], [c_44, c_992])).
% 6.87/2.52  tff(c_56, plain, (v4_pre_topc('#skF_2', '#skF_1') | k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_123])).
% 6.87/2.52  tff(c_182, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_82, c_56])).
% 6.87/2.52  tff(c_1005, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_999, c_182])).
% 6.87/2.52  tff(c_8, plain, (![A_5]: (k2_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.87/2.52  tff(c_12, plain, (![A_8]: (r1_tarski(k1_xboole_0, A_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.87/2.52  tff(c_114, plain, (![A_55, B_56]: (k4_xboole_0(A_55, B_56)=k1_xboole_0 | ~r1_tarski(A_55, B_56))), inference(cnfTransformation, [status(thm)], [f_29])).
% 6.87/2.52  tff(c_134, plain, (![A_8]: (k4_xboole_0(k1_xboole_0, A_8)=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_114])).
% 6.87/2.52  tff(c_273, plain, (![A_63, B_64]: (k5_xboole_0(A_63, k4_xboole_0(B_64, A_63))=k2_xboole_0(A_63, B_64))), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.87/2.52  tff(c_291, plain, (![A_8]: (k5_xboole_0(A_8, k1_xboole_0)=k2_xboole_0(A_8, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_134, c_273])).
% 6.87/2.52  tff(c_297, plain, (![A_8]: (k5_xboole_0(A_8, k1_xboole_0)=A_8)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_291])).
% 6.87/2.52  tff(c_14, plain, (![A_9, B_10]: (r1_tarski(k4_xboole_0(A_9, B_10), A_9))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.87/2.52  tff(c_133, plain, (![A_9, B_10]: (k4_xboole_0(k4_xboole_0(A_9, B_10), A_9)=k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_114])).
% 6.87/2.52  tff(c_282, plain, (![A_9, B_10]: (k2_xboole_0(A_9, k4_xboole_0(A_9, B_10))=k5_xboole_0(A_9, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_133, c_273])).
% 6.87/2.52  tff(c_589, plain, (![A_9, B_10]: (k2_xboole_0(A_9, k4_xboole_0(A_9, B_10))=A_9)), inference(demodulation, [status(thm), theory('equality')], [c_297, c_282])).
% 6.87/2.52  tff(c_1029, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_1005, c_589])).
% 6.87/2.52  tff(c_1311, plain, (![A_104, B_105]: (m1_subset_1(k2_tops_1(A_104, B_105), k1_zfmisc_1(u1_struct_0(A_104))) | ~m1_subset_1(B_105, k1_zfmisc_1(u1_struct_0(A_104))) | ~l1_pre_topc(A_104))), inference(cnfTransformation, [status(thm)], [f_88])).
% 6.87/2.52  tff(c_22, plain, (![A_16, B_17]: (k3_subset_1(A_16, k3_subset_1(A_16, B_17))=B_17 | ~m1_subset_1(B_17, k1_zfmisc_1(A_16)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.87/2.52  tff(c_1327, plain, (![A_104, B_105]: (k3_subset_1(u1_struct_0(A_104), k3_subset_1(u1_struct_0(A_104), k2_tops_1(A_104, B_105)))=k2_tops_1(A_104, B_105) | ~m1_subset_1(B_105, k1_zfmisc_1(u1_struct_0(A_104))) | ~l1_pre_topc(A_104))), inference(resolution, [status(thm)], [c_1311, c_22])).
% 6.87/2.52  tff(c_20, plain, (![A_14, B_15]: (k4_xboole_0(A_14, B_15)=k3_subset_1(A_14, B_15) | ~m1_subset_1(B_15, k1_zfmisc_1(A_14)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.87/2.52  tff(c_4049, plain, (![A_188, B_189]: (k4_xboole_0(u1_struct_0(A_188), k2_tops_1(A_188, B_189))=k3_subset_1(u1_struct_0(A_188), k2_tops_1(A_188, B_189)) | ~m1_subset_1(B_189, k1_zfmisc_1(u1_struct_0(A_188))) | ~l1_pre_topc(A_188))), inference(resolution, [status(thm)], [c_1311, c_20])).
% 6.87/2.52  tff(c_4056, plain, (k4_xboole_0(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', '#skF_2'))=k3_subset_1(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_44, c_4049])).
% 6.87/2.52  tff(c_4061, plain, (k4_xboole_0(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', '#skF_2'))=k3_subset_1(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_4056])).
% 6.87/2.52  tff(c_30, plain, (![A_24, B_25]: (m1_subset_1(A_24, k1_zfmisc_1(B_25)) | ~r1_tarski(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_67])).
% 6.87/2.52  tff(c_482, plain, (![A_74, B_75]: (k4_xboole_0(A_74, B_75)=k3_subset_1(A_74, B_75) | ~m1_subset_1(B_75, k1_zfmisc_1(A_74)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.87/2.52  tff(c_627, plain, (![B_80, A_81]: (k4_xboole_0(B_80, A_81)=k3_subset_1(B_80, A_81) | ~r1_tarski(A_81, B_80))), inference(resolution, [status(thm)], [c_30, c_482])).
% 6.87/2.52  tff(c_742, plain, (![A_88, B_89]: (k4_xboole_0(A_88, k4_xboole_0(A_88, B_89))=k3_subset_1(A_88, k4_xboole_0(A_88, B_89)))), inference(resolution, [status(thm)], [c_14, c_627])).
% 6.87/2.52  tff(c_770, plain, (![A_88, B_89]: (r1_tarski(k3_subset_1(A_88, k4_xboole_0(A_88, B_89)), A_88))), inference(superposition, [status(thm), theory('equality')], [c_742, c_14])).
% 6.87/2.52  tff(c_4198, plain, (r1_tarski(k3_subset_1(u1_struct_0('#skF_1'), k3_subset_1(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', '#skF_2'))), u1_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_4061, c_770])).
% 6.87/2.52  tff(c_4790, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), u1_struct_0('#skF_1')) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1327, c_4198])).
% 6.87/2.52  tff(c_4810, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_4790])).
% 6.87/2.52  tff(c_1574, plain, (![A_117, B_118, C_119]: (k4_subset_1(A_117, B_118, C_119)=k2_xboole_0(B_118, C_119) | ~m1_subset_1(C_119, k1_zfmisc_1(A_117)) | ~m1_subset_1(B_118, k1_zfmisc_1(A_117)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.87/2.52  tff(c_2615, plain, (![B_147, B_148, A_149]: (k4_subset_1(B_147, B_148, A_149)=k2_xboole_0(B_148, A_149) | ~m1_subset_1(B_148, k1_zfmisc_1(B_147)) | ~r1_tarski(A_149, B_147))), inference(resolution, [status(thm)], [c_30, c_1574])).
% 6.87/2.52  tff(c_2624, plain, (![A_149]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', A_149)=k2_xboole_0('#skF_2', A_149) | ~r1_tarski(A_149, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_44, c_2615])).
% 6.87/2.52  tff(c_4823, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_4810, c_2624])).
% 6.87/2.52  tff(c_4848, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2390, c_1029, c_4823])).
% 6.87/2.52  tff(c_4850, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2035, c_4848])).
% 6.87/2.52  tff(c_4851, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_50])).
% 6.87/2.52  tff(c_5513, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_5487, c_4851])).
% 6.87/2.52  tff(c_4852, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_50])).
% 6.87/2.52  tff(c_6137, plain, (![A_272, B_273]: (r1_tarski(k2_tops_1(A_272, B_273), B_273) | ~v4_pre_topc(B_273, A_272) | ~m1_subset_1(B_273, k1_zfmisc_1(u1_struct_0(A_272))) | ~l1_pre_topc(A_272))), inference(cnfTransformation, [status(thm)], [f_104])).
% 6.87/2.52  tff(c_6144, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_44, c_6137])).
% 6.87/2.52  tff(c_6149, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_4852, c_6144])).
% 6.87/2.52  tff(c_5371, plain, (![A_237, B_238]: (k4_xboole_0(A_237, B_238)=k3_subset_1(A_237, B_238) | ~m1_subset_1(B_238, k1_zfmisc_1(A_237)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.87/2.52  tff(c_5378, plain, (![B_25, A_24]: (k4_xboole_0(B_25, A_24)=k3_subset_1(B_25, A_24) | ~r1_tarski(A_24, B_25))), inference(resolution, [status(thm)], [c_30, c_5371])).
% 6.87/2.52  tff(c_6162, plain, (k4_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k3_subset_1('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_6149, c_5378])).
% 6.87/2.52  tff(c_6907, plain, (![A_292, B_293]: (k7_subset_1(u1_struct_0(A_292), B_293, k2_tops_1(A_292, B_293))=k1_tops_1(A_292, B_293) | ~m1_subset_1(B_293, k1_zfmisc_1(u1_struct_0(A_292))) | ~l1_pre_topc(A_292))), inference(cnfTransformation, [status(thm)], [f_111])).
% 6.87/2.52  tff(c_6914, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_44, c_6907])).
% 6.87/2.52  tff(c_6919, plain, (k3_subset_1('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_6162, c_5487, c_6914])).
% 6.87/2.52  tff(c_5327, plain, (![A_233, B_234]: (k3_subset_1(A_233, k3_subset_1(A_233, B_234))=B_234 | ~m1_subset_1(B_234, k1_zfmisc_1(A_233)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.87/2.52  tff(c_5332, plain, (![B_25, A_24]: (k3_subset_1(B_25, k3_subset_1(B_25, A_24))=A_24 | ~r1_tarski(A_24, B_25))), inference(resolution, [status(thm)], [c_30, c_5327])).
% 6.87/2.52  tff(c_6930, plain, (k3_subset_1('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_6919, c_5332])).
% 6.87/2.52  tff(c_6934, plain, (k3_subset_1('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_6149, c_6930])).
% 6.87/2.52  tff(c_6926, plain, (k4_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_6919, c_6162])).
% 6.87/2.52  tff(c_5440, plain, (![B_239, A_240]: (k4_xboole_0(B_239, A_240)=k3_subset_1(B_239, A_240) | ~r1_tarski(A_240, B_239))), inference(resolution, [status(thm)], [c_30, c_5371])).
% 6.87/2.52  tff(c_5466, plain, (![A_9, B_10]: (k4_xboole_0(A_9, k4_xboole_0(A_9, B_10))=k3_subset_1(A_9, k4_xboole_0(A_9, B_10)))), inference(resolution, [status(thm)], [c_14, c_5440])).
% 6.87/2.52  tff(c_7062, plain, (k3_subset_1('#skF_2', k4_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2')))=k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_6926, c_5466])).
% 6.87/2.52  tff(c_7086, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k3_subset_1('#skF_2', k1_tops_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_6926, c_7062])).
% 6.87/2.52  tff(c_7244, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_6934, c_7086])).
% 6.87/2.52  tff(c_7245, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5513, c_7244])).
% 6.87/2.52  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.87/2.52  
% 6.87/2.52  Inference rules
% 6.87/2.52  ----------------------
% 6.87/2.52  #Ref     : 0
% 6.87/2.52  #Sup     : 1714
% 6.87/2.52  #Fact    : 0
% 6.87/2.52  #Define  : 0
% 6.87/2.52  #Split   : 8
% 6.87/2.52  #Chain   : 0
% 6.87/2.52  #Close   : 0
% 6.87/2.52  
% 6.87/2.52  Ordering : KBO
% 6.87/2.52  
% 6.87/2.52  Simplification rules
% 6.87/2.52  ----------------------
% 6.87/2.52  #Subsume      : 47
% 6.87/2.52  #Demod        : 1999
% 6.87/2.52  #Tautology    : 1210
% 6.87/2.52  #SimpNegUnit  : 10
% 6.87/2.52  #BackRed      : 18
% 6.87/2.52  
% 6.87/2.52  #Partial instantiations: 0
% 6.87/2.52  #Strategies tried      : 1
% 6.87/2.52  
% 6.87/2.52  Timing (in seconds)
% 6.87/2.52  ----------------------
% 6.87/2.52  Preprocessing        : 0.31
% 6.87/2.52  Parsing              : 0.17
% 6.87/2.52  CNF conversion       : 0.02
% 6.87/2.52  Main loop            : 1.36
% 6.87/2.52  Inferencing          : 0.44
% 6.87/2.52  Reduction            : 0.55
% 6.87/2.52  Demodulation         : 0.43
% 6.87/2.52  BG Simplification    : 0.04
% 6.87/2.52  Subsumption          : 0.20
% 6.87/2.52  Abstraction          : 0.08
% 6.87/2.52  MUC search           : 0.00
% 6.87/2.52  Cooper               : 0.00
% 6.87/2.52  Total                : 1.72
% 6.87/2.53  Index Insertion      : 0.00
% 6.87/2.53  Index Deletion       : 0.00
% 6.87/2.53  Index Matching       : 0.00
% 6.87/2.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------
