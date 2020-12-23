%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:05 EST 2020

% Result     : Theorem 3.72s
% Output     : CNFRefutation 3.98s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 299 expanded)
%              Number of leaves         :   38 ( 123 expanded)
%              Depth                    :   12
%              Number of atoms          :  172 ( 760 expanded)
%              Number of equality atoms :   36 ( 146 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_tops_1 > v2_tops_1 > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(v2_tops_1,type,(
    v2_tops_1: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(v3_tops_1,type,(
    v3_tops_1: ( $i * $i ) > $o )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

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

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_128,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
             => ( v3_tops_1(B,A)
              <=> B = k2_tops_1(A,B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_tops_1)).

tff(f_98,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> k1_tops_1(A,B) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_tops_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_107,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> r1_tarski(B,k2_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_tops_1)).

tff(f_66,axiom,(
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

tff(f_75,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_tops_1(B,A)
          <=> v2_tops_1(k2_pre_topc(A,B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tops_1)).

tff(f_116,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_tops_1(B,A)
           => v2_tops_1(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_tops_1)).

tff(f_89,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_82,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(c_48,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_50,plain,
    ( k2_tops_1('#skF_1','#skF_2') != '#skF_2'
    | ~ v3_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_59,plain,(
    ~ v3_tops_1('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_46,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_281,plain,(
    ! [A_77,B_78] :
      ( k1_tops_1(A_77,B_78) = k1_xboole_0
      | ~ v2_tops_1(B_78,A_77)
      | ~ m1_subset_1(B_78,k1_zfmisc_1(u1_struct_0(A_77)))
      | ~ l1_pre_topc(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_292,plain,
    ( k1_tops_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ v2_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_281])).

tff(c_297,plain,
    ( k1_tops_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_292])).

tff(c_298,plain,(
    ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_297])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_56,plain,
    ( v3_tops_1('#skF_2','#skF_1')
    | k2_tops_1('#skF_1','#skF_2') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_60,plain,(
    k2_tops_1('#skF_1','#skF_2') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_59,c_56])).

tff(c_413,plain,(
    ! [B_94,A_95] :
      ( v2_tops_1(B_94,A_95)
      | ~ r1_tarski(B_94,k2_tops_1(A_95,B_94))
      | ~ m1_subset_1(B_94,k1_zfmisc_1(u1_struct_0(A_95)))
      | ~ l1_pre_topc(A_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_415,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | ~ r1_tarski('#skF_2','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_413])).

tff(c_417,plain,(
    v2_tops_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_6,c_415])).

tff(c_419,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_298,c_417])).

tff(c_421,plain,(
    v2_tops_1('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_297])).

tff(c_44,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_446,plain,(
    ! [A_96,B_97] :
      ( k2_pre_topc(A_96,B_97) = B_97
      | ~ v4_pre_topc(B_97,A_96)
      | ~ m1_subset_1(B_97,k1_zfmisc_1(u1_struct_0(A_96)))
      | ~ l1_pre_topc(A_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_457,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = '#skF_2'
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_446])).

tff(c_462,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_44,c_457])).

tff(c_572,plain,(
    ! [B_110,A_111] :
      ( v3_tops_1(B_110,A_111)
      | ~ v2_tops_1(k2_pre_topc(A_111,B_110),A_111)
      | ~ m1_subset_1(B_110,k1_zfmisc_1(u1_struct_0(A_111)))
      | ~ l1_pre_topc(A_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_574,plain,
    ( v3_tops_1('#skF_2','#skF_1')
    | ~ v2_tops_1('#skF_2','#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_462,c_572])).

tff(c_576,plain,(
    v3_tops_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_421,c_574])).

tff(c_578,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_59,c_576])).

tff(c_580,plain,(
    v3_tops_1('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_735,plain,(
    ! [B_142,A_143] :
      ( v2_tops_1(B_142,A_143)
      | ~ v3_tops_1(B_142,A_143)
      | ~ m1_subset_1(B_142,k1_zfmisc_1(u1_struct_0(A_143)))
      | ~ l1_pre_topc(A_143) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_746,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | ~ v3_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_735])).

tff(c_751,plain,(
    v2_tops_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_580,c_746])).

tff(c_800,plain,(
    ! [A_152,B_153] :
      ( k1_tops_1(A_152,B_153) = k1_xboole_0
      | ~ v2_tops_1(B_153,A_152)
      | ~ m1_subset_1(B_153,k1_zfmisc_1(u1_struct_0(A_152)))
      | ~ l1_pre_topc(A_152) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_811,plain,
    ( k1_tops_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ v2_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_800])).

tff(c_816,plain,(
    k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_751,c_811])).

tff(c_690,plain,(
    ! [A_135,B_136] :
      ( r1_tarski(k1_tops_1(A_135,B_136),B_136)
      | ~ m1_subset_1(B_136,k1_zfmisc_1(u1_struct_0(A_135)))
      | ~ l1_pre_topc(A_135) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_698,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_690])).

tff(c_703,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_698])).

tff(c_820,plain,(
    r1_tarski(k1_xboole_0,'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_816,c_703])).

tff(c_20,plain,(
    ! [A_14,B_15] :
      ( m1_subset_1(A_14,k1_zfmisc_1(B_15))
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_579,plain,(
    k2_tops_1('#skF_1','#skF_2') != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_939,plain,(
    ! [B_164,A_165] :
      ( r1_tarski(B_164,k2_tops_1(A_165,B_164))
      | ~ v2_tops_1(B_164,A_165)
      | ~ m1_subset_1(B_164,k1_zfmisc_1(u1_struct_0(A_165)))
      | ~ l1_pre_topc(A_165) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_947,plain,
    ( r1_tarski('#skF_2',k2_tops_1('#skF_1','#skF_2'))
    | ~ v2_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_939])).

tff(c_952,plain,(
    r1_tarski('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_751,c_947])).

tff(c_622,plain,(
    ! [A_122,B_123] :
      ( k4_xboole_0(A_122,B_123) = k3_subset_1(A_122,B_123)
      | ~ m1_subset_1(B_123,k1_zfmisc_1(A_122)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_629,plain,(
    ! [B_15,A_14] :
      ( k4_xboole_0(B_15,A_14) = k3_subset_1(B_15,A_14)
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(resolution,[status(thm)],[c_20,c_622])).

tff(c_855,plain,(
    k4_xboole_0('#skF_2',k1_xboole_0) = k3_subset_1('#skF_2',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_820,c_629])).

tff(c_671,plain,(
    ! [A_131,B_132,C_133] :
      ( k7_subset_1(A_131,B_132,C_133) = k4_xboole_0(B_132,C_133)
      | ~ m1_subset_1(B_132,k1_zfmisc_1(A_131)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_680,plain,(
    ! [C_133] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_133) = k4_xboole_0('#skF_2',C_133) ),
    inference(resolution,[status(thm)],[c_46,c_671])).

tff(c_830,plain,(
    ! [A_154,B_155] :
      ( k2_pre_topc(A_154,B_155) = B_155
      | ~ v4_pre_topc(B_155,A_154)
      | ~ m1_subset_1(B_155,k1_zfmisc_1(u1_struct_0(A_154)))
      | ~ l1_pre_topc(A_154) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_841,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = '#skF_2'
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_830])).

tff(c_846,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_44,c_841])).

tff(c_1198,plain,(
    ! [A_201,B_202] :
      ( k7_subset_1(u1_struct_0(A_201),k2_pre_topc(A_201,B_202),k1_tops_1(A_201,B_202)) = k2_tops_1(A_201,B_202)
      | ~ m1_subset_1(B_202,k1_zfmisc_1(u1_struct_0(A_201)))
      | ~ l1_pre_topc(A_201) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_1207,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_846,c_1198])).

tff(c_1214,plain,(
    k3_subset_1('#skF_2',k1_xboole_0) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_855,c_816,c_680,c_1207])).

tff(c_654,plain,(
    ! [A_127,B_128] :
      ( m1_subset_1(k3_subset_1(A_127,B_128),k1_zfmisc_1(A_127))
      | ~ m1_subset_1(B_128,k1_zfmisc_1(A_127)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_18,plain,(
    ! [A_14,B_15] :
      ( r1_tarski(A_14,B_15)
      | ~ m1_subset_1(A_14,k1_zfmisc_1(B_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_663,plain,(
    ! [A_129,B_130] :
      ( r1_tarski(k3_subset_1(A_129,B_130),A_129)
      | ~ m1_subset_1(B_130,k1_zfmisc_1(A_129)) ) ),
    inference(resolution,[status(thm)],[c_654,c_18])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_670,plain,(
    ! [A_129,B_130] :
      ( k3_subset_1(A_129,B_130) = A_129
      | ~ r1_tarski(A_129,k3_subset_1(A_129,B_130))
      | ~ m1_subset_1(B_130,k1_zfmisc_1(A_129)) ) ),
    inference(resolution,[status(thm)],[c_663,c_2])).

tff(c_1227,plain,
    ( k3_subset_1('#skF_2',k1_xboole_0) = '#skF_2'
    | ~ r1_tarski('#skF_2',k2_tops_1('#skF_1','#skF_2'))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1214,c_670])).

tff(c_1241,plain,
    ( k2_tops_1('#skF_1','#skF_2') = '#skF_2'
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_952,c_1214,c_1227])).

tff(c_1242,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_579,c_1241])).

tff(c_1247,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_2') ),
    inference(resolution,[status(thm)],[c_20,c_1242])).

tff(c_1251,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_820,c_1247])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n014.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 16:50:07 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.72/1.81  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.88/1.82  
% 3.88/1.82  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.88/1.82  %$ v4_pre_topc > v3_tops_1 > v2_tops_1 > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1
% 3.88/1.82  
% 3.88/1.82  %Foreground sorts:
% 3.88/1.82  
% 3.88/1.82  
% 3.88/1.82  %Background operators:
% 3.88/1.82  
% 3.88/1.82  
% 3.88/1.82  %Foreground operators:
% 3.88/1.82  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.88/1.82  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.88/1.82  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 3.88/1.82  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.88/1.82  tff(v2_tops_1, type, v2_tops_1: ($i * $i) > $o).
% 3.88/1.82  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.88/1.82  tff(v3_tops_1, type, v3_tops_1: ($i * $i) > $o).
% 3.88/1.82  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.88/1.82  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.88/1.82  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.88/1.82  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 3.88/1.82  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 3.88/1.82  tff('#skF_2', type, '#skF_2': $i).
% 3.88/1.82  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 3.88/1.82  tff('#skF_1', type, '#skF_1': $i).
% 3.88/1.82  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.88/1.82  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 3.88/1.82  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.88/1.82  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.88/1.82  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.88/1.82  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.88/1.82  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.88/1.82  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 3.88/1.82  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.88/1.82  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.88/1.82  
% 3.98/1.84  tff(f_128, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => (v3_tops_1(B, A) <=> (B = k2_tops_1(A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_tops_1)).
% 3.98/1.84  tff(f_98, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (k1_tops_1(A, B) = k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t84_tops_1)).
% 3.98/1.84  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.98/1.84  tff(f_107, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> r1_tarski(B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_tops_1)).
% 3.98/1.84  tff(f_66, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_pre_topc)).
% 3.98/1.84  tff(f_75, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tops_1(B, A) <=> v2_tops_1(k2_pre_topc(A, B), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_tops_1)).
% 3.98/1.84  tff(f_116, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tops_1(B, A) => v2_tops_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_tops_1)).
% 3.98/1.84  tff(f_89, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tops_1)).
% 3.98/1.84  tff(f_51, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.98/1.84  tff(f_37, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 3.98/1.84  tff(f_45, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 3.98/1.84  tff(f_82, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l78_tops_1)).
% 3.98/1.84  tff(f_41, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 3.98/1.84  tff(c_48, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.98/1.84  tff(c_50, plain, (k2_tops_1('#skF_1', '#skF_2')!='#skF_2' | ~v3_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.98/1.84  tff(c_59, plain, (~v3_tops_1('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_50])).
% 3.98/1.84  tff(c_46, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.98/1.84  tff(c_281, plain, (![A_77, B_78]: (k1_tops_1(A_77, B_78)=k1_xboole_0 | ~v2_tops_1(B_78, A_77) | ~m1_subset_1(B_78, k1_zfmisc_1(u1_struct_0(A_77))) | ~l1_pre_topc(A_77))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.98/1.84  tff(c_292, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0 | ~v2_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_46, c_281])).
% 3.98/1.84  tff(c_297, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0 | ~v2_tops_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_292])).
% 3.98/1.84  tff(c_298, plain, (~v2_tops_1('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_297])).
% 3.98/1.84  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.98/1.84  tff(c_56, plain, (v3_tops_1('#skF_2', '#skF_1') | k2_tops_1('#skF_1', '#skF_2')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.98/1.84  tff(c_60, plain, (k2_tops_1('#skF_1', '#skF_2')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_59, c_56])).
% 3.98/1.84  tff(c_413, plain, (![B_94, A_95]: (v2_tops_1(B_94, A_95) | ~r1_tarski(B_94, k2_tops_1(A_95, B_94)) | ~m1_subset_1(B_94, k1_zfmisc_1(u1_struct_0(A_95))) | ~l1_pre_topc(A_95))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.98/1.84  tff(c_415, plain, (v2_tops_1('#skF_2', '#skF_1') | ~r1_tarski('#skF_2', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_60, c_413])).
% 3.98/1.84  tff(c_417, plain, (v2_tops_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_6, c_415])).
% 3.98/1.84  tff(c_419, plain, $false, inference(negUnitSimplification, [status(thm)], [c_298, c_417])).
% 3.98/1.84  tff(c_421, plain, (v2_tops_1('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_297])).
% 3.98/1.84  tff(c_44, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.98/1.84  tff(c_446, plain, (![A_96, B_97]: (k2_pre_topc(A_96, B_97)=B_97 | ~v4_pre_topc(B_97, A_96) | ~m1_subset_1(B_97, k1_zfmisc_1(u1_struct_0(A_96))) | ~l1_pre_topc(A_96))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.98/1.84  tff(c_457, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2' | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_46, c_446])).
% 3.98/1.84  tff(c_462, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_44, c_457])).
% 3.98/1.84  tff(c_572, plain, (![B_110, A_111]: (v3_tops_1(B_110, A_111) | ~v2_tops_1(k2_pre_topc(A_111, B_110), A_111) | ~m1_subset_1(B_110, k1_zfmisc_1(u1_struct_0(A_111))) | ~l1_pre_topc(A_111))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.98/1.84  tff(c_574, plain, (v3_tops_1('#skF_2', '#skF_1') | ~v2_tops_1('#skF_2', '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_462, c_572])).
% 3.98/1.84  tff(c_576, plain, (v3_tops_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_421, c_574])).
% 3.98/1.84  tff(c_578, plain, $false, inference(negUnitSimplification, [status(thm)], [c_59, c_576])).
% 3.98/1.84  tff(c_580, plain, (v3_tops_1('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_50])).
% 3.98/1.84  tff(c_735, plain, (![B_142, A_143]: (v2_tops_1(B_142, A_143) | ~v3_tops_1(B_142, A_143) | ~m1_subset_1(B_142, k1_zfmisc_1(u1_struct_0(A_143))) | ~l1_pre_topc(A_143))), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.98/1.84  tff(c_746, plain, (v2_tops_1('#skF_2', '#skF_1') | ~v3_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_46, c_735])).
% 3.98/1.84  tff(c_751, plain, (v2_tops_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_580, c_746])).
% 3.98/1.84  tff(c_800, plain, (![A_152, B_153]: (k1_tops_1(A_152, B_153)=k1_xboole_0 | ~v2_tops_1(B_153, A_152) | ~m1_subset_1(B_153, k1_zfmisc_1(u1_struct_0(A_152))) | ~l1_pre_topc(A_152))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.98/1.84  tff(c_811, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0 | ~v2_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_46, c_800])).
% 3.98/1.84  tff(c_816, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_48, c_751, c_811])).
% 3.98/1.84  tff(c_690, plain, (![A_135, B_136]: (r1_tarski(k1_tops_1(A_135, B_136), B_136) | ~m1_subset_1(B_136, k1_zfmisc_1(u1_struct_0(A_135))) | ~l1_pre_topc(A_135))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.98/1.84  tff(c_698, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_46, c_690])).
% 3.98/1.84  tff(c_703, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_698])).
% 3.98/1.84  tff(c_820, plain, (r1_tarski(k1_xboole_0, '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_816, c_703])).
% 3.98/1.84  tff(c_20, plain, (![A_14, B_15]: (m1_subset_1(A_14, k1_zfmisc_1(B_15)) | ~r1_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.98/1.84  tff(c_579, plain, (k2_tops_1('#skF_1', '#skF_2')!='#skF_2'), inference(splitRight, [status(thm)], [c_50])).
% 3.98/1.84  tff(c_939, plain, (![B_164, A_165]: (r1_tarski(B_164, k2_tops_1(A_165, B_164)) | ~v2_tops_1(B_164, A_165) | ~m1_subset_1(B_164, k1_zfmisc_1(u1_struct_0(A_165))) | ~l1_pre_topc(A_165))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.98/1.84  tff(c_947, plain, (r1_tarski('#skF_2', k2_tops_1('#skF_1', '#skF_2')) | ~v2_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_46, c_939])).
% 3.98/1.84  tff(c_952, plain, (r1_tarski('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_751, c_947])).
% 3.98/1.84  tff(c_622, plain, (![A_122, B_123]: (k4_xboole_0(A_122, B_123)=k3_subset_1(A_122, B_123) | ~m1_subset_1(B_123, k1_zfmisc_1(A_122)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.98/1.84  tff(c_629, plain, (![B_15, A_14]: (k4_xboole_0(B_15, A_14)=k3_subset_1(B_15, A_14) | ~r1_tarski(A_14, B_15))), inference(resolution, [status(thm)], [c_20, c_622])).
% 3.98/1.84  tff(c_855, plain, (k4_xboole_0('#skF_2', k1_xboole_0)=k3_subset_1('#skF_2', k1_xboole_0)), inference(resolution, [status(thm)], [c_820, c_629])).
% 3.98/1.84  tff(c_671, plain, (![A_131, B_132, C_133]: (k7_subset_1(A_131, B_132, C_133)=k4_xboole_0(B_132, C_133) | ~m1_subset_1(B_132, k1_zfmisc_1(A_131)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.98/1.84  tff(c_680, plain, (![C_133]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_133)=k4_xboole_0('#skF_2', C_133))), inference(resolution, [status(thm)], [c_46, c_671])).
% 3.98/1.84  tff(c_830, plain, (![A_154, B_155]: (k2_pre_topc(A_154, B_155)=B_155 | ~v4_pre_topc(B_155, A_154) | ~m1_subset_1(B_155, k1_zfmisc_1(u1_struct_0(A_154))) | ~l1_pre_topc(A_154))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.98/1.84  tff(c_841, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2' | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_46, c_830])).
% 3.98/1.84  tff(c_846, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_44, c_841])).
% 3.98/1.84  tff(c_1198, plain, (![A_201, B_202]: (k7_subset_1(u1_struct_0(A_201), k2_pre_topc(A_201, B_202), k1_tops_1(A_201, B_202))=k2_tops_1(A_201, B_202) | ~m1_subset_1(B_202, k1_zfmisc_1(u1_struct_0(A_201))) | ~l1_pre_topc(A_201))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.98/1.84  tff(c_1207, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_846, c_1198])).
% 3.98/1.84  tff(c_1214, plain, (k3_subset_1('#skF_2', k1_xboole_0)=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_855, c_816, c_680, c_1207])).
% 3.98/1.84  tff(c_654, plain, (![A_127, B_128]: (m1_subset_1(k3_subset_1(A_127, B_128), k1_zfmisc_1(A_127)) | ~m1_subset_1(B_128, k1_zfmisc_1(A_127)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.98/1.84  tff(c_18, plain, (![A_14, B_15]: (r1_tarski(A_14, B_15) | ~m1_subset_1(A_14, k1_zfmisc_1(B_15)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.98/1.84  tff(c_663, plain, (![A_129, B_130]: (r1_tarski(k3_subset_1(A_129, B_130), A_129) | ~m1_subset_1(B_130, k1_zfmisc_1(A_129)))), inference(resolution, [status(thm)], [c_654, c_18])).
% 3.98/1.84  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.98/1.84  tff(c_670, plain, (![A_129, B_130]: (k3_subset_1(A_129, B_130)=A_129 | ~r1_tarski(A_129, k3_subset_1(A_129, B_130)) | ~m1_subset_1(B_130, k1_zfmisc_1(A_129)))), inference(resolution, [status(thm)], [c_663, c_2])).
% 3.98/1.84  tff(c_1227, plain, (k3_subset_1('#skF_2', k1_xboole_0)='#skF_2' | ~r1_tarski('#skF_2', k2_tops_1('#skF_1', '#skF_2')) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1214, c_670])).
% 3.98/1.84  tff(c_1241, plain, (k2_tops_1('#skF_1', '#skF_2')='#skF_2' | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_952, c_1214, c_1227])).
% 3.98/1.84  tff(c_1242, plain, (~m1_subset_1(k1_xboole_0, k1_zfmisc_1('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_579, c_1241])).
% 3.98/1.84  tff(c_1247, plain, (~r1_tarski(k1_xboole_0, '#skF_2')), inference(resolution, [status(thm)], [c_20, c_1242])).
% 3.98/1.84  tff(c_1251, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_820, c_1247])).
% 3.98/1.84  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.98/1.84  
% 3.98/1.84  Inference rules
% 3.98/1.84  ----------------------
% 3.98/1.84  #Ref     : 0
% 3.98/1.84  #Sup     : 257
% 3.98/1.84  #Fact    : 0
% 3.98/1.84  #Define  : 0
% 3.98/1.84  #Split   : 6
% 3.98/1.84  #Chain   : 0
% 3.98/1.84  #Close   : 0
% 3.98/1.84  
% 3.98/1.84  Ordering : KBO
% 3.98/1.84  
% 3.98/1.84  Simplification rules
% 3.98/1.84  ----------------------
% 3.98/1.84  #Subsume      : 9
% 3.98/1.84  #Demod        : 136
% 3.98/1.84  #Tautology    : 113
% 3.98/1.84  #SimpNegUnit  : 9
% 3.98/1.84  #BackRed      : 9
% 3.98/1.84  
% 3.98/1.84  #Partial instantiations: 0
% 3.98/1.84  #Strategies tried      : 1
% 3.98/1.84  
% 3.98/1.84  Timing (in seconds)
% 3.98/1.84  ----------------------
% 3.98/1.85  Preprocessing        : 0.41
% 3.98/1.85  Parsing              : 0.22
% 3.98/1.85  CNF conversion       : 0.03
% 3.98/1.85  Main loop            : 0.60
% 3.98/1.85  Inferencing          : 0.22
% 3.98/1.85  Reduction            : 0.19
% 3.98/1.85  Demodulation         : 0.13
% 3.98/1.85  BG Simplification    : 0.03
% 3.98/1.85  Subsumption          : 0.10
% 3.98/1.85  Abstraction          : 0.03
% 3.98/1.85  MUC search           : 0.00
% 3.98/1.85  Cooper               : 0.00
% 3.98/1.85  Total                : 1.06
% 3.98/1.85  Index Insertion      : 0.00
% 3.98/1.85  Index Deletion       : 0.00
% 3.98/1.85  Index Matching       : 0.00
% 3.98/1.85  BG Taut test         : 0.00
%------------------------------------------------------------------------------
