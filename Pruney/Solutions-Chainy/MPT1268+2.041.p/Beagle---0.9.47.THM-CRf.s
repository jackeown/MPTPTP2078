%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:52 EST 2020

% Result     : Theorem 6.16s
% Output     : CNFRefutation 6.16s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 527 expanded)
%              Number of leaves         :   35 ( 193 expanded)
%              Depth                    :   17
%              Number of atoms          :  262 (1521 expanded)
%              Number of equality atoms :   21 ( 129 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v2_tops_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_2 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

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

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_118,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v2_tops_1(B,A)
            <=> ! [C] :
                  ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
                 => ( ( r1_tarski(C,B)
                      & v3_pre_topc(C,A) )
                   => C = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_tops_1)).

tff(f_99,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> k1_tops_1(A,B) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_tops_1)).

tff(f_72,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_52,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k1_tops_1(A,B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).

tff(f_42,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k4_xboole_0(B,A))
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_xboole_1)).

tff(f_90,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B,C] :
          ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
         => ( r2_hidden(B,k1_tops_1(A,C))
          <=> ? [D] :
                ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                & v3_pre_topc(D,A)
                & r1_tarski(D,C)
                & r2_hidden(B,D) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_tops_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_48,plain,
    ( k1_xboole_0 != '#skF_5'
    | ~ v2_tops_1('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_68,plain,(
    ~ v2_tops_1('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_44,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_42,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_415,plain,(
    ! [B_101,A_102] :
      ( v2_tops_1(B_101,A_102)
      | k1_tops_1(A_102,B_101) != k1_xboole_0
      | ~ m1_subset_1(B_101,k1_zfmisc_1(u1_struct_0(A_102)))
      | ~ l1_pre_topc(A_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_422,plain,
    ( v2_tops_1('#skF_4','#skF_3')
    | k1_tops_1('#skF_3','#skF_4') != k1_xboole_0
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_415])).

tff(c_426,plain,
    ( v2_tops_1('#skF_4','#skF_3')
    | k1_tops_1('#skF_3','#skF_4') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_422])).

tff(c_427,plain,(
    k1_tops_1('#skF_3','#skF_4') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_426])).

tff(c_150,plain,(
    ! [A_76,B_77] :
      ( r1_tarski(k1_tops_1(A_76,B_77),B_77)
      | ~ m1_subset_1(B_77,k1_zfmisc_1(u1_struct_0(A_76)))
      | ~ l1_pre_topc(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_155,plain,
    ( r1_tarski(k1_tops_1('#skF_3','#skF_4'),'#skF_4')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_150])).

tff(c_159,plain,(
    r1_tarski(k1_tops_1('#skF_3','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_155])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_110,plain,(
    ! [A_63,B_64] :
      ( ~ r2_hidden('#skF_1'(A_63,B_64),B_64)
      | r1_tarski(A_63,B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_115,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_110])).

tff(c_87,plain,(
    ! [A_57,B_58] :
      ( r1_tarski(A_57,B_58)
      | ~ m1_subset_1(A_57,k1_zfmisc_1(B_58)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_95,plain,(
    r1_tarski('#skF_4',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_42,c_87])).

tff(c_129,plain,(
    ! [A_71,C_72,B_73] :
      ( r1_tarski(A_71,C_72)
      | ~ r1_tarski(B_73,C_72)
      | ~ r1_tarski(A_71,B_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_163,plain,(
    ! [A_78] :
      ( r1_tarski(A_78,u1_struct_0('#skF_3'))
      | ~ r1_tarski(A_78,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_95,c_129])).

tff(c_10,plain,(
    ! [A_8,C_10,B_9] :
      ( r1_tarski(A_8,C_10)
      | ~ r1_tarski(B_9,C_10)
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_194,plain,(
    ! [A_81,A_82] :
      ( r1_tarski(A_81,u1_struct_0('#skF_3'))
      | ~ r1_tarski(A_81,A_82)
      | ~ r1_tarski(A_82,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_163,c_10])).

tff(c_198,plain,
    ( r1_tarski(k1_tops_1('#skF_3','#skF_4'),u1_struct_0('#skF_3'))
    | ~ r1_tarski('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_159,c_194])).

tff(c_208,plain,(
    r1_tarski(k1_tops_1('#skF_3','#skF_4'),u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_115,c_198])).

tff(c_20,plain,(
    ! [A_16,B_17] :
      ( m1_subset_1(A_16,k1_zfmisc_1(B_17))
      | ~ r1_tarski(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_66,plain,(
    ! [C_47] :
      ( v2_tops_1('#skF_4','#skF_3')
      | k1_xboole_0 = C_47
      | ~ v3_pre_topc(C_47,'#skF_3')
      | ~ r1_tarski(C_47,'#skF_4')
      | ~ m1_subset_1(C_47,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_181,plain,(
    ! [C_80] :
      ( k1_xboole_0 = C_80
      | ~ v3_pre_topc(C_80,'#skF_3')
      | ~ r1_tarski(C_80,'#skF_4')
      | ~ m1_subset_1(C_80,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_66])).

tff(c_375,plain,(
    ! [A_100] :
      ( k1_xboole_0 = A_100
      | ~ v3_pre_topc(A_100,'#skF_3')
      | ~ r1_tarski(A_100,'#skF_4')
      | ~ r1_tarski(A_100,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_20,c_181])).

tff(c_386,plain,
    ( k1_tops_1('#skF_3','#skF_4') = k1_xboole_0
    | ~ v3_pre_topc(k1_tops_1('#skF_3','#skF_4'),'#skF_3')
    | ~ r1_tarski(k1_tops_1('#skF_3','#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_208,c_375])).

tff(c_405,plain,
    ( k1_tops_1('#skF_3','#skF_4') = k1_xboole_0
    | ~ v3_pre_topc(k1_tops_1('#skF_3','#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_159,c_386])).

tff(c_429,plain,(
    ~ v3_pre_topc(k1_tops_1('#skF_3','#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_427,c_405])).

tff(c_46,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_479,plain,(
    ! [A_109,B_110] :
      ( v3_pre_topc(k1_tops_1(A_109,B_110),A_109)
      | ~ m1_subset_1(B_110,k1_zfmisc_1(u1_struct_0(A_109)))
      | ~ l1_pre_topc(A_109)
      | ~ v2_pre_topc(A_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_484,plain,
    ( v3_pre_topc(k1_tops_1('#skF_3','#skF_4'),'#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_479])).

tff(c_488,plain,(
    v3_pre_topc(k1_tops_1('#skF_3','#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_484])).

tff(c_490,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_429,c_488])).

tff(c_491,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_492,plain,(
    v2_tops_1('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_50,plain,
    ( v3_pre_topc('#skF_5','#skF_3')
    | ~ v2_tops_1('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_494,plain,(
    v3_pre_topc('#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_492,c_50])).

tff(c_52,plain,
    ( r1_tarski('#skF_5','#skF_4')
    | ~ v2_tops_1('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_497,plain,(
    r1_tarski('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_492,c_52])).

tff(c_54,plain,
    ( m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ v2_tops_1('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_535,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_492,c_54])).

tff(c_12,plain,(
    ! [A_11] : r1_tarski(k1_xboole_0,A_11) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_687,plain,(
    ! [A_151,B_152] :
      ( r1_tarski(k1_tops_1(A_151,B_152),B_152)
      | ~ m1_subset_1(B_152,k1_zfmisc_1(u1_struct_0(A_151)))
      | ~ l1_pre_topc(A_151) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_856,plain,(
    ! [A_160,A_161] :
      ( r1_tarski(k1_tops_1(A_160,A_161),A_161)
      | ~ l1_pre_topc(A_160)
      | ~ r1_tarski(A_161,u1_struct_0(A_160)) ) ),
    inference(resolution,[status(thm)],[c_20,c_687])).

tff(c_558,plain,(
    ! [A_130,C_131,B_132] :
      ( r1_tarski(A_130,C_131)
      | ~ r1_tarski(B_132,C_131)
      | ~ r1_tarski(A_130,B_132) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_573,plain,(
    ! [A_130,A_11] :
      ( r1_tarski(A_130,A_11)
      | ~ r1_tarski(A_130,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_12,c_558])).

tff(c_879,plain,(
    ! [A_160,A_11] :
      ( r1_tarski(k1_tops_1(A_160,k1_xboole_0),A_11)
      | ~ l1_pre_topc(A_160)
      | ~ r1_tarski(k1_xboole_0,u1_struct_0(A_160)) ) ),
    inference(resolution,[status(thm)],[c_856,c_573])).

tff(c_903,plain,(
    ! [A_162,A_163] :
      ( r1_tarski(k1_tops_1(A_162,k1_xboole_0),A_163)
      | ~ l1_pre_topc(A_162) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_879])).

tff(c_14,plain,(
    ! [A_12,B_13] :
      ( k1_xboole_0 = A_12
      | ~ r1_tarski(A_12,k4_xboole_0(B_13,A_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_952,plain,(
    ! [A_164] :
      ( k1_tops_1(A_164,k1_xboole_0) = k1_xboole_0
      | ~ l1_pre_topc(A_164) ) ),
    inference(resolution,[status(thm)],[c_903,c_14])).

tff(c_956,plain,(
    k1_tops_1('#skF_3',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_44,c_952])).

tff(c_1224,plain,(
    ! [A_189,B_190,C_191] :
      ( r1_tarski('#skF_2'(A_189,B_190,C_191),C_191)
      | ~ r2_hidden(B_190,k1_tops_1(A_189,C_191))
      | ~ m1_subset_1(C_191,k1_zfmisc_1(u1_struct_0(A_189)))
      | ~ l1_pre_topc(A_189)
      | ~ v2_pre_topc(A_189) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_1226,plain,(
    ! [B_190] :
      ( r1_tarski('#skF_2'('#skF_3',B_190,k1_xboole_0),k1_xboole_0)
      | ~ r2_hidden(B_190,k1_xboole_0)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_956,c_1224])).

tff(c_1236,plain,(
    ! [B_190] :
      ( r1_tarski('#skF_2'('#skF_3',B_190,k1_xboole_0),k1_xboole_0)
      | ~ r2_hidden(B_190,k1_xboole_0)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_1226])).

tff(c_1309,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_1236])).

tff(c_1312,plain,(
    ~ r1_tarski(k1_xboole_0,u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_20,c_1309])).

tff(c_1316,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_1312])).

tff(c_1363,plain,(
    ! [B_195] :
      ( r1_tarski('#skF_2'('#skF_3',B_195,k1_xboole_0),k1_xboole_0)
      | ~ r2_hidden(B_195,k1_xboole_0) ) ),
    inference(splitRight,[status(thm)],[c_1236])).

tff(c_1378,plain,(
    ! [B_195,A_11] :
      ( r1_tarski('#skF_2'('#skF_3',B_195,k1_xboole_0),A_11)
      | ~ r2_hidden(B_195,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_1363,c_573])).

tff(c_1318,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_1236])).

tff(c_1381,plain,(
    ! [B_197,A_198,C_199] :
      ( r2_hidden(B_197,'#skF_2'(A_198,B_197,C_199))
      | ~ r2_hidden(B_197,k1_tops_1(A_198,C_199))
      | ~ m1_subset_1(C_199,k1_zfmisc_1(u1_struct_0(A_198)))
      | ~ l1_pre_topc(A_198)
      | ~ v2_pre_topc(A_198) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_1383,plain,(
    ! [B_197] :
      ( r2_hidden(B_197,'#skF_2'('#skF_3',B_197,k1_xboole_0))
      | ~ r2_hidden(B_197,k1_xboole_0)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_956,c_1381])).

tff(c_1422,plain,(
    ! [B_202] :
      ( r2_hidden(B_202,'#skF_2'('#skF_3',B_202,k1_xboole_0))
      | ~ r2_hidden(B_202,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_1318,c_1383])).

tff(c_22,plain,(
    ! [B_19,A_18] :
      ( ~ r1_tarski(B_19,A_18)
      | ~ r2_hidden(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1509,plain,(
    ! [B_206] :
      ( ~ r1_tarski('#skF_2'('#skF_3',B_206,k1_xboole_0),B_206)
      | ~ r2_hidden(B_206,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_1422,c_22])).

tff(c_1522,plain,(
    ! [A_11] : ~ r2_hidden(A_11,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_1378,c_1509])).

tff(c_779,plain,(
    ! [A_154,B_155] :
      ( k1_tops_1(A_154,B_155) = k1_xboole_0
      | ~ v2_tops_1(B_155,A_154)
      | ~ m1_subset_1(B_155,k1_zfmisc_1(u1_struct_0(A_154)))
      | ~ l1_pre_topc(A_154) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_789,plain,
    ( k1_tops_1('#skF_3','#skF_4') = k1_xboole_0
    | ~ v2_tops_1('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_779])).

tff(c_796,plain,(
    k1_tops_1('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_492,c_789])).

tff(c_1578,plain,(
    ! [B_212,A_213,C_214,D_215] :
      ( r2_hidden(B_212,k1_tops_1(A_213,C_214))
      | ~ r2_hidden(B_212,D_215)
      | ~ r1_tarski(D_215,C_214)
      | ~ v3_pre_topc(D_215,A_213)
      | ~ m1_subset_1(D_215,k1_zfmisc_1(u1_struct_0(A_213)))
      | ~ m1_subset_1(C_214,k1_zfmisc_1(u1_struct_0(A_213)))
      | ~ l1_pre_topc(A_213)
      | ~ v2_pre_topc(A_213) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_3016,plain,(
    ! [A_352,B_353,A_354,C_355] :
      ( r2_hidden('#skF_1'(A_352,B_353),k1_tops_1(A_354,C_355))
      | ~ r1_tarski(A_352,C_355)
      | ~ v3_pre_topc(A_352,A_354)
      | ~ m1_subset_1(A_352,k1_zfmisc_1(u1_struct_0(A_354)))
      | ~ m1_subset_1(C_355,k1_zfmisc_1(u1_struct_0(A_354)))
      | ~ l1_pre_topc(A_354)
      | ~ v2_pre_topc(A_354)
      | r1_tarski(A_352,B_353) ) ),
    inference(resolution,[status(thm)],[c_6,c_1578])).

tff(c_3037,plain,(
    ! [A_352,B_353] :
      ( r2_hidden('#skF_1'(A_352,B_353),k1_xboole_0)
      | ~ r1_tarski(A_352,'#skF_4')
      | ~ v3_pre_topc(A_352,'#skF_3')
      | ~ m1_subset_1(A_352,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | r1_tarski(A_352,B_353) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_796,c_3016])).

tff(c_3048,plain,(
    ! [A_352,B_353] :
      ( r2_hidden('#skF_1'(A_352,B_353),k1_xboole_0)
      | ~ r1_tarski(A_352,'#skF_4')
      | ~ v3_pre_topc(A_352,'#skF_3')
      | ~ m1_subset_1(A_352,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | r1_tarski(A_352,B_353) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_3037])).

tff(c_3076,plain,(
    ! [A_358,B_359] :
      ( ~ r1_tarski(A_358,'#skF_4')
      | ~ v3_pre_topc(A_358,'#skF_3')
      | ~ m1_subset_1(A_358,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | r1_tarski(A_358,B_359) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1522,c_3048])).

tff(c_3083,plain,(
    ! [B_359] :
      ( ~ r1_tarski('#skF_5','#skF_4')
      | ~ v3_pre_topc('#skF_5','#skF_3')
      | r1_tarski('#skF_5',B_359) ) ),
    inference(resolution,[status(thm)],[c_535,c_3076])).

tff(c_3097,plain,(
    ! [B_359] : r1_tarski('#skF_5',B_359) ),
    inference(demodulation,[status(thm),theory(equality)],[c_494,c_497,c_3083])).

tff(c_689,plain,
    ( r1_tarski(k1_tops_1('#skF_3','#skF_5'),'#skF_5')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_535,c_687])).

tff(c_697,plain,(
    r1_tarski(k1_tops_1('#skF_3','#skF_5'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_689])).

tff(c_574,plain,(
    ! [C_133,B_134,A_135] :
      ( r2_hidden(C_133,B_134)
      | ~ r2_hidden(C_133,A_135)
      | ~ r1_tarski(A_135,B_134) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_663,plain,(
    ! [A_145,B_146,B_147] :
      ( r2_hidden('#skF_1'(A_145,B_146),B_147)
      | ~ r1_tarski(A_145,B_147)
      | r1_tarski(A_145,B_146) ) ),
    inference(resolution,[status(thm)],[c_6,c_574])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1585,plain,(
    ! [A_216,B_217,B_218,B_219] :
      ( r2_hidden('#skF_1'(A_216,B_217),B_218)
      | ~ r1_tarski(B_219,B_218)
      | ~ r1_tarski(A_216,B_219)
      | r1_tarski(A_216,B_217) ) ),
    inference(resolution,[status(thm)],[c_663,c_2])).

tff(c_1680,plain,(
    ! [A_235,B_236] :
      ( r2_hidden('#skF_1'(A_235,B_236),'#skF_5')
      | ~ r1_tarski(A_235,k1_tops_1('#skF_3','#skF_5'))
      | r1_tarski(A_235,B_236) ) ),
    inference(resolution,[status(thm)],[c_697,c_1585])).

tff(c_2728,plain,(
    ! [A_333,B_334,B_335] :
      ( r2_hidden('#skF_1'(A_333,B_334),B_335)
      | ~ r1_tarski('#skF_5',B_335)
      | ~ r1_tarski(A_333,k1_tops_1('#skF_3','#skF_5'))
      | r1_tarski(A_333,B_334) ) ),
    inference(resolution,[status(thm)],[c_1680,c_2])).

tff(c_2751,plain,(
    ! [A_333,B_334] :
      ( ~ r1_tarski('#skF_5',k1_xboole_0)
      | ~ r1_tarski(A_333,k1_tops_1('#skF_3','#skF_5'))
      | r1_tarski(A_333,B_334) ) ),
    inference(resolution,[status(thm)],[c_2728,c_1522])).

tff(c_2780,plain,(
    ~ r1_tarski('#skF_5',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_2751])).

tff(c_3126,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3097,c_2780])).

tff(c_3128,plain,(
    r1_tarski('#skF_5',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_2751])).

tff(c_3224,plain,(
    ! [A_364] : r1_tarski('#skF_5',A_364) ),
    inference(resolution,[status(thm)],[c_3128,c_573])).

tff(c_3291,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_3224,c_14])).

tff(c_3327,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_491,c_3291])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.32  % Computer   : n022.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % DateTime   : Tue Dec  1 19:07:55 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.16/2.22  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.16/2.24  
% 6.16/2.24  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.16/2.24  %$ v3_pre_topc > v2_tops_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_2 > #skF_4 > #skF_1
% 6.16/2.24  
% 6.16/2.24  %Foreground sorts:
% 6.16/2.24  
% 6.16/2.24  
% 6.16/2.24  %Background operators:
% 6.16/2.24  
% 6.16/2.24  
% 6.16/2.24  %Foreground operators:
% 6.16/2.24  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 6.16/2.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.16/2.24  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.16/2.24  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.16/2.24  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.16/2.24  tff(v2_tops_1, type, v2_tops_1: ($i * $i) > $o).
% 6.16/2.24  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 6.16/2.24  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 6.16/2.24  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.16/2.24  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.16/2.24  tff('#skF_5', type, '#skF_5': $i).
% 6.16/2.24  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 6.16/2.24  tff('#skF_3', type, '#skF_3': $i).
% 6.16/2.24  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 6.16/2.24  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.16/2.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.16/2.24  tff('#skF_4', type, '#skF_4': $i).
% 6.16/2.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.16/2.24  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 6.16/2.24  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.16/2.24  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 6.16/2.24  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 6.16/2.24  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.16/2.24  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 6.16/2.24  
% 6.16/2.26  tff(f_118, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((r1_tarski(C, B) & v3_pre_topc(C, A)) => (C = k1_xboole_0))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_tops_1)).
% 6.16/2.26  tff(f_99, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (k1_tops_1(A, B) = k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t84_tops_1)).
% 6.16/2.26  tff(f_72, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tops_1)).
% 6.16/2.26  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 6.16/2.26  tff(f_52, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 6.16/2.26  tff(f_40, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 6.16/2.26  tff(f_65, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k1_tops_1(A, B), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_tops_1)).
% 6.16/2.26  tff(f_42, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 6.16/2.26  tff(f_46, axiom, (![A, B]: (r1_tarski(A, k4_xboole_0(B, A)) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_xboole_1)).
% 6.16/2.26  tff(f_90, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B, C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(B, k1_tops_1(A, C)) <=> (?[D]: (((m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) & v3_pre_topc(D, A)) & r1_tarski(D, C)) & r2_hidden(B, D)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t54_tops_1)).
% 6.16/2.26  tff(f_57, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 6.16/2.26  tff(c_48, plain, (k1_xboole_0!='#skF_5' | ~v2_tops_1('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_118])).
% 6.16/2.26  tff(c_68, plain, (~v2_tops_1('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_48])).
% 6.16/2.26  tff(c_44, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_118])).
% 6.16/2.26  tff(c_42, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_118])).
% 6.16/2.26  tff(c_415, plain, (![B_101, A_102]: (v2_tops_1(B_101, A_102) | k1_tops_1(A_102, B_101)!=k1_xboole_0 | ~m1_subset_1(B_101, k1_zfmisc_1(u1_struct_0(A_102))) | ~l1_pre_topc(A_102))), inference(cnfTransformation, [status(thm)], [f_99])).
% 6.16/2.26  tff(c_422, plain, (v2_tops_1('#skF_4', '#skF_3') | k1_tops_1('#skF_3', '#skF_4')!=k1_xboole_0 | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_42, c_415])).
% 6.16/2.26  tff(c_426, plain, (v2_tops_1('#skF_4', '#skF_3') | k1_tops_1('#skF_3', '#skF_4')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_44, c_422])).
% 6.16/2.26  tff(c_427, plain, (k1_tops_1('#skF_3', '#skF_4')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_68, c_426])).
% 6.16/2.26  tff(c_150, plain, (![A_76, B_77]: (r1_tarski(k1_tops_1(A_76, B_77), B_77) | ~m1_subset_1(B_77, k1_zfmisc_1(u1_struct_0(A_76))) | ~l1_pre_topc(A_76))), inference(cnfTransformation, [status(thm)], [f_72])).
% 6.16/2.26  tff(c_155, plain, (r1_tarski(k1_tops_1('#skF_3', '#skF_4'), '#skF_4') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_42, c_150])).
% 6.16/2.26  tff(c_159, plain, (r1_tarski(k1_tops_1('#skF_3', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_155])).
% 6.16/2.26  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.16/2.26  tff(c_110, plain, (![A_63, B_64]: (~r2_hidden('#skF_1'(A_63, B_64), B_64) | r1_tarski(A_63, B_64))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.16/2.26  tff(c_115, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_110])).
% 6.16/2.26  tff(c_87, plain, (![A_57, B_58]: (r1_tarski(A_57, B_58) | ~m1_subset_1(A_57, k1_zfmisc_1(B_58)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 6.16/2.26  tff(c_95, plain, (r1_tarski('#skF_4', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_42, c_87])).
% 6.16/2.26  tff(c_129, plain, (![A_71, C_72, B_73]: (r1_tarski(A_71, C_72) | ~r1_tarski(B_73, C_72) | ~r1_tarski(A_71, B_73))), inference(cnfTransformation, [status(thm)], [f_40])).
% 6.16/2.26  tff(c_163, plain, (![A_78]: (r1_tarski(A_78, u1_struct_0('#skF_3')) | ~r1_tarski(A_78, '#skF_4'))), inference(resolution, [status(thm)], [c_95, c_129])).
% 6.16/2.26  tff(c_10, plain, (![A_8, C_10, B_9]: (r1_tarski(A_8, C_10) | ~r1_tarski(B_9, C_10) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_40])).
% 6.16/2.26  tff(c_194, plain, (![A_81, A_82]: (r1_tarski(A_81, u1_struct_0('#skF_3')) | ~r1_tarski(A_81, A_82) | ~r1_tarski(A_82, '#skF_4'))), inference(resolution, [status(thm)], [c_163, c_10])).
% 6.16/2.26  tff(c_198, plain, (r1_tarski(k1_tops_1('#skF_3', '#skF_4'), u1_struct_0('#skF_3')) | ~r1_tarski('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_159, c_194])).
% 6.16/2.26  tff(c_208, plain, (r1_tarski(k1_tops_1('#skF_3', '#skF_4'), u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_115, c_198])).
% 6.16/2.26  tff(c_20, plain, (![A_16, B_17]: (m1_subset_1(A_16, k1_zfmisc_1(B_17)) | ~r1_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_52])).
% 6.16/2.26  tff(c_66, plain, (![C_47]: (v2_tops_1('#skF_4', '#skF_3') | k1_xboole_0=C_47 | ~v3_pre_topc(C_47, '#skF_3') | ~r1_tarski(C_47, '#skF_4') | ~m1_subset_1(C_47, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_118])).
% 6.16/2.26  tff(c_181, plain, (![C_80]: (k1_xboole_0=C_80 | ~v3_pre_topc(C_80, '#skF_3') | ~r1_tarski(C_80, '#skF_4') | ~m1_subset_1(C_80, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_68, c_66])).
% 6.16/2.26  tff(c_375, plain, (![A_100]: (k1_xboole_0=A_100 | ~v3_pre_topc(A_100, '#skF_3') | ~r1_tarski(A_100, '#skF_4') | ~r1_tarski(A_100, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_20, c_181])).
% 6.16/2.26  tff(c_386, plain, (k1_tops_1('#skF_3', '#skF_4')=k1_xboole_0 | ~v3_pre_topc(k1_tops_1('#skF_3', '#skF_4'), '#skF_3') | ~r1_tarski(k1_tops_1('#skF_3', '#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_208, c_375])).
% 6.16/2.26  tff(c_405, plain, (k1_tops_1('#skF_3', '#skF_4')=k1_xboole_0 | ~v3_pre_topc(k1_tops_1('#skF_3', '#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_159, c_386])).
% 6.16/2.26  tff(c_429, plain, (~v3_pre_topc(k1_tops_1('#skF_3', '#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_427, c_405])).
% 6.16/2.26  tff(c_46, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_118])).
% 6.16/2.26  tff(c_479, plain, (![A_109, B_110]: (v3_pre_topc(k1_tops_1(A_109, B_110), A_109) | ~m1_subset_1(B_110, k1_zfmisc_1(u1_struct_0(A_109))) | ~l1_pre_topc(A_109) | ~v2_pre_topc(A_109))), inference(cnfTransformation, [status(thm)], [f_65])).
% 6.16/2.26  tff(c_484, plain, (v3_pre_topc(k1_tops_1('#skF_3', '#skF_4'), '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_42, c_479])).
% 6.16/2.26  tff(c_488, plain, (v3_pre_topc(k1_tops_1('#skF_3', '#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_484])).
% 6.16/2.26  tff(c_490, plain, $false, inference(negUnitSimplification, [status(thm)], [c_429, c_488])).
% 6.16/2.26  tff(c_491, plain, (k1_xboole_0!='#skF_5'), inference(splitRight, [status(thm)], [c_48])).
% 6.16/2.26  tff(c_492, plain, (v2_tops_1('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_48])).
% 6.16/2.26  tff(c_50, plain, (v3_pre_topc('#skF_5', '#skF_3') | ~v2_tops_1('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_118])).
% 6.16/2.26  tff(c_494, plain, (v3_pre_topc('#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_492, c_50])).
% 6.16/2.26  tff(c_52, plain, (r1_tarski('#skF_5', '#skF_4') | ~v2_tops_1('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_118])).
% 6.16/2.26  tff(c_497, plain, (r1_tarski('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_492, c_52])).
% 6.16/2.26  tff(c_54, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~v2_tops_1('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_118])).
% 6.16/2.26  tff(c_535, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_492, c_54])).
% 6.16/2.26  tff(c_12, plain, (![A_11]: (r1_tarski(k1_xboole_0, A_11))), inference(cnfTransformation, [status(thm)], [f_42])).
% 6.16/2.26  tff(c_687, plain, (![A_151, B_152]: (r1_tarski(k1_tops_1(A_151, B_152), B_152) | ~m1_subset_1(B_152, k1_zfmisc_1(u1_struct_0(A_151))) | ~l1_pre_topc(A_151))), inference(cnfTransformation, [status(thm)], [f_72])).
% 6.16/2.26  tff(c_856, plain, (![A_160, A_161]: (r1_tarski(k1_tops_1(A_160, A_161), A_161) | ~l1_pre_topc(A_160) | ~r1_tarski(A_161, u1_struct_0(A_160)))), inference(resolution, [status(thm)], [c_20, c_687])).
% 6.16/2.26  tff(c_558, plain, (![A_130, C_131, B_132]: (r1_tarski(A_130, C_131) | ~r1_tarski(B_132, C_131) | ~r1_tarski(A_130, B_132))), inference(cnfTransformation, [status(thm)], [f_40])).
% 6.16/2.26  tff(c_573, plain, (![A_130, A_11]: (r1_tarski(A_130, A_11) | ~r1_tarski(A_130, k1_xboole_0))), inference(resolution, [status(thm)], [c_12, c_558])).
% 6.16/2.26  tff(c_879, plain, (![A_160, A_11]: (r1_tarski(k1_tops_1(A_160, k1_xboole_0), A_11) | ~l1_pre_topc(A_160) | ~r1_tarski(k1_xboole_0, u1_struct_0(A_160)))), inference(resolution, [status(thm)], [c_856, c_573])).
% 6.16/2.26  tff(c_903, plain, (![A_162, A_163]: (r1_tarski(k1_tops_1(A_162, k1_xboole_0), A_163) | ~l1_pre_topc(A_162))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_879])).
% 6.16/2.26  tff(c_14, plain, (![A_12, B_13]: (k1_xboole_0=A_12 | ~r1_tarski(A_12, k4_xboole_0(B_13, A_12)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 6.16/2.26  tff(c_952, plain, (![A_164]: (k1_tops_1(A_164, k1_xboole_0)=k1_xboole_0 | ~l1_pre_topc(A_164))), inference(resolution, [status(thm)], [c_903, c_14])).
% 6.16/2.26  tff(c_956, plain, (k1_tops_1('#skF_3', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_44, c_952])).
% 6.16/2.26  tff(c_1224, plain, (![A_189, B_190, C_191]: (r1_tarski('#skF_2'(A_189, B_190, C_191), C_191) | ~r2_hidden(B_190, k1_tops_1(A_189, C_191)) | ~m1_subset_1(C_191, k1_zfmisc_1(u1_struct_0(A_189))) | ~l1_pre_topc(A_189) | ~v2_pre_topc(A_189))), inference(cnfTransformation, [status(thm)], [f_90])).
% 6.16/2.26  tff(c_1226, plain, (![B_190]: (r1_tarski('#skF_2'('#skF_3', B_190, k1_xboole_0), k1_xboole_0) | ~r2_hidden(B_190, k1_xboole_0) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_956, c_1224])).
% 6.16/2.26  tff(c_1236, plain, (![B_190]: (r1_tarski('#skF_2'('#skF_3', B_190, k1_xboole_0), k1_xboole_0) | ~r2_hidden(B_190, k1_xboole_0) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_1226])).
% 6.16/2.26  tff(c_1309, plain, (~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(splitLeft, [status(thm)], [c_1236])).
% 6.16/2.26  tff(c_1312, plain, (~r1_tarski(k1_xboole_0, u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_20, c_1309])).
% 6.16/2.26  tff(c_1316, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_1312])).
% 6.16/2.26  tff(c_1363, plain, (![B_195]: (r1_tarski('#skF_2'('#skF_3', B_195, k1_xboole_0), k1_xboole_0) | ~r2_hidden(B_195, k1_xboole_0))), inference(splitRight, [status(thm)], [c_1236])).
% 6.16/2.26  tff(c_1378, plain, (![B_195, A_11]: (r1_tarski('#skF_2'('#skF_3', B_195, k1_xboole_0), A_11) | ~r2_hidden(B_195, k1_xboole_0))), inference(resolution, [status(thm)], [c_1363, c_573])).
% 6.16/2.26  tff(c_1318, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(splitRight, [status(thm)], [c_1236])).
% 6.16/2.26  tff(c_1381, plain, (![B_197, A_198, C_199]: (r2_hidden(B_197, '#skF_2'(A_198, B_197, C_199)) | ~r2_hidden(B_197, k1_tops_1(A_198, C_199)) | ~m1_subset_1(C_199, k1_zfmisc_1(u1_struct_0(A_198))) | ~l1_pre_topc(A_198) | ~v2_pre_topc(A_198))), inference(cnfTransformation, [status(thm)], [f_90])).
% 6.16/2.26  tff(c_1383, plain, (![B_197]: (r2_hidden(B_197, '#skF_2'('#skF_3', B_197, k1_xboole_0)) | ~r2_hidden(B_197, k1_xboole_0) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_956, c_1381])).
% 6.16/2.26  tff(c_1422, plain, (![B_202]: (r2_hidden(B_202, '#skF_2'('#skF_3', B_202, k1_xboole_0)) | ~r2_hidden(B_202, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_1318, c_1383])).
% 6.16/2.26  tff(c_22, plain, (![B_19, A_18]: (~r1_tarski(B_19, A_18) | ~r2_hidden(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.16/2.26  tff(c_1509, plain, (![B_206]: (~r1_tarski('#skF_2'('#skF_3', B_206, k1_xboole_0), B_206) | ~r2_hidden(B_206, k1_xboole_0))), inference(resolution, [status(thm)], [c_1422, c_22])).
% 6.16/2.26  tff(c_1522, plain, (![A_11]: (~r2_hidden(A_11, k1_xboole_0))), inference(resolution, [status(thm)], [c_1378, c_1509])).
% 6.16/2.26  tff(c_779, plain, (![A_154, B_155]: (k1_tops_1(A_154, B_155)=k1_xboole_0 | ~v2_tops_1(B_155, A_154) | ~m1_subset_1(B_155, k1_zfmisc_1(u1_struct_0(A_154))) | ~l1_pre_topc(A_154))), inference(cnfTransformation, [status(thm)], [f_99])).
% 6.16/2.26  tff(c_789, plain, (k1_tops_1('#skF_3', '#skF_4')=k1_xboole_0 | ~v2_tops_1('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_42, c_779])).
% 6.16/2.26  tff(c_796, plain, (k1_tops_1('#skF_3', '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_44, c_492, c_789])).
% 6.16/2.26  tff(c_1578, plain, (![B_212, A_213, C_214, D_215]: (r2_hidden(B_212, k1_tops_1(A_213, C_214)) | ~r2_hidden(B_212, D_215) | ~r1_tarski(D_215, C_214) | ~v3_pre_topc(D_215, A_213) | ~m1_subset_1(D_215, k1_zfmisc_1(u1_struct_0(A_213))) | ~m1_subset_1(C_214, k1_zfmisc_1(u1_struct_0(A_213))) | ~l1_pre_topc(A_213) | ~v2_pre_topc(A_213))), inference(cnfTransformation, [status(thm)], [f_90])).
% 6.16/2.26  tff(c_3016, plain, (![A_352, B_353, A_354, C_355]: (r2_hidden('#skF_1'(A_352, B_353), k1_tops_1(A_354, C_355)) | ~r1_tarski(A_352, C_355) | ~v3_pre_topc(A_352, A_354) | ~m1_subset_1(A_352, k1_zfmisc_1(u1_struct_0(A_354))) | ~m1_subset_1(C_355, k1_zfmisc_1(u1_struct_0(A_354))) | ~l1_pre_topc(A_354) | ~v2_pre_topc(A_354) | r1_tarski(A_352, B_353))), inference(resolution, [status(thm)], [c_6, c_1578])).
% 6.16/2.26  tff(c_3037, plain, (![A_352, B_353]: (r2_hidden('#skF_1'(A_352, B_353), k1_xboole_0) | ~r1_tarski(A_352, '#skF_4') | ~v3_pre_topc(A_352, '#skF_3') | ~m1_subset_1(A_352, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | r1_tarski(A_352, B_353))), inference(superposition, [status(thm), theory('equality')], [c_796, c_3016])).
% 6.16/2.26  tff(c_3048, plain, (![A_352, B_353]: (r2_hidden('#skF_1'(A_352, B_353), k1_xboole_0) | ~r1_tarski(A_352, '#skF_4') | ~v3_pre_topc(A_352, '#skF_3') | ~m1_subset_1(A_352, k1_zfmisc_1(u1_struct_0('#skF_3'))) | r1_tarski(A_352, B_353))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_3037])).
% 6.16/2.26  tff(c_3076, plain, (![A_358, B_359]: (~r1_tarski(A_358, '#skF_4') | ~v3_pre_topc(A_358, '#skF_3') | ~m1_subset_1(A_358, k1_zfmisc_1(u1_struct_0('#skF_3'))) | r1_tarski(A_358, B_359))), inference(negUnitSimplification, [status(thm)], [c_1522, c_3048])).
% 6.16/2.26  tff(c_3083, plain, (![B_359]: (~r1_tarski('#skF_5', '#skF_4') | ~v3_pre_topc('#skF_5', '#skF_3') | r1_tarski('#skF_5', B_359))), inference(resolution, [status(thm)], [c_535, c_3076])).
% 6.16/2.26  tff(c_3097, plain, (![B_359]: (r1_tarski('#skF_5', B_359))), inference(demodulation, [status(thm), theory('equality')], [c_494, c_497, c_3083])).
% 6.16/2.26  tff(c_689, plain, (r1_tarski(k1_tops_1('#skF_3', '#skF_5'), '#skF_5') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_535, c_687])).
% 6.16/2.26  tff(c_697, plain, (r1_tarski(k1_tops_1('#skF_3', '#skF_5'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_689])).
% 6.16/2.26  tff(c_574, plain, (![C_133, B_134, A_135]: (r2_hidden(C_133, B_134) | ~r2_hidden(C_133, A_135) | ~r1_tarski(A_135, B_134))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.16/2.26  tff(c_663, plain, (![A_145, B_146, B_147]: (r2_hidden('#skF_1'(A_145, B_146), B_147) | ~r1_tarski(A_145, B_147) | r1_tarski(A_145, B_146))), inference(resolution, [status(thm)], [c_6, c_574])).
% 6.16/2.26  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.16/2.26  tff(c_1585, plain, (![A_216, B_217, B_218, B_219]: (r2_hidden('#skF_1'(A_216, B_217), B_218) | ~r1_tarski(B_219, B_218) | ~r1_tarski(A_216, B_219) | r1_tarski(A_216, B_217))), inference(resolution, [status(thm)], [c_663, c_2])).
% 6.16/2.26  tff(c_1680, plain, (![A_235, B_236]: (r2_hidden('#skF_1'(A_235, B_236), '#skF_5') | ~r1_tarski(A_235, k1_tops_1('#skF_3', '#skF_5')) | r1_tarski(A_235, B_236))), inference(resolution, [status(thm)], [c_697, c_1585])).
% 6.16/2.26  tff(c_2728, plain, (![A_333, B_334, B_335]: (r2_hidden('#skF_1'(A_333, B_334), B_335) | ~r1_tarski('#skF_5', B_335) | ~r1_tarski(A_333, k1_tops_1('#skF_3', '#skF_5')) | r1_tarski(A_333, B_334))), inference(resolution, [status(thm)], [c_1680, c_2])).
% 6.16/2.26  tff(c_2751, plain, (![A_333, B_334]: (~r1_tarski('#skF_5', k1_xboole_0) | ~r1_tarski(A_333, k1_tops_1('#skF_3', '#skF_5')) | r1_tarski(A_333, B_334))), inference(resolution, [status(thm)], [c_2728, c_1522])).
% 6.16/2.26  tff(c_2780, plain, (~r1_tarski('#skF_5', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_2751])).
% 6.16/2.26  tff(c_3126, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3097, c_2780])).
% 6.16/2.26  tff(c_3128, plain, (r1_tarski('#skF_5', k1_xboole_0)), inference(splitRight, [status(thm)], [c_2751])).
% 6.16/2.26  tff(c_3224, plain, (![A_364]: (r1_tarski('#skF_5', A_364))), inference(resolution, [status(thm)], [c_3128, c_573])).
% 6.16/2.26  tff(c_3291, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_3224, c_14])).
% 6.16/2.26  tff(c_3327, plain, $false, inference(negUnitSimplification, [status(thm)], [c_491, c_3291])).
% 6.16/2.26  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.16/2.26  
% 6.16/2.26  Inference rules
% 6.16/2.26  ----------------------
% 6.16/2.26  #Ref     : 0
% 6.16/2.26  #Sup     : 706
% 6.16/2.26  #Fact    : 0
% 6.16/2.26  #Define  : 0
% 6.16/2.26  #Split   : 15
% 6.16/2.26  #Chain   : 0
% 6.16/2.26  #Close   : 0
% 6.16/2.26  
% 6.16/2.26  Ordering : KBO
% 6.16/2.26  
% 6.16/2.26  Simplification rules
% 6.16/2.26  ----------------------
% 6.16/2.26  #Subsume      : 229
% 6.16/2.26  #Demod        : 390
% 6.16/2.26  #Tautology    : 167
% 6.16/2.26  #SimpNegUnit  : 19
% 6.16/2.26  #BackRed      : 17
% 6.16/2.26  
% 6.16/2.26  #Partial instantiations: 0
% 6.16/2.26  #Strategies tried      : 1
% 6.16/2.26  
% 6.16/2.26  Timing (in seconds)
% 6.16/2.26  ----------------------
% 6.16/2.27  Preprocessing        : 0.38
% 6.16/2.27  Parsing              : 0.19
% 6.16/2.27  CNF conversion       : 0.03
% 6.16/2.27  Main loop            : 1.12
% 6.16/2.27  Inferencing          : 0.36
% 6.16/2.27  Reduction            : 0.33
% 6.16/2.27  Demodulation         : 0.22
% 6.16/2.27  BG Simplification    : 0.04
% 6.16/2.27  Subsumption          : 0.31
% 6.16/2.27  Abstraction          : 0.04
% 6.16/2.27  MUC search           : 0.00
% 6.16/2.27  Cooper               : 0.00
% 6.16/2.27  Total                : 1.55
% 6.16/2.27  Index Insertion      : 0.00
% 6.16/2.27  Index Deletion       : 0.00
% 6.16/2.27  Index Matching       : 0.00
% 6.16/2.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
