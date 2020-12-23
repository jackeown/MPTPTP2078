%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:09 EST 2020

% Result     : Theorem 3.54s
% Output     : CNFRefutation 3.54s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 245 expanded)
%              Number of leaves         :   39 ( 103 expanded)
%              Depth                    :   15
%              Number of atoms          :  207 ( 653 expanded)
%              Number of equality atoms :   40 (  97 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_tops_1 > v3_pre_topc > v2_tops_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k7_subset_1 > k4_xboole_0 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_153,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( ( v3_pre_topc(B,A)
                & v3_tops_1(B,A) )
             => B = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_tops_1)).

tff(f_27,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_37,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_139,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_tops_1(B,A)
           => v2_tops_1(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_tops_1)).

tff(f_121,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> k1_tops_1(A,B) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_tops_1)).

tff(f_58,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_xboole_0(B)
           => v4_pre_topc(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_pre_topc)).

tff(f_96,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & v2_tops_1(B,A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v1_xboole_0(k1_tops_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc13_tops_1)).

tff(f_79,axiom,(
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

tff(f_88,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_tops_1(B,A)
          <=> v2_tops_1(k2_pre_topc(A,B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tops_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_64,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_112,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_pre_topc(B,A)
           => k2_pre_topc(A,k1_tops_1(A,k2_pre_topc(A,B))) = k2_pre_topc(A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_tops_1)).

tff(f_103,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).

tff(f_130,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> r1_tarski(B,k2_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_tops_1)).

tff(f_31,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(c_44,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_52,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_50,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_2,plain,(
    ! [A_1] : k4_xboole_0(A_1,k1_xboole_0) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_8,plain,(
    ! [A_6] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_98,plain,(
    ! [A_54,B_55,C_56] :
      ( k7_subset_1(A_54,B_55,C_56) = k4_xboole_0(B_55,C_56)
      | ~ m1_subset_1(B_55,k1_zfmisc_1(A_54)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_107,plain,(
    ! [A_6,C_56] : k7_subset_1(A_6,k1_xboole_0,C_56) = k4_xboole_0(k1_xboole_0,C_56) ),
    inference(resolution,[status(thm)],[c_8,c_98])).

tff(c_46,plain,(
    v3_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_127,plain,(
    ! [B_61,A_62] :
      ( v2_tops_1(B_61,A_62)
      | ~ v3_tops_1(B_61,A_62)
      | ~ m1_subset_1(B_61,k1_zfmisc_1(u1_struct_0(A_62)))
      | ~ l1_pre_topc(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_134,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | ~ v3_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_50,c_127])).

tff(c_142,plain,(
    v2_tops_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_46,c_134])).

tff(c_540,plain,(
    ! [A_118,B_119] :
      ( k1_tops_1(A_118,B_119) = k1_xboole_0
      | ~ v2_tops_1(B_119,A_118)
      | ~ m1_subset_1(B_119,k1_zfmisc_1(u1_struct_0(A_118)))
      | ~ l1_pre_topc(A_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_550,plain,
    ( k1_tops_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ v2_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_50,c_540])).

tff(c_559,plain,(
    k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_142,c_550])).

tff(c_54,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_167,plain,(
    ! [B_72,A_73] :
      ( v4_pre_topc(B_72,A_73)
      | ~ v1_xboole_0(B_72)
      | ~ m1_subset_1(B_72,k1_zfmisc_1(u1_struct_0(A_73)))
      | ~ l1_pre_topc(A_73)
      | ~ v2_pre_topc(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_183,plain,(
    ! [A_73] :
      ( v4_pre_topc(k1_xboole_0,A_73)
      | ~ v1_xboole_0(k1_xboole_0)
      | ~ l1_pre_topc(A_73)
      | ~ v2_pre_topc(A_73) ) ),
    inference(resolution,[status(thm)],[c_8,c_167])).

tff(c_185,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_183])).

tff(c_344,plain,(
    ! [A_95,B_96] :
      ( k1_tops_1(A_95,B_96) = k1_xboole_0
      | ~ v2_tops_1(B_96,A_95)
      | ~ m1_subset_1(B_96,k1_zfmisc_1(u1_struct_0(A_95)))
      | ~ l1_pre_topc(A_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_354,plain,
    ( k1_tops_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ v2_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_50,c_344])).

tff(c_363,plain,(
    k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_142,c_354])).

tff(c_228,plain,(
    ! [A_81,B_82] :
      ( v1_xboole_0(k1_tops_1(A_81,B_82))
      | ~ m1_subset_1(B_82,k1_zfmisc_1(u1_struct_0(A_81)))
      | ~ v2_tops_1(B_82,A_81)
      | ~ l1_pre_topc(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_235,plain,
    ( v1_xboole_0(k1_tops_1('#skF_1','#skF_2'))
    | ~ v2_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_50,c_228])).

tff(c_243,plain,(
    v1_xboole_0(k1_tops_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_142,c_235])).

tff(c_365,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_363,c_243])).

tff(c_367,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_185,c_365])).

tff(c_368,plain,(
    ! [A_73] :
      ( v4_pre_topc(k1_xboole_0,A_73)
      | ~ l1_pre_topc(A_73)
      | ~ v2_pre_topc(A_73) ) ),
    inference(splitRight,[status(thm)],[c_183])).

tff(c_492,plain,(
    ! [A_114,B_115] :
      ( k2_pre_topc(A_114,B_115) = B_115
      | ~ v4_pre_topc(B_115,A_114)
      | ~ m1_subset_1(B_115,k1_zfmisc_1(u1_struct_0(A_114)))
      | ~ l1_pre_topc(A_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_514,plain,(
    ! [A_116] :
      ( k2_pre_topc(A_116,k1_xboole_0) = k1_xboole_0
      | ~ v4_pre_topc(k1_xboole_0,A_116)
      | ~ l1_pre_topc(A_116) ) ),
    inference(resolution,[status(thm)],[c_8,c_492])).

tff(c_519,plain,(
    ! [A_117] :
      ( k2_pre_topc(A_117,k1_xboole_0) = k1_xboole_0
      | ~ l1_pre_topc(A_117)
      | ~ v2_pre_topc(A_117) ) ),
    inference(resolution,[status(thm)],[c_368,c_514])).

tff(c_522,plain,
    ( k2_pre_topc('#skF_1',k1_xboole_0) = k1_xboole_0
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_54,c_519])).

tff(c_525,plain,(
    k2_pre_topc('#skF_1',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_522])).

tff(c_635,plain,(
    ! [A_131,B_132] :
      ( v2_tops_1(k2_pre_topc(A_131,B_132),A_131)
      | ~ v3_tops_1(B_132,A_131)
      | ~ m1_subset_1(B_132,k1_zfmisc_1(u1_struct_0(A_131)))
      | ~ l1_pre_topc(A_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_642,plain,
    ( v2_tops_1(k2_pre_topc('#skF_1','#skF_2'),'#skF_1')
    | ~ v3_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_50,c_635])).

tff(c_650,plain,(
    v2_tops_1(k2_pre_topc('#skF_1','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_46,c_642])).

tff(c_67,plain,(
    ! [A_46,B_47] :
      ( r1_tarski(A_46,B_47)
      | ~ m1_subset_1(A_46,k1_zfmisc_1(B_47)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_79,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(resolution,[status(thm)],[c_8,c_67])).

tff(c_18,plain,(
    ! [A_15,B_16] :
      ( m1_subset_1(k2_pre_topc(A_15,B_16),k1_zfmisc_1(u1_struct_0(A_15)))
      | ~ m1_subset_1(B_16,k1_zfmisc_1(u1_struct_0(A_15)))
      | ~ l1_pre_topc(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_948,plain,(
    ! [A_160,B_161] :
      ( k1_tops_1(A_160,k2_pre_topc(A_160,B_161)) = k1_xboole_0
      | ~ v2_tops_1(k2_pre_topc(A_160,B_161),A_160)
      | ~ m1_subset_1(B_161,k1_zfmisc_1(u1_struct_0(A_160)))
      | ~ l1_pre_topc(A_160) ) ),
    inference(resolution,[status(thm)],[c_18,c_540])).

tff(c_958,plain,
    ( k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')) = k1_xboole_0
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_650,c_948])).

tff(c_969,plain,(
    k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_958])).

tff(c_12,plain,(
    ! [A_7,B_8] :
      ( m1_subset_1(A_7,k1_zfmisc_1(B_8))
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_48,plain,(
    v3_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_815,plain,(
    ! [A_150,B_151] :
      ( k2_pre_topc(A_150,k1_tops_1(A_150,k2_pre_topc(A_150,B_151))) = k2_pre_topc(A_150,B_151)
      | ~ v3_pre_topc(B_151,A_150)
      | ~ m1_subset_1(B_151,k1_zfmisc_1(u1_struct_0(A_150)))
      | ~ l1_pre_topc(A_150) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_822,plain,
    ( k2_pre_topc('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2'))) = k2_pre_topc('#skF_1','#skF_2')
    | ~ v3_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_50,c_815])).

tff(c_830,plain,(
    k2_pre_topc('#skF_1',k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2'))) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_48,c_822])).

tff(c_432,plain,(
    ! [A_107,B_108] :
      ( m1_subset_1(k2_pre_topc(A_107,B_108),k1_zfmisc_1(u1_struct_0(A_107)))
      | ~ m1_subset_1(B_108,k1_zfmisc_1(u1_struct_0(A_107)))
      | ~ l1_pre_topc(A_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_10,plain,(
    ! [A_7,B_8] :
      ( r1_tarski(A_7,B_8)
      | ~ m1_subset_1(A_7,k1_zfmisc_1(B_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_458,plain,(
    ! [A_107,B_108] :
      ( r1_tarski(k2_pre_topc(A_107,B_108),u1_struct_0(A_107))
      | ~ m1_subset_1(B_108,k1_zfmisc_1(u1_struct_0(A_107)))
      | ~ l1_pre_topc(A_107) ) ),
    inference(resolution,[status(thm)],[c_432,c_10])).

tff(c_845,plain,
    ( r1_tarski(k2_pre_topc('#skF_1','#skF_2'),u1_struct_0('#skF_1'))
    | ~ m1_subset_1(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_830,c_458])).

tff(c_860,plain,
    ( r1_tarski(k2_pre_topc('#skF_1','#skF_2'),u1_struct_0('#skF_1'))
    | ~ m1_subset_1(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_845])).

tff(c_894,plain,(
    ~ m1_subset_1(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_860])).

tff(c_899,plain,(
    ~ r1_tarski(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')),u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_12,c_894])).

tff(c_973,plain,(
    ~ r1_tarski(k1_xboole_0,u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_969,c_899])).

tff(c_979,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_973])).

tff(c_980,plain,(
    r1_tarski(k2_pre_topc('#skF_1','#skF_2'),u1_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_860])).

tff(c_556,plain,(
    ! [A_118,A_7] :
      ( k1_tops_1(A_118,A_7) = k1_xboole_0
      | ~ v2_tops_1(A_7,A_118)
      | ~ l1_pre_topc(A_118)
      | ~ r1_tarski(A_7,u1_struct_0(A_118)) ) ),
    inference(resolution,[status(thm)],[c_12,c_540])).

tff(c_987,plain,
    ( k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')) = k1_xboole_0
    | ~ v2_tops_1(k2_pre_topc('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_980,c_556])).

tff(c_1010,plain,(
    k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_650,c_987])).

tff(c_1027,plain,(
    k2_pre_topc('#skF_1',k1_xboole_0) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1010,c_830])).

tff(c_1028,plain,(
    k2_pre_topc('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_525,c_1027])).

tff(c_30,plain,(
    ! [A_25,B_27] :
      ( k7_subset_1(u1_struct_0(A_25),k2_pre_topc(A_25,B_27),k1_tops_1(A_25,B_27)) = k2_tops_1(A_25,B_27)
      | ~ m1_subset_1(B_27,k1_zfmisc_1(u1_struct_0(A_25)))
      | ~ l1_pre_topc(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_1060,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),k1_xboole_0,k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1028,c_30])).

tff(c_1079,plain,(
    k2_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_2,c_107,c_559,c_1060])).

tff(c_687,plain,(
    ! [B_136,A_137] :
      ( r1_tarski(B_136,k2_tops_1(A_137,B_136))
      | ~ v2_tops_1(B_136,A_137)
      | ~ m1_subset_1(B_136,k1_zfmisc_1(u1_struct_0(A_137)))
      | ~ l1_pre_topc(A_137) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_694,plain,
    ( r1_tarski('#skF_2',k2_tops_1('#skF_1','#skF_2'))
    | ~ v2_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_50,c_687])).

tff(c_702,plain,(
    r1_tarski('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_142,c_694])).

tff(c_1090,plain,(
    r1_tarski('#skF_2',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1079,c_702])).

tff(c_4,plain,(
    ! [A_2] :
      ( k1_xboole_0 = A_2
      | ~ r1_tarski(A_2,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1108,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_1090,c_4])).

tff(c_1113,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_1108])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:44:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.54/1.57  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.54/1.58  
% 3.54/1.58  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.54/1.58  %$ v4_pre_topc > v3_tops_1 > v3_pre_topc > v2_tops_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k7_subset_1 > k4_xboole_0 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1
% 3.54/1.58  
% 3.54/1.58  %Foreground sorts:
% 3.54/1.58  
% 3.54/1.58  
% 3.54/1.58  %Background operators:
% 3.54/1.58  
% 3.54/1.58  
% 3.54/1.58  %Foreground operators:
% 3.54/1.58  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 3.54/1.58  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.54/1.58  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.54/1.58  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.54/1.58  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 3.54/1.58  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.54/1.58  tff(v2_tops_1, type, v2_tops_1: ($i * $i) > $o).
% 3.54/1.58  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.54/1.58  tff(v3_tops_1, type, v3_tops_1: ($i * $i) > $o).
% 3.54/1.58  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.54/1.58  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 3.54/1.58  tff('#skF_2', type, '#skF_2': $i).
% 3.54/1.58  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 3.54/1.58  tff('#skF_1', type, '#skF_1': $i).
% 3.54/1.58  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.54/1.58  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 3.54/1.58  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.54/1.58  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.54/1.58  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.54/1.58  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.54/1.58  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.54/1.58  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 3.54/1.58  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.54/1.58  
% 3.54/1.60  tff(f_153, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & v3_tops_1(B, A)) => (B = k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t97_tops_1)).
% 3.54/1.60  tff(f_27, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 3.54/1.60  tff(f_37, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 3.54/1.60  tff(f_35, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 3.54/1.60  tff(f_139, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tops_1(B, A) => v2_tops_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_tops_1)).
% 3.54/1.60  tff(f_121, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (k1_tops_1(A, B) = k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t84_tops_1)).
% 3.54/1.60  tff(f_58, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_xboole_0(B) => v4_pre_topc(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_pre_topc)).
% 3.54/1.60  tff(f_96, axiom, (![A, B]: (((l1_pre_topc(A) & v2_tops_1(B, A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v1_xboole_0(k1_tops_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc13_tops_1)).
% 3.54/1.60  tff(f_79, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_pre_topc)).
% 3.54/1.60  tff(f_88, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tops_1(B, A) <=> v2_tops_1(k2_pre_topc(A, B), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_tops_1)).
% 3.54/1.60  tff(f_41, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.54/1.60  tff(f_64, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 3.54/1.60  tff(f_112, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) => (k2_pre_topc(A, k1_tops_1(A, k2_pre_topc(A, B))) = k2_pre_topc(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t59_tops_1)).
% 3.54/1.60  tff(f_103, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l78_tops_1)).
% 3.54/1.60  tff(f_130, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> r1_tarski(B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_tops_1)).
% 3.54/1.60  tff(f_31, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 3.54/1.60  tff(c_44, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_153])).
% 3.54/1.60  tff(c_52, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_153])).
% 3.54/1.60  tff(c_50, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_153])).
% 3.54/1.60  tff(c_2, plain, (![A_1]: (k4_xboole_0(A_1, k1_xboole_0)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.54/1.60  tff(c_8, plain, (![A_6]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.54/1.60  tff(c_98, plain, (![A_54, B_55, C_56]: (k7_subset_1(A_54, B_55, C_56)=k4_xboole_0(B_55, C_56) | ~m1_subset_1(B_55, k1_zfmisc_1(A_54)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.54/1.60  tff(c_107, plain, (![A_6, C_56]: (k7_subset_1(A_6, k1_xboole_0, C_56)=k4_xboole_0(k1_xboole_0, C_56))), inference(resolution, [status(thm)], [c_8, c_98])).
% 3.54/1.60  tff(c_46, plain, (v3_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_153])).
% 3.54/1.60  tff(c_127, plain, (![B_61, A_62]: (v2_tops_1(B_61, A_62) | ~v3_tops_1(B_61, A_62) | ~m1_subset_1(B_61, k1_zfmisc_1(u1_struct_0(A_62))) | ~l1_pre_topc(A_62))), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.54/1.60  tff(c_134, plain, (v2_tops_1('#skF_2', '#skF_1') | ~v3_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_50, c_127])).
% 3.54/1.60  tff(c_142, plain, (v2_tops_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_46, c_134])).
% 3.54/1.60  tff(c_540, plain, (![A_118, B_119]: (k1_tops_1(A_118, B_119)=k1_xboole_0 | ~v2_tops_1(B_119, A_118) | ~m1_subset_1(B_119, k1_zfmisc_1(u1_struct_0(A_118))) | ~l1_pre_topc(A_118))), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.54/1.60  tff(c_550, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0 | ~v2_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_50, c_540])).
% 3.54/1.60  tff(c_559, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_52, c_142, c_550])).
% 3.54/1.60  tff(c_54, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_153])).
% 3.54/1.60  tff(c_167, plain, (![B_72, A_73]: (v4_pre_topc(B_72, A_73) | ~v1_xboole_0(B_72) | ~m1_subset_1(B_72, k1_zfmisc_1(u1_struct_0(A_73))) | ~l1_pre_topc(A_73) | ~v2_pre_topc(A_73))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.54/1.60  tff(c_183, plain, (![A_73]: (v4_pre_topc(k1_xboole_0, A_73) | ~v1_xboole_0(k1_xboole_0) | ~l1_pre_topc(A_73) | ~v2_pre_topc(A_73))), inference(resolution, [status(thm)], [c_8, c_167])).
% 3.54/1.60  tff(c_185, plain, (~v1_xboole_0(k1_xboole_0)), inference(splitLeft, [status(thm)], [c_183])).
% 3.54/1.60  tff(c_344, plain, (![A_95, B_96]: (k1_tops_1(A_95, B_96)=k1_xboole_0 | ~v2_tops_1(B_96, A_95) | ~m1_subset_1(B_96, k1_zfmisc_1(u1_struct_0(A_95))) | ~l1_pre_topc(A_95))), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.54/1.60  tff(c_354, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0 | ~v2_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_50, c_344])).
% 3.54/1.60  tff(c_363, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_52, c_142, c_354])).
% 3.54/1.60  tff(c_228, plain, (![A_81, B_82]: (v1_xboole_0(k1_tops_1(A_81, B_82)) | ~m1_subset_1(B_82, k1_zfmisc_1(u1_struct_0(A_81))) | ~v2_tops_1(B_82, A_81) | ~l1_pre_topc(A_81))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.54/1.60  tff(c_235, plain, (v1_xboole_0(k1_tops_1('#skF_1', '#skF_2')) | ~v2_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_50, c_228])).
% 3.54/1.60  tff(c_243, plain, (v1_xboole_0(k1_tops_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_142, c_235])).
% 3.54/1.60  tff(c_365, plain, (v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_363, c_243])).
% 3.54/1.60  tff(c_367, plain, $false, inference(negUnitSimplification, [status(thm)], [c_185, c_365])).
% 3.54/1.60  tff(c_368, plain, (![A_73]: (v4_pre_topc(k1_xboole_0, A_73) | ~l1_pre_topc(A_73) | ~v2_pre_topc(A_73))), inference(splitRight, [status(thm)], [c_183])).
% 3.54/1.60  tff(c_492, plain, (![A_114, B_115]: (k2_pre_topc(A_114, B_115)=B_115 | ~v4_pre_topc(B_115, A_114) | ~m1_subset_1(B_115, k1_zfmisc_1(u1_struct_0(A_114))) | ~l1_pre_topc(A_114))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.54/1.60  tff(c_514, plain, (![A_116]: (k2_pre_topc(A_116, k1_xboole_0)=k1_xboole_0 | ~v4_pre_topc(k1_xboole_0, A_116) | ~l1_pre_topc(A_116))), inference(resolution, [status(thm)], [c_8, c_492])).
% 3.54/1.60  tff(c_519, plain, (![A_117]: (k2_pre_topc(A_117, k1_xboole_0)=k1_xboole_0 | ~l1_pre_topc(A_117) | ~v2_pre_topc(A_117))), inference(resolution, [status(thm)], [c_368, c_514])).
% 3.54/1.60  tff(c_522, plain, (k2_pre_topc('#skF_1', k1_xboole_0)=k1_xboole_0 | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_54, c_519])).
% 3.54/1.60  tff(c_525, plain, (k2_pre_topc('#skF_1', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_52, c_522])).
% 3.54/1.60  tff(c_635, plain, (![A_131, B_132]: (v2_tops_1(k2_pre_topc(A_131, B_132), A_131) | ~v3_tops_1(B_132, A_131) | ~m1_subset_1(B_132, k1_zfmisc_1(u1_struct_0(A_131))) | ~l1_pre_topc(A_131))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.54/1.60  tff(c_642, plain, (v2_tops_1(k2_pre_topc('#skF_1', '#skF_2'), '#skF_1') | ~v3_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_50, c_635])).
% 3.54/1.60  tff(c_650, plain, (v2_tops_1(k2_pre_topc('#skF_1', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_46, c_642])).
% 3.54/1.60  tff(c_67, plain, (![A_46, B_47]: (r1_tarski(A_46, B_47) | ~m1_subset_1(A_46, k1_zfmisc_1(B_47)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.54/1.60  tff(c_79, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(resolution, [status(thm)], [c_8, c_67])).
% 3.54/1.60  tff(c_18, plain, (![A_15, B_16]: (m1_subset_1(k2_pre_topc(A_15, B_16), k1_zfmisc_1(u1_struct_0(A_15))) | ~m1_subset_1(B_16, k1_zfmisc_1(u1_struct_0(A_15))) | ~l1_pre_topc(A_15))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.54/1.60  tff(c_948, plain, (![A_160, B_161]: (k1_tops_1(A_160, k2_pre_topc(A_160, B_161))=k1_xboole_0 | ~v2_tops_1(k2_pre_topc(A_160, B_161), A_160) | ~m1_subset_1(B_161, k1_zfmisc_1(u1_struct_0(A_160))) | ~l1_pre_topc(A_160))), inference(resolution, [status(thm)], [c_18, c_540])).
% 3.54/1.60  tff(c_958, plain, (k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))=k1_xboole_0 | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_650, c_948])).
% 3.54/1.60  tff(c_969, plain, (k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_958])).
% 3.54/1.60  tff(c_12, plain, (![A_7, B_8]: (m1_subset_1(A_7, k1_zfmisc_1(B_8)) | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.54/1.60  tff(c_48, plain, (v3_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_153])).
% 3.54/1.60  tff(c_815, plain, (![A_150, B_151]: (k2_pre_topc(A_150, k1_tops_1(A_150, k2_pre_topc(A_150, B_151)))=k2_pre_topc(A_150, B_151) | ~v3_pre_topc(B_151, A_150) | ~m1_subset_1(B_151, k1_zfmisc_1(u1_struct_0(A_150))) | ~l1_pre_topc(A_150))), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.54/1.60  tff(c_822, plain, (k2_pre_topc('#skF_1', k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')))=k2_pre_topc('#skF_1', '#skF_2') | ~v3_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_50, c_815])).
% 3.54/1.60  tff(c_830, plain, (k2_pre_topc('#skF_1', k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_48, c_822])).
% 3.54/1.60  tff(c_432, plain, (![A_107, B_108]: (m1_subset_1(k2_pre_topc(A_107, B_108), k1_zfmisc_1(u1_struct_0(A_107))) | ~m1_subset_1(B_108, k1_zfmisc_1(u1_struct_0(A_107))) | ~l1_pre_topc(A_107))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.54/1.60  tff(c_10, plain, (![A_7, B_8]: (r1_tarski(A_7, B_8) | ~m1_subset_1(A_7, k1_zfmisc_1(B_8)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.54/1.60  tff(c_458, plain, (![A_107, B_108]: (r1_tarski(k2_pre_topc(A_107, B_108), u1_struct_0(A_107)) | ~m1_subset_1(B_108, k1_zfmisc_1(u1_struct_0(A_107))) | ~l1_pre_topc(A_107))), inference(resolution, [status(thm)], [c_432, c_10])).
% 3.54/1.60  tff(c_845, plain, (r1_tarski(k2_pre_topc('#skF_1', '#skF_2'), u1_struct_0('#skF_1')) | ~m1_subset_1(k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_830, c_458])).
% 3.54/1.60  tff(c_860, plain, (r1_tarski(k2_pre_topc('#skF_1', '#skF_2'), u1_struct_0('#skF_1')) | ~m1_subset_1(k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_845])).
% 3.54/1.60  tff(c_894, plain, (~m1_subset_1(k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_860])).
% 3.54/1.60  tff(c_899, plain, (~r1_tarski(k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')), u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_12, c_894])).
% 3.54/1.60  tff(c_973, plain, (~r1_tarski(k1_xboole_0, u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_969, c_899])).
% 3.54/1.60  tff(c_979, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_79, c_973])).
% 3.54/1.60  tff(c_980, plain, (r1_tarski(k2_pre_topc('#skF_1', '#skF_2'), u1_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_860])).
% 3.54/1.60  tff(c_556, plain, (![A_118, A_7]: (k1_tops_1(A_118, A_7)=k1_xboole_0 | ~v2_tops_1(A_7, A_118) | ~l1_pre_topc(A_118) | ~r1_tarski(A_7, u1_struct_0(A_118)))), inference(resolution, [status(thm)], [c_12, c_540])).
% 3.54/1.60  tff(c_987, plain, (k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))=k1_xboole_0 | ~v2_tops_1(k2_pre_topc('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_980, c_556])).
% 3.54/1.60  tff(c_1010, plain, (k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_52, c_650, c_987])).
% 3.54/1.60  tff(c_1027, plain, (k2_pre_topc('#skF_1', k1_xboole_0)=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1010, c_830])).
% 3.54/1.60  tff(c_1028, plain, (k2_pre_topc('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_525, c_1027])).
% 3.54/1.60  tff(c_30, plain, (![A_25, B_27]: (k7_subset_1(u1_struct_0(A_25), k2_pre_topc(A_25, B_27), k1_tops_1(A_25, B_27))=k2_tops_1(A_25, B_27) | ~m1_subset_1(B_27, k1_zfmisc_1(u1_struct_0(A_25))) | ~l1_pre_topc(A_25))), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.54/1.60  tff(c_1060, plain, (k7_subset_1(u1_struct_0('#skF_1'), k1_xboole_0, k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1028, c_30])).
% 3.54/1.60  tff(c_1079, plain, (k2_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_2, c_107, c_559, c_1060])).
% 3.54/1.60  tff(c_687, plain, (![B_136, A_137]: (r1_tarski(B_136, k2_tops_1(A_137, B_136)) | ~v2_tops_1(B_136, A_137) | ~m1_subset_1(B_136, k1_zfmisc_1(u1_struct_0(A_137))) | ~l1_pre_topc(A_137))), inference(cnfTransformation, [status(thm)], [f_130])).
% 3.54/1.60  tff(c_694, plain, (r1_tarski('#skF_2', k2_tops_1('#skF_1', '#skF_2')) | ~v2_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_50, c_687])).
% 3.54/1.60  tff(c_702, plain, (r1_tarski('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_142, c_694])).
% 3.54/1.60  tff(c_1090, plain, (r1_tarski('#skF_2', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1079, c_702])).
% 3.54/1.60  tff(c_4, plain, (![A_2]: (k1_xboole_0=A_2 | ~r1_tarski(A_2, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.54/1.60  tff(c_1108, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_1090, c_4])).
% 3.54/1.60  tff(c_1113, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_1108])).
% 3.54/1.60  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.54/1.60  
% 3.54/1.60  Inference rules
% 3.54/1.60  ----------------------
% 3.54/1.60  #Ref     : 0
% 3.54/1.60  #Sup     : 221
% 3.54/1.60  #Fact    : 0
% 3.54/1.60  #Define  : 0
% 3.54/1.60  #Split   : 7
% 3.54/1.60  #Chain   : 0
% 3.54/1.60  #Close   : 0
% 3.54/1.60  
% 3.54/1.60  Ordering : KBO
% 3.54/1.60  
% 3.54/1.60  Simplification rules
% 3.54/1.60  ----------------------
% 3.54/1.60  #Subsume      : 30
% 3.54/1.61  #Demod        : 222
% 3.54/1.61  #Tautology    : 77
% 3.54/1.61  #SimpNegUnit  : 4
% 3.54/1.61  #BackRed      : 14
% 3.54/1.61  
% 3.54/1.61  #Partial instantiations: 0
% 3.54/1.61  #Strategies tried      : 1
% 3.54/1.61  
% 3.54/1.61  Timing (in seconds)
% 3.54/1.61  ----------------------
% 3.54/1.61  Preprocessing        : 0.33
% 3.54/1.61  Parsing              : 0.17
% 3.54/1.61  CNF conversion       : 0.02
% 3.54/1.61  Main loop            : 0.44
% 3.54/1.61  Inferencing          : 0.17
% 3.54/1.61  Reduction            : 0.14
% 3.54/1.61  Demodulation         : 0.10
% 3.54/1.61  BG Simplification    : 0.02
% 3.54/1.61  Subsumption          : 0.07
% 3.54/1.61  Abstraction          : 0.02
% 3.54/1.61  MUC search           : 0.00
% 3.54/1.61  Cooper               : 0.00
% 3.54/1.61  Total                : 0.81
% 3.54/1.61  Index Insertion      : 0.00
% 3.54/1.61  Index Deletion       : 0.00
% 3.54/1.61  Index Matching       : 0.00
% 3.54/1.61  BG Taut test         : 0.00
%------------------------------------------------------------------------------
