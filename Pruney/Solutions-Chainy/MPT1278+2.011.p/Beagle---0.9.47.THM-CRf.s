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
% DateTime   : Thu Dec  3 10:22:10 EST 2020

% Result     : Theorem 4.72s
% Output     : CNFRefutation 5.09s
% Verified   : 
% Statistics : Number of formulae       :  164 (3183 expanded)
%              Number of leaves         :   42 (1086 expanded)
%              Depth                    :   20
%              Number of atoms          :  306 (6014 expanded)
%              Number of equality atoms :   88 (2089 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_tops_1 > v3_pre_topc > v2_tops_1 > v1_tops_1 > m1_subset_1 > v2_pre_topc > l1_pre_topc > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

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

tff(v3_tops_1,type,(
    v3_tops_1: ( $i * $i ) > $o )).

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

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_155,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( ( v3_pre_topc(B,A)
                & v3_tops_1(B,A) )
             => B = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_tops_1)).

tff(f_141,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_tops_1(B,A)
           => v2_tops_1(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_tops_1)).

tff(f_123,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> k1_tops_1(A,B) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_tops_1)).

tff(f_96,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => k1_tops_1(A,k1_tops_1(A,B)) = k1_tops_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',projectivity_k1_tops_1)).

tff(f_35,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_41,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_33,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_29,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_90,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k1_tops_1(A,B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_114,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_pre_topc(B,A)
          <=> v4_pre_topc(k3_subset_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_tops_1)).

tff(f_64,axiom,(
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

tff(f_82,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> v1_tops_1(k3_subset_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_1)).

tff(f_73,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_tops_1(B,A)
          <=> k2_pre_topc(A,B) = k2_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tops_1)).

tff(f_132,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_tops_1(B,A)
           => v1_tops_1(k3_subset_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_tops_1)).

tff(c_52,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_60,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_54,plain,(
    v3_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_58,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_482,plain,(
    ! [B_70,A_71] :
      ( v2_tops_1(B_70,A_71)
      | ~ v3_tops_1(B_70,A_71)
      | ~ m1_subset_1(B_70,k1_zfmisc_1(u1_struct_0(A_71)))
      | ~ l1_pre_topc(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_493,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | ~ v3_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_58,c_482])).

tff(c_502,plain,(
    v2_tops_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_54,c_493])).

tff(c_861,plain,(
    ! [A_92,B_93] :
      ( k1_tops_1(A_92,B_93) = k1_xboole_0
      | ~ v2_tops_1(B_93,A_92)
      | ~ m1_subset_1(B_93,k1_zfmisc_1(u1_struct_0(A_92)))
      | ~ l1_pre_topc(A_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_872,plain,
    ( k1_tops_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ v2_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_58,c_861])).

tff(c_881,plain,(
    k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_502,c_872])).

tff(c_1126,plain,(
    ! [A_108,B_109] :
      ( k1_tops_1(A_108,k1_tops_1(A_108,B_109)) = k1_tops_1(A_108,B_109)
      | ~ m1_subset_1(B_109,k1_zfmisc_1(u1_struct_0(A_108)))
      | ~ l1_pre_topc(A_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_1134,plain,
    ( k1_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_58,c_1126])).

tff(c_1142,plain,(
    k1_tops_1('#skF_1',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_881,c_881,c_1134])).

tff(c_10,plain,(
    ! [A_7] : k2_subset_1(A_7) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_14,plain,(
    ! [A_10] : m1_subset_1(k2_subset_1(A_10),k1_zfmisc_1(A_10)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_63,plain,(
    ! [A_10] : m1_subset_1(A_10,k1_zfmisc_1(A_10)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_14])).

tff(c_133,plain,(
    ! [A_50,B_51] : k4_xboole_0(A_50,k4_xboole_0(A_50,B_51)) = k3_xboole_0(A_50,B_51) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    ! [A_6] : k4_xboole_0(k1_xboole_0,A_6) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_163,plain,(
    ! [B_52] : k3_xboole_0(k1_xboole_0,B_52) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_133,c_8])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_168,plain,(
    ! [B_52] : k3_xboole_0(B_52,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_163,c_2])).

tff(c_4,plain,(
    ! [A_3] : k4_xboole_0(A_3,k1_xboole_0) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_159,plain,(
    ! [A_3] : k4_xboole_0(A_3,A_3) = k3_xboole_0(A_3,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_133])).

tff(c_242,plain,(
    ! [A_3] : k4_xboole_0(A_3,A_3) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_168,c_159])).

tff(c_301,plain,(
    ! [A_59,B_60] :
      ( k4_xboole_0(A_59,B_60) = k3_subset_1(A_59,B_60)
      | ~ m1_subset_1(B_60,k1_zfmisc_1(A_59)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_307,plain,(
    ! [A_10] : k4_xboole_0(A_10,A_10) = k3_subset_1(A_10,A_10) ),
    inference(resolution,[status(thm)],[c_63,c_301])).

tff(c_328,plain,(
    ! [A_63] : k3_subset_1(A_63,A_63) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_242,c_307])).

tff(c_16,plain,(
    ! [A_11,B_12] :
      ( m1_subset_1(k3_subset_1(A_11,B_12),k1_zfmisc_1(A_11))
      | ~ m1_subset_1(B_12,k1_zfmisc_1(A_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_333,plain,(
    ! [A_63] :
      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_63))
      | ~ m1_subset_1(A_63,k1_zfmisc_1(A_63)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_328,c_16])).

tff(c_338,plain,(
    ! [A_63] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_63)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_333])).

tff(c_816,plain,(
    ! [B_84,A_85] :
      ( v2_tops_1(B_84,A_85)
      | k1_tops_1(A_85,B_84) != k1_xboole_0
      | ~ m1_subset_1(B_84,k1_zfmisc_1(u1_struct_0(A_85)))
      | ~ l1_pre_topc(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_832,plain,(
    ! [A_85] :
      ( v2_tops_1(k1_xboole_0,A_85)
      | k1_tops_1(A_85,k1_xboole_0) != k1_xboole_0
      | ~ l1_pre_topc(A_85) ) ),
    inference(resolution,[status(thm)],[c_338,c_816])).

tff(c_62,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_840,plain,(
    ! [A_88,B_89] :
      ( v3_pre_topc(k1_tops_1(A_88,B_89),A_88)
      | ~ m1_subset_1(B_89,k1_zfmisc_1(u1_struct_0(A_88)))
      | ~ l1_pre_topc(A_88)
      | ~ v2_pre_topc(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_848,plain,
    ( v3_pre_topc(k1_tops_1('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_58,c_840])).

tff(c_856,plain,(
    v3_pre_topc(k1_tops_1('#skF_1','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_848])).

tff(c_883,plain,(
    v3_pre_topc(k1_xboole_0,'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_881,c_856])).

tff(c_310,plain,(
    ! [A_10] : k3_subset_1(A_10,A_10) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_242,c_307])).

tff(c_186,plain,(
    ! [A_53,B_54] :
      ( k3_subset_1(A_53,k3_subset_1(A_53,B_54)) = B_54
      | ~ m1_subset_1(B_54,k1_zfmisc_1(A_53)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_192,plain,(
    ! [A_10] : k3_subset_1(A_10,k3_subset_1(A_10,A_10)) = A_10 ),
    inference(resolution,[status(thm)],[c_63,c_186])).

tff(c_327,plain,(
    ! [A_10] : k3_subset_1(A_10,k1_xboole_0) = A_10 ),
    inference(demodulation,[status(thm),theory(equality)],[c_310,c_192])).

tff(c_1657,plain,(
    ! [A_135,B_136] :
      ( v4_pre_topc(k3_subset_1(u1_struct_0(A_135),B_136),A_135)
      | ~ v3_pre_topc(B_136,A_135)
      | ~ m1_subset_1(B_136,k1_zfmisc_1(u1_struct_0(A_135)))
      | ~ l1_pre_topc(A_135) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_1665,plain,(
    ! [A_135] :
      ( v4_pre_topc(u1_struct_0(A_135),A_135)
      | ~ v3_pre_topc(k1_xboole_0,A_135)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(A_135)))
      | ~ l1_pre_topc(A_135) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_327,c_1657])).

tff(c_1717,plain,(
    ! [A_140] :
      ( v4_pre_topc(u1_struct_0(A_140),A_140)
      | ~ v3_pre_topc(k1_xboole_0,A_140)
      | ~ l1_pre_topc(A_140) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_338,c_1665])).

tff(c_769,plain,(
    ! [A_80,B_81] :
      ( k2_pre_topc(A_80,B_81) = B_81
      | ~ v4_pre_topc(B_81,A_80)
      | ~ m1_subset_1(B_81,k1_zfmisc_1(u1_struct_0(A_80)))
      | ~ l1_pre_topc(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_790,plain,(
    ! [A_80] :
      ( k2_pre_topc(A_80,u1_struct_0(A_80)) = u1_struct_0(A_80)
      | ~ v4_pre_topc(u1_struct_0(A_80),A_80)
      | ~ l1_pre_topc(A_80) ) ),
    inference(resolution,[status(thm)],[c_63,c_769])).

tff(c_1727,plain,(
    ! [A_141] :
      ( k2_pre_topc(A_141,u1_struct_0(A_141)) = u1_struct_0(A_141)
      | ~ v3_pre_topc(k1_xboole_0,A_141)
      | ~ l1_pre_topc(A_141) ) ),
    inference(resolution,[status(thm)],[c_1717,c_790])).

tff(c_1386,plain,(
    ! [A_116,B_117] :
      ( v1_tops_1(k3_subset_1(u1_struct_0(A_116),B_117),A_116)
      | ~ v2_tops_1(B_117,A_116)
      | ~ m1_subset_1(B_117,k1_zfmisc_1(u1_struct_0(A_116)))
      | ~ l1_pre_topc(A_116) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_1394,plain,(
    ! [A_116] :
      ( v1_tops_1(u1_struct_0(A_116),A_116)
      | ~ v2_tops_1(k1_xboole_0,A_116)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(A_116)))
      | ~ l1_pre_topc(A_116) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_327,c_1386])).

tff(c_1409,plain,(
    ! [A_118] :
      ( v1_tops_1(u1_struct_0(A_118),A_118)
      | ~ v2_tops_1(k1_xboole_0,A_118)
      | ~ l1_pre_topc(A_118) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_338,c_1394])).

tff(c_1048,plain,(
    ! [A_104,B_105] :
      ( k2_pre_topc(A_104,B_105) = k2_struct_0(A_104)
      | ~ v1_tops_1(B_105,A_104)
      | ~ m1_subset_1(B_105,k1_zfmisc_1(u1_struct_0(A_104)))
      | ~ l1_pre_topc(A_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1070,plain,(
    ! [A_104] :
      ( k2_pre_topc(A_104,u1_struct_0(A_104)) = k2_struct_0(A_104)
      | ~ v1_tops_1(u1_struct_0(A_104),A_104)
      | ~ l1_pre_topc(A_104) ) ),
    inference(resolution,[status(thm)],[c_63,c_1048])).

tff(c_1413,plain,(
    ! [A_118] :
      ( k2_pre_topc(A_118,u1_struct_0(A_118)) = k2_struct_0(A_118)
      | ~ v2_tops_1(k1_xboole_0,A_118)
      | ~ l1_pre_topc(A_118) ) ),
    inference(resolution,[status(thm)],[c_1409,c_1070])).

tff(c_1749,plain,(
    ! [A_143] :
      ( u1_struct_0(A_143) = k2_struct_0(A_143)
      | ~ v2_tops_1(k1_xboole_0,A_143)
      | ~ l1_pre_topc(A_143)
      | ~ v3_pre_topc(k1_xboole_0,A_143)
      | ~ l1_pre_topc(A_143) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1727,c_1413])).

tff(c_1752,plain,
    ( u1_struct_0('#skF_1') = k2_struct_0('#skF_1')
    | ~ v2_tops_1(k1_xboole_0,'#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_883,c_1749])).

tff(c_1755,plain,
    ( u1_struct_0('#skF_1') = k2_struct_0('#skF_1')
    | ~ v2_tops_1(k1_xboole_0,'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_1752])).

tff(c_1756,plain,(
    ~ v2_tops_1(k1_xboole_0,'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_1755])).

tff(c_1759,plain,
    ( k1_tops_1('#skF_1',k1_xboole_0) != k1_xboole_0
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_832,c_1756])).

tff(c_1763,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_1142,c_1759])).

tff(c_1764,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_1755])).

tff(c_1818,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1764,c_58])).

tff(c_56,plain,(
    v3_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_42,plain,(
    ! [A_31,B_33] :
      ( v4_pre_topc(k3_subset_1(u1_struct_0(A_31),B_33),A_31)
      | ~ v3_pre_topc(B_33,A_31)
      | ~ m1_subset_1(B_33,k1_zfmisc_1(u1_struct_0(A_31)))
      | ~ l1_pre_topc(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_1837,plain,(
    ! [B_33] :
      ( v4_pre_topc(k3_subset_1(k2_struct_0('#skF_1'),B_33),'#skF_1')
      | ~ v3_pre_topc(B_33,'#skF_1')
      | ~ m1_subset_1(B_33,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1764,c_42])).

tff(c_2916,plain,(
    ! [B_184] :
      ( v4_pre_topc(k3_subset_1(k2_struct_0('#skF_1'),B_184),'#skF_1')
      | ~ v3_pre_topc(B_184,'#skF_1')
      | ~ m1_subset_1(B_184,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_1764,c_1837])).

tff(c_48,plain,(
    ! [A_37,B_39] :
      ( v1_tops_1(k3_subset_1(u1_struct_0(A_37),B_39),A_37)
      | ~ v3_tops_1(B_39,A_37)
      | ~ m1_subset_1(B_39,k1_zfmisc_1(u1_struct_0(A_37)))
      | ~ l1_pre_topc(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_898,plain,(
    ! [B_96,A_97] :
      ( v1_tops_1(B_96,A_97)
      | k2_pre_topc(A_97,B_96) != k2_struct_0(A_97)
      | ~ m1_subset_1(B_96,k1_zfmisc_1(u1_struct_0(A_97)))
      | ~ l1_pre_topc(A_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_909,plain,
    ( v1_tops_1('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != k2_struct_0('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_58,c_898])).

tff(c_918,plain,
    ( v1_tops_1('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_909])).

tff(c_920,plain,(
    k2_pre_topc('#skF_1','#skF_2') != k2_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_918])).

tff(c_1059,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = k2_struct_0('#skF_1')
    | ~ v1_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_58,c_1048])).

tff(c_1068,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = k2_struct_0('#skF_1')
    | ~ v1_tops_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_1059])).

tff(c_1069,plain,(
    ~ v1_tops_1('#skF_2','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_920,c_1068])).

tff(c_191,plain,(
    k3_subset_1(u1_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_58,c_186])).

tff(c_1401,plain,
    ( v1_tops_1('#skF_2','#skF_1')
    | ~ v2_tops_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_191,c_1386])).

tff(c_1407,plain,
    ( v1_tops_1('#skF_2','#skF_1')
    | ~ v2_tops_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_1401])).

tff(c_1408,plain,
    ( ~ v2_tops_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_1069,c_1407])).

tff(c_1420,plain,(
    ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_1408])).

tff(c_1423,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_16,c_1420])).

tff(c_1427,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_1423])).

tff(c_1429,plain,(
    m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_1408])).

tff(c_24,plain,(
    ! [B_20,A_18] :
      ( v1_tops_1(B_20,A_18)
      | k2_pre_topc(A_18,B_20) != k2_struct_0(A_18)
      | ~ m1_subset_1(B_20,k1_zfmisc_1(u1_struct_0(A_18)))
      | ~ l1_pre_topc(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1439,plain,
    ( v1_tops_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) != k2_struct_0('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_1429,c_24])).

tff(c_1469,plain,
    ( v1_tops_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) != k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_1439])).

tff(c_1547,plain,(
    k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) != k2_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_1469])).

tff(c_26,plain,(
    ! [A_18,B_20] :
      ( k2_pre_topc(A_18,B_20) = k2_struct_0(A_18)
      | ~ v1_tops_1(B_20,A_18)
      | ~ m1_subset_1(B_20,k1_zfmisc_1(u1_struct_0(A_18)))
      | ~ l1_pre_topc(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1434,plain,
    ( k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = k2_struct_0('#skF_1')
    | ~ v1_tops_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_1429,c_26])).

tff(c_1464,plain,
    ( k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = k2_struct_0('#skF_1')
    | ~ v1_tops_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_1434])).

tff(c_1576,plain,(
    ~ v1_tops_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_1547,c_1464])).

tff(c_1579,plain,
    ( ~ v3_tops_1('#skF_2','#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_48,c_1576])).

tff(c_1586,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_54,c_1579])).

tff(c_1588,plain,(
    k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = k2_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_1469])).

tff(c_1766,plain,(
    ! [B_144,A_145] :
      ( v4_pre_topc(B_144,A_145)
      | k2_pre_topc(A_145,B_144) != B_144
      | ~ v2_pre_topc(A_145)
      | ~ m1_subset_1(B_144,k1_zfmisc_1(u1_struct_0(A_145)))
      | ~ l1_pre_topc(A_145) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_1769,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) != k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')
    | ~ v2_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_1429,c_1766])).

tff(c_1787,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | k3_subset_1(u1_struct_0('#skF_1'),'#skF_2') != k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_62,c_1588,c_1769])).

tff(c_2482,plain,
    ( v4_pre_topc(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | k3_subset_1(k2_struct_0('#skF_1'),'#skF_2') != k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1764,c_1764,c_1787])).

tff(c_2483,plain,(
    k3_subset_1(k2_struct_0('#skF_1'),'#skF_2') != k2_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_2482])).

tff(c_1804,plain,(
    k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1764,c_1588])).

tff(c_1809,plain,(
    m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1764,c_1764,c_1429])).

tff(c_22,plain,(
    ! [A_15,B_17] :
      ( k2_pre_topc(A_15,B_17) = B_17
      | ~ v4_pre_topc(B_17,A_15)
      | ~ m1_subset_1(B_17,k1_zfmisc_1(u1_struct_0(A_15)))
      | ~ l1_pre_topc(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_1913,plain,(
    ! [B_17] :
      ( k2_pre_topc('#skF_1',B_17) = B_17
      | ~ v4_pre_topc(B_17,'#skF_1')
      | ~ m1_subset_1(B_17,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1764,c_22])).

tff(c_2545,plain,(
    ! [B_168] :
      ( k2_pre_topc('#skF_1',B_168) = B_168
      | ~ v4_pre_topc(B_168,'#skF_1')
      | ~ m1_subset_1(B_168,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_1913])).

tff(c_2548,plain,
    ( k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')
    | ~ v4_pre_topc(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_1809,c_2545])).

tff(c_2565,plain,
    ( k3_subset_1(k2_struct_0('#skF_1'),'#skF_2') = k2_struct_0('#skF_1')
    | ~ v4_pre_topc(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1804,c_2548])).

tff(c_2566,plain,(
    ~ v4_pre_topc(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_2483,c_2565])).

tff(c_2919,plain,
    ( ~ v3_pre_topc('#skF_2','#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_2916,c_2566])).

tff(c_2938,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1818,c_56,c_2919])).

tff(c_2940,plain,(
    k3_subset_1(k2_struct_0('#skF_1'),'#skF_2') = k2_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_2482])).

tff(c_308,plain,(
    k4_xboole_0(u1_struct_0('#skF_1'),'#skF_2') = k3_subset_1(u1_struct_0('#skF_1'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_58,c_301])).

tff(c_6,plain,(
    ! [A_4,B_5] : k4_xboole_0(A_4,k4_xboole_0(A_4,B_5)) = k3_xboole_0(A_4,B_5) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_376,plain,(
    k4_xboole_0(u1_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = k3_xboole_0(u1_struct_0('#skF_1'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_308,c_6])).

tff(c_379,plain,(
    k4_xboole_0(u1_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = k3_xboole_0('#skF_2',u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_376])).

tff(c_311,plain,(
    ! [A_61,B_62] :
      ( m1_subset_1(k3_subset_1(A_61,B_62),k1_zfmisc_1(A_61))
      | ~ m1_subset_1(B_62,k1_zfmisc_1(A_61)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_12,plain,(
    ! [A_8,B_9] :
      ( k4_xboole_0(A_8,B_9) = k3_subset_1(A_8,B_9)
      | ~ m1_subset_1(B_9,k1_zfmisc_1(A_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_993,plain,(
    ! [A_102,B_103] :
      ( k4_xboole_0(A_102,k3_subset_1(A_102,B_103)) = k3_subset_1(A_102,k3_subset_1(A_102,B_103))
      | ~ m1_subset_1(B_103,k1_zfmisc_1(A_102)) ) ),
    inference(resolution,[status(thm)],[c_311,c_12])).

tff(c_999,plain,(
    k4_xboole_0(u1_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = k3_subset_1(u1_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) ),
    inference(resolution,[status(thm)],[c_58,c_993])).

tff(c_1006,plain,(
    k3_xboole_0('#skF_2',u1_struct_0('#skF_1')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_379,c_191,c_999])).

tff(c_1012,plain,(
    k4_xboole_0(u1_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1006,c_379])).

tff(c_1813,plain,(
    k4_xboole_0(k2_struct_0('#skF_1'),k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1764,c_1764,c_1012])).

tff(c_2969,plain,(
    k4_xboole_0(k2_struct_0('#skF_1'),k2_struct_0('#skF_1')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2940,c_1813])).

tff(c_3008,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_2969,c_242])).

tff(c_3019,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_3008])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 10:52:19 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.72/1.93  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.72/1.95  
% 4.72/1.95  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.72/1.95  %$ v4_pre_topc > v3_tops_1 > v3_pre_topc > v2_tops_1 > v1_tops_1 > m1_subset_1 > v2_pre_topc > l1_pre_topc > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1
% 4.72/1.95  
% 4.72/1.95  %Foreground sorts:
% 4.72/1.95  
% 4.72/1.95  
% 4.72/1.95  %Background operators:
% 4.72/1.95  
% 4.72/1.95  
% 4.72/1.95  %Foreground operators:
% 4.72/1.95  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 4.72/1.95  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.72/1.95  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.72/1.95  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.72/1.95  tff(v2_tops_1, type, v2_tops_1: ($i * $i) > $o).
% 4.72/1.95  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.72/1.95  tff(v3_tops_1, type, v3_tops_1: ($i * $i) > $o).
% 4.72/1.95  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 4.72/1.95  tff(v1_tops_1, type, v1_tops_1: ($i * $i) > $o).
% 4.72/1.95  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 4.72/1.95  tff('#skF_2', type, '#skF_2': $i).
% 4.72/1.95  tff('#skF_1', type, '#skF_1': $i).
% 4.72/1.95  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.72/1.95  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 4.72/1.95  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.72/1.95  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.72/1.95  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.72/1.95  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.72/1.95  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.72/1.95  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 4.72/1.95  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 4.72/1.95  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 4.72/1.95  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.72/1.95  
% 5.09/1.97  tff(f_155, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & v3_tops_1(B, A)) => (B = k1_xboole_0)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_tops_1)).
% 5.09/1.97  tff(f_141, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tops_1(B, A) => v2_tops_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_tops_1)).
% 5.09/1.97  tff(f_123, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (k1_tops_1(A, B) = k1_xboole_0)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t84_tops_1)).
% 5.09/1.97  tff(f_96, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (k1_tops_1(A, k1_tops_1(A, B)) = k1_tops_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', projectivity_k1_tops_1)).
% 5.09/1.97  tff(f_35, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 5.09/1.97  tff(f_41, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 5.09/1.97  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 5.09/1.97  tff(f_33, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 5.09/1.97  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 5.09/1.97  tff(f_29, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 5.09/1.97  tff(f_39, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 5.09/1.97  tff(f_45, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 5.09/1.97  tff(f_90, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k1_tops_1(A, B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_tops_1)).
% 5.09/1.97  tff(f_49, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 5.09/1.97  tff(f_114, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> v4_pre_topc(k3_subset_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_tops_1)).
% 5.09/1.97  tff(f_64, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 5.09/1.97  tff(f_82, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> v1_tops_1(k3_subset_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tops_1)).
% 5.09/1.97  tff(f_73, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) <=> (k2_pre_topc(A, B) = k2_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tops_1)).
% 5.09/1.97  tff(f_132, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tops_1(B, A) => v1_tops_1(k3_subset_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_tops_1)).
% 5.09/1.97  tff(c_52, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_155])).
% 5.09/1.97  tff(c_60, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_155])).
% 5.09/1.97  tff(c_54, plain, (v3_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_155])).
% 5.09/1.97  tff(c_58, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_155])).
% 5.09/1.97  tff(c_482, plain, (![B_70, A_71]: (v2_tops_1(B_70, A_71) | ~v3_tops_1(B_70, A_71) | ~m1_subset_1(B_70, k1_zfmisc_1(u1_struct_0(A_71))) | ~l1_pre_topc(A_71))), inference(cnfTransformation, [status(thm)], [f_141])).
% 5.09/1.97  tff(c_493, plain, (v2_tops_1('#skF_2', '#skF_1') | ~v3_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_58, c_482])).
% 5.09/1.97  tff(c_502, plain, (v2_tops_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_54, c_493])).
% 5.09/1.97  tff(c_861, plain, (![A_92, B_93]: (k1_tops_1(A_92, B_93)=k1_xboole_0 | ~v2_tops_1(B_93, A_92) | ~m1_subset_1(B_93, k1_zfmisc_1(u1_struct_0(A_92))) | ~l1_pre_topc(A_92))), inference(cnfTransformation, [status(thm)], [f_123])).
% 5.09/1.97  tff(c_872, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0 | ~v2_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_58, c_861])).
% 5.09/1.97  tff(c_881, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_60, c_502, c_872])).
% 5.09/1.97  tff(c_1126, plain, (![A_108, B_109]: (k1_tops_1(A_108, k1_tops_1(A_108, B_109))=k1_tops_1(A_108, B_109) | ~m1_subset_1(B_109, k1_zfmisc_1(u1_struct_0(A_108))) | ~l1_pre_topc(A_108))), inference(cnfTransformation, [status(thm)], [f_96])).
% 5.09/1.97  tff(c_1134, plain, (k1_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_58, c_1126])).
% 5.09/1.97  tff(c_1142, plain, (k1_tops_1('#skF_1', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_60, c_881, c_881, c_1134])).
% 5.09/1.97  tff(c_10, plain, (![A_7]: (k2_subset_1(A_7)=A_7)), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.09/1.97  tff(c_14, plain, (![A_10]: (m1_subset_1(k2_subset_1(A_10), k1_zfmisc_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.09/1.97  tff(c_63, plain, (![A_10]: (m1_subset_1(A_10, k1_zfmisc_1(A_10)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_14])).
% 5.09/1.97  tff(c_133, plain, (![A_50, B_51]: (k4_xboole_0(A_50, k4_xboole_0(A_50, B_51))=k3_xboole_0(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.09/1.97  tff(c_8, plain, (![A_6]: (k4_xboole_0(k1_xboole_0, A_6)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.09/1.97  tff(c_163, plain, (![B_52]: (k3_xboole_0(k1_xboole_0, B_52)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_133, c_8])).
% 5.09/1.97  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.09/1.97  tff(c_168, plain, (![B_52]: (k3_xboole_0(B_52, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_163, c_2])).
% 5.09/1.97  tff(c_4, plain, (![A_3]: (k4_xboole_0(A_3, k1_xboole_0)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.09/1.97  tff(c_159, plain, (![A_3]: (k4_xboole_0(A_3, A_3)=k3_xboole_0(A_3, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_4, c_133])).
% 5.09/1.97  tff(c_242, plain, (![A_3]: (k4_xboole_0(A_3, A_3)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_168, c_159])).
% 5.09/1.97  tff(c_301, plain, (![A_59, B_60]: (k4_xboole_0(A_59, B_60)=k3_subset_1(A_59, B_60) | ~m1_subset_1(B_60, k1_zfmisc_1(A_59)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.09/1.97  tff(c_307, plain, (![A_10]: (k4_xboole_0(A_10, A_10)=k3_subset_1(A_10, A_10))), inference(resolution, [status(thm)], [c_63, c_301])).
% 5.09/1.97  tff(c_328, plain, (![A_63]: (k3_subset_1(A_63, A_63)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_242, c_307])).
% 5.09/1.97  tff(c_16, plain, (![A_11, B_12]: (m1_subset_1(k3_subset_1(A_11, B_12), k1_zfmisc_1(A_11)) | ~m1_subset_1(B_12, k1_zfmisc_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.09/1.97  tff(c_333, plain, (![A_63]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_63)) | ~m1_subset_1(A_63, k1_zfmisc_1(A_63)))), inference(superposition, [status(thm), theory('equality')], [c_328, c_16])).
% 5.09/1.97  tff(c_338, plain, (![A_63]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_63)))), inference(demodulation, [status(thm), theory('equality')], [c_63, c_333])).
% 5.09/1.97  tff(c_816, plain, (![B_84, A_85]: (v2_tops_1(B_84, A_85) | k1_tops_1(A_85, B_84)!=k1_xboole_0 | ~m1_subset_1(B_84, k1_zfmisc_1(u1_struct_0(A_85))) | ~l1_pre_topc(A_85))), inference(cnfTransformation, [status(thm)], [f_123])).
% 5.09/1.97  tff(c_832, plain, (![A_85]: (v2_tops_1(k1_xboole_0, A_85) | k1_tops_1(A_85, k1_xboole_0)!=k1_xboole_0 | ~l1_pre_topc(A_85))), inference(resolution, [status(thm)], [c_338, c_816])).
% 5.09/1.97  tff(c_62, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_155])).
% 5.09/1.97  tff(c_840, plain, (![A_88, B_89]: (v3_pre_topc(k1_tops_1(A_88, B_89), A_88) | ~m1_subset_1(B_89, k1_zfmisc_1(u1_struct_0(A_88))) | ~l1_pre_topc(A_88) | ~v2_pre_topc(A_88))), inference(cnfTransformation, [status(thm)], [f_90])).
% 5.09/1.97  tff(c_848, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_58, c_840])).
% 5.09/1.97  tff(c_856, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_848])).
% 5.09/1.97  tff(c_883, plain, (v3_pre_topc(k1_xboole_0, '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_881, c_856])).
% 5.09/1.97  tff(c_310, plain, (![A_10]: (k3_subset_1(A_10, A_10)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_242, c_307])).
% 5.09/1.97  tff(c_186, plain, (![A_53, B_54]: (k3_subset_1(A_53, k3_subset_1(A_53, B_54))=B_54 | ~m1_subset_1(B_54, k1_zfmisc_1(A_53)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.09/1.97  tff(c_192, plain, (![A_10]: (k3_subset_1(A_10, k3_subset_1(A_10, A_10))=A_10)), inference(resolution, [status(thm)], [c_63, c_186])).
% 5.09/1.97  tff(c_327, plain, (![A_10]: (k3_subset_1(A_10, k1_xboole_0)=A_10)), inference(demodulation, [status(thm), theory('equality')], [c_310, c_192])).
% 5.09/1.97  tff(c_1657, plain, (![A_135, B_136]: (v4_pre_topc(k3_subset_1(u1_struct_0(A_135), B_136), A_135) | ~v3_pre_topc(B_136, A_135) | ~m1_subset_1(B_136, k1_zfmisc_1(u1_struct_0(A_135))) | ~l1_pre_topc(A_135))), inference(cnfTransformation, [status(thm)], [f_114])).
% 5.09/1.97  tff(c_1665, plain, (![A_135]: (v4_pre_topc(u1_struct_0(A_135), A_135) | ~v3_pre_topc(k1_xboole_0, A_135) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0(A_135))) | ~l1_pre_topc(A_135))), inference(superposition, [status(thm), theory('equality')], [c_327, c_1657])).
% 5.09/1.97  tff(c_1717, plain, (![A_140]: (v4_pre_topc(u1_struct_0(A_140), A_140) | ~v3_pre_topc(k1_xboole_0, A_140) | ~l1_pre_topc(A_140))), inference(demodulation, [status(thm), theory('equality')], [c_338, c_1665])).
% 5.09/1.97  tff(c_769, plain, (![A_80, B_81]: (k2_pre_topc(A_80, B_81)=B_81 | ~v4_pre_topc(B_81, A_80) | ~m1_subset_1(B_81, k1_zfmisc_1(u1_struct_0(A_80))) | ~l1_pre_topc(A_80))), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.09/1.97  tff(c_790, plain, (![A_80]: (k2_pre_topc(A_80, u1_struct_0(A_80))=u1_struct_0(A_80) | ~v4_pre_topc(u1_struct_0(A_80), A_80) | ~l1_pre_topc(A_80))), inference(resolution, [status(thm)], [c_63, c_769])).
% 5.09/1.97  tff(c_1727, plain, (![A_141]: (k2_pre_topc(A_141, u1_struct_0(A_141))=u1_struct_0(A_141) | ~v3_pre_topc(k1_xboole_0, A_141) | ~l1_pre_topc(A_141))), inference(resolution, [status(thm)], [c_1717, c_790])).
% 5.09/1.97  tff(c_1386, plain, (![A_116, B_117]: (v1_tops_1(k3_subset_1(u1_struct_0(A_116), B_117), A_116) | ~v2_tops_1(B_117, A_116) | ~m1_subset_1(B_117, k1_zfmisc_1(u1_struct_0(A_116))) | ~l1_pre_topc(A_116))), inference(cnfTransformation, [status(thm)], [f_82])).
% 5.09/1.97  tff(c_1394, plain, (![A_116]: (v1_tops_1(u1_struct_0(A_116), A_116) | ~v2_tops_1(k1_xboole_0, A_116) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0(A_116))) | ~l1_pre_topc(A_116))), inference(superposition, [status(thm), theory('equality')], [c_327, c_1386])).
% 5.09/1.97  tff(c_1409, plain, (![A_118]: (v1_tops_1(u1_struct_0(A_118), A_118) | ~v2_tops_1(k1_xboole_0, A_118) | ~l1_pre_topc(A_118))), inference(demodulation, [status(thm), theory('equality')], [c_338, c_1394])).
% 5.09/1.97  tff(c_1048, plain, (![A_104, B_105]: (k2_pre_topc(A_104, B_105)=k2_struct_0(A_104) | ~v1_tops_1(B_105, A_104) | ~m1_subset_1(B_105, k1_zfmisc_1(u1_struct_0(A_104))) | ~l1_pre_topc(A_104))), inference(cnfTransformation, [status(thm)], [f_73])).
% 5.09/1.97  tff(c_1070, plain, (![A_104]: (k2_pre_topc(A_104, u1_struct_0(A_104))=k2_struct_0(A_104) | ~v1_tops_1(u1_struct_0(A_104), A_104) | ~l1_pre_topc(A_104))), inference(resolution, [status(thm)], [c_63, c_1048])).
% 5.09/1.97  tff(c_1413, plain, (![A_118]: (k2_pre_topc(A_118, u1_struct_0(A_118))=k2_struct_0(A_118) | ~v2_tops_1(k1_xboole_0, A_118) | ~l1_pre_topc(A_118))), inference(resolution, [status(thm)], [c_1409, c_1070])).
% 5.09/1.97  tff(c_1749, plain, (![A_143]: (u1_struct_0(A_143)=k2_struct_0(A_143) | ~v2_tops_1(k1_xboole_0, A_143) | ~l1_pre_topc(A_143) | ~v3_pre_topc(k1_xboole_0, A_143) | ~l1_pre_topc(A_143))), inference(superposition, [status(thm), theory('equality')], [c_1727, c_1413])).
% 5.09/1.97  tff(c_1752, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1') | ~v2_tops_1(k1_xboole_0, '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_883, c_1749])).
% 5.09/1.97  tff(c_1755, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1') | ~v2_tops_1(k1_xboole_0, '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_1752])).
% 5.09/1.97  tff(c_1756, plain, (~v2_tops_1(k1_xboole_0, '#skF_1')), inference(splitLeft, [status(thm)], [c_1755])).
% 5.09/1.97  tff(c_1759, plain, (k1_tops_1('#skF_1', k1_xboole_0)!=k1_xboole_0 | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_832, c_1756])).
% 5.09/1.97  tff(c_1763, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_1142, c_1759])).
% 5.09/1.97  tff(c_1764, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_1755])).
% 5.09/1.97  tff(c_1818, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_1764, c_58])).
% 5.09/1.97  tff(c_56, plain, (v3_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_155])).
% 5.09/1.97  tff(c_42, plain, (![A_31, B_33]: (v4_pre_topc(k3_subset_1(u1_struct_0(A_31), B_33), A_31) | ~v3_pre_topc(B_33, A_31) | ~m1_subset_1(B_33, k1_zfmisc_1(u1_struct_0(A_31))) | ~l1_pre_topc(A_31))), inference(cnfTransformation, [status(thm)], [f_114])).
% 5.09/1.97  tff(c_1837, plain, (![B_33]: (v4_pre_topc(k3_subset_1(k2_struct_0('#skF_1'), B_33), '#skF_1') | ~v3_pre_topc(B_33, '#skF_1') | ~m1_subset_1(B_33, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_1764, c_42])).
% 5.09/1.97  tff(c_2916, plain, (![B_184]: (v4_pre_topc(k3_subset_1(k2_struct_0('#skF_1'), B_184), '#skF_1') | ~v3_pre_topc(B_184, '#skF_1') | ~m1_subset_1(B_184, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_1764, c_1837])).
% 5.09/1.97  tff(c_48, plain, (![A_37, B_39]: (v1_tops_1(k3_subset_1(u1_struct_0(A_37), B_39), A_37) | ~v3_tops_1(B_39, A_37) | ~m1_subset_1(B_39, k1_zfmisc_1(u1_struct_0(A_37))) | ~l1_pre_topc(A_37))), inference(cnfTransformation, [status(thm)], [f_132])).
% 5.09/1.97  tff(c_898, plain, (![B_96, A_97]: (v1_tops_1(B_96, A_97) | k2_pre_topc(A_97, B_96)!=k2_struct_0(A_97) | ~m1_subset_1(B_96, k1_zfmisc_1(u1_struct_0(A_97))) | ~l1_pre_topc(A_97))), inference(cnfTransformation, [status(thm)], [f_73])).
% 5.09/1.97  tff(c_909, plain, (v1_tops_1('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!=k2_struct_0('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_58, c_898])).
% 5.09/1.97  tff(c_918, plain, (v1_tops_1('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_909])).
% 5.09/1.97  tff(c_920, plain, (k2_pre_topc('#skF_1', '#skF_2')!=k2_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_918])).
% 5.09/1.97  tff(c_1059, plain, (k2_pre_topc('#skF_1', '#skF_2')=k2_struct_0('#skF_1') | ~v1_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_58, c_1048])).
% 5.09/1.97  tff(c_1068, plain, (k2_pre_topc('#skF_1', '#skF_2')=k2_struct_0('#skF_1') | ~v1_tops_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_1059])).
% 5.09/1.97  tff(c_1069, plain, (~v1_tops_1('#skF_2', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_920, c_1068])).
% 5.09/1.97  tff(c_191, plain, (k3_subset_1(u1_struct_0('#skF_1'), k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))='#skF_2'), inference(resolution, [status(thm)], [c_58, c_186])).
% 5.09/1.97  tff(c_1401, plain, (v1_tops_1('#skF_2', '#skF_1') | ~v2_tops_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_191, c_1386])).
% 5.09/1.97  tff(c_1407, plain, (v1_tops_1('#skF_2', '#skF_1') | ~v2_tops_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_1401])).
% 5.09/1.97  tff(c_1408, plain, (~v2_tops_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_1069, c_1407])).
% 5.09/1.97  tff(c_1420, plain, (~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_1408])).
% 5.09/1.97  tff(c_1423, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_16, c_1420])).
% 5.09/1.97  tff(c_1427, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_1423])).
% 5.09/1.97  tff(c_1429, plain, (m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_1408])).
% 5.09/1.97  tff(c_24, plain, (![B_20, A_18]: (v1_tops_1(B_20, A_18) | k2_pre_topc(A_18, B_20)!=k2_struct_0(A_18) | ~m1_subset_1(B_20, k1_zfmisc_1(u1_struct_0(A_18))) | ~l1_pre_topc(A_18))), inference(cnfTransformation, [status(thm)], [f_73])).
% 5.09/1.97  tff(c_1439, plain, (v1_tops_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1') | k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))!=k2_struct_0('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_1429, c_24])).
% 5.09/1.97  tff(c_1469, plain, (v1_tops_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1') | k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))!=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_1439])).
% 5.09/1.97  tff(c_1547, plain, (k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))!=k2_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_1469])).
% 5.09/1.97  tff(c_26, plain, (![A_18, B_20]: (k2_pre_topc(A_18, B_20)=k2_struct_0(A_18) | ~v1_tops_1(B_20, A_18) | ~m1_subset_1(B_20, k1_zfmisc_1(u1_struct_0(A_18))) | ~l1_pre_topc(A_18))), inference(cnfTransformation, [status(thm)], [f_73])).
% 5.09/1.97  tff(c_1434, plain, (k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))=k2_struct_0('#skF_1') | ~v1_tops_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_1429, c_26])).
% 5.09/1.97  tff(c_1464, plain, (k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))=k2_struct_0('#skF_1') | ~v1_tops_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_1434])).
% 5.09/1.97  tff(c_1576, plain, (~v1_tops_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_1547, c_1464])).
% 5.09/1.97  tff(c_1579, plain, (~v3_tops_1('#skF_2', '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_48, c_1576])).
% 5.09/1.97  tff(c_1586, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_54, c_1579])).
% 5.09/1.97  tff(c_1588, plain, (k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))=k2_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_1469])).
% 5.09/1.97  tff(c_1766, plain, (![B_144, A_145]: (v4_pre_topc(B_144, A_145) | k2_pre_topc(A_145, B_144)!=B_144 | ~v2_pre_topc(A_145) | ~m1_subset_1(B_144, k1_zfmisc_1(u1_struct_0(A_145))) | ~l1_pre_topc(A_145))), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.09/1.97  tff(c_1769, plain, (v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1') | k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))!=k3_subset_1(u1_struct_0('#skF_1'), '#skF_2') | ~v2_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_1429, c_1766])).
% 5.09/1.97  tff(c_1787, plain, (v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1') | k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')!=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_62, c_1588, c_1769])).
% 5.09/1.97  tff(c_2482, plain, (v4_pre_topc(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | k3_subset_1(k2_struct_0('#skF_1'), '#skF_2')!=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1764, c_1764, c_1787])).
% 5.09/1.97  tff(c_2483, plain, (k3_subset_1(k2_struct_0('#skF_1'), '#skF_2')!=k2_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_2482])).
% 5.09/1.97  tff(c_1804, plain, (k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1764, c_1588])).
% 5.09/1.97  tff(c_1809, plain, (m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_1764, c_1764, c_1429])).
% 5.09/1.97  tff(c_22, plain, (![A_15, B_17]: (k2_pre_topc(A_15, B_17)=B_17 | ~v4_pre_topc(B_17, A_15) | ~m1_subset_1(B_17, k1_zfmisc_1(u1_struct_0(A_15))) | ~l1_pre_topc(A_15))), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.09/1.97  tff(c_1913, plain, (![B_17]: (k2_pre_topc('#skF_1', B_17)=B_17 | ~v4_pre_topc(B_17, '#skF_1') | ~m1_subset_1(B_17, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_1764, c_22])).
% 5.09/1.97  tff(c_2545, plain, (![B_168]: (k2_pre_topc('#skF_1', B_168)=B_168 | ~v4_pre_topc(B_168, '#skF_1') | ~m1_subset_1(B_168, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_1913])).
% 5.09/1.97  tff(c_2548, plain, (k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))=k3_subset_1(k2_struct_0('#skF_1'), '#skF_2') | ~v4_pre_topc(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(resolution, [status(thm)], [c_1809, c_2545])).
% 5.09/1.97  tff(c_2565, plain, (k3_subset_1(k2_struct_0('#skF_1'), '#skF_2')=k2_struct_0('#skF_1') | ~v4_pre_topc(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1804, c_2548])).
% 5.09/1.97  tff(c_2566, plain, (~v4_pre_topc(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_2483, c_2565])).
% 5.09/1.97  tff(c_2919, plain, (~v3_pre_topc('#skF_2', '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_2916, c_2566])).
% 5.09/1.97  tff(c_2938, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1818, c_56, c_2919])).
% 5.09/1.97  tff(c_2940, plain, (k3_subset_1(k2_struct_0('#skF_1'), '#skF_2')=k2_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_2482])).
% 5.09/1.97  tff(c_308, plain, (k4_xboole_0(u1_struct_0('#skF_1'), '#skF_2')=k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')), inference(resolution, [status(thm)], [c_58, c_301])).
% 5.09/1.97  tff(c_6, plain, (![A_4, B_5]: (k4_xboole_0(A_4, k4_xboole_0(A_4, B_5))=k3_xboole_0(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.09/1.97  tff(c_376, plain, (k4_xboole_0(u1_struct_0('#skF_1'), k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))=k3_xboole_0(u1_struct_0('#skF_1'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_308, c_6])).
% 5.09/1.97  tff(c_379, plain, (k4_xboole_0(u1_struct_0('#skF_1'), k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))=k3_xboole_0('#skF_2', u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_376])).
% 5.09/1.97  tff(c_311, plain, (![A_61, B_62]: (m1_subset_1(k3_subset_1(A_61, B_62), k1_zfmisc_1(A_61)) | ~m1_subset_1(B_62, k1_zfmisc_1(A_61)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.09/1.97  tff(c_12, plain, (![A_8, B_9]: (k4_xboole_0(A_8, B_9)=k3_subset_1(A_8, B_9) | ~m1_subset_1(B_9, k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.09/1.97  tff(c_993, plain, (![A_102, B_103]: (k4_xboole_0(A_102, k3_subset_1(A_102, B_103))=k3_subset_1(A_102, k3_subset_1(A_102, B_103)) | ~m1_subset_1(B_103, k1_zfmisc_1(A_102)))), inference(resolution, [status(thm)], [c_311, c_12])).
% 5.09/1.97  tff(c_999, plain, (k4_xboole_0(u1_struct_0('#skF_1'), k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))=k3_subset_1(u1_struct_0('#skF_1'), k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))), inference(resolution, [status(thm)], [c_58, c_993])).
% 5.09/1.97  tff(c_1006, plain, (k3_xboole_0('#skF_2', u1_struct_0('#skF_1'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_379, c_191, c_999])).
% 5.09/1.97  tff(c_1012, plain, (k4_xboole_0(u1_struct_0('#skF_1'), k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1006, c_379])).
% 5.09/1.97  tff(c_1813, plain, (k4_xboole_0(k2_struct_0('#skF_1'), k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1764, c_1764, c_1012])).
% 5.09/1.97  tff(c_2969, plain, (k4_xboole_0(k2_struct_0('#skF_1'), k2_struct_0('#skF_1'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2940, c_1813])).
% 5.09/1.97  tff(c_3008, plain, (k1_xboole_0='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_2969, c_242])).
% 5.09/1.97  tff(c_3019, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_3008])).
% 5.09/1.97  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.09/1.97  
% 5.09/1.97  Inference rules
% 5.09/1.97  ----------------------
% 5.09/1.97  #Ref     : 0
% 5.09/1.97  #Sup     : 650
% 5.09/1.97  #Fact    : 0
% 5.09/1.97  #Define  : 0
% 5.09/1.97  #Split   : 10
% 5.09/1.97  #Chain   : 0
% 5.09/1.97  #Close   : 0
% 5.09/1.97  
% 5.09/1.97  Ordering : KBO
% 5.09/1.97  
% 5.09/1.97  Simplification rules
% 5.09/1.97  ----------------------
% 5.09/1.97  #Subsume      : 60
% 5.09/1.97  #Demod        : 882
% 5.09/1.97  #Tautology    : 377
% 5.09/1.97  #SimpNegUnit  : 31
% 5.09/1.97  #BackRed      : 38
% 5.09/1.97  
% 5.09/1.97  #Partial instantiations: 0
% 5.09/1.97  #Strategies tried      : 1
% 5.09/1.97  
% 5.09/1.97  Timing (in seconds)
% 5.09/1.97  ----------------------
% 5.09/1.97  Preprocessing        : 0.35
% 5.09/1.97  Parsing              : 0.20
% 5.09/1.97  CNF conversion       : 0.02
% 5.09/1.97  Main loop            : 0.80
% 5.09/1.97  Inferencing          : 0.25
% 5.09/1.97  Reduction            : 0.34
% 5.09/1.97  Demodulation         : 0.27
% 5.09/1.97  BG Simplification    : 0.03
% 5.09/1.98  Subsumption          : 0.12
% 5.09/1.98  Abstraction          : 0.03
% 5.09/1.98  MUC search           : 0.00
% 5.09/1.98  Cooper               : 0.00
% 5.09/1.98  Total                : 1.20
% 5.09/1.98  Index Insertion      : 0.00
% 5.09/1.98  Index Deletion       : 0.00
% 5.09/1.98  Index Matching       : 0.00
% 5.09/1.98  BG Taut test         : 0.00
%------------------------------------------------------------------------------
