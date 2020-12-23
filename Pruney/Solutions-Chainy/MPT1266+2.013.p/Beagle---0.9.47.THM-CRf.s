%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:44 EST 2020

% Result     : Theorem 10.94s
% Output     : CNFRefutation 11.10s
% Verified   : 
% Statistics : Number of formulae       :  160 (1137 expanded)
%              Number of leaves         :   48 ( 401 expanded)
%              Depth                    :   15
%              Number of atoms          :  270 (2424 expanded)
%              Number of equality atoms :   72 ( 660 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tops_1 > v1_tops_1 > r1_tarski > m1_subset_1 > l1_struct_0 > l1_pre_topc > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_subset_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(v1_tops_1,type,(
    v1_tops_1: ( $i * $i ) > $o )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_125,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v2_tops_1(B,A)
            <=> k1_tops_1(A,B) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_tops_1)).

tff(f_79,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_69,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_57,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_102,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_tops_1(B,A)
          <=> k2_pre_topc(A,B) = k2_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tops_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_111,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> v1_tops_1(k3_subset_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_1)).

tff(f_45,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_47,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_63,axiom,(
    ! [A] : k2_subset_1(A) = k3_subset_1(A,k1_subset_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_subset_1)).

tff(f_93,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k3_subset_1(u1_struct_0(A),k2_pre_topc(A,k3_subset_1(u1_struct_0(A),B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tops_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_115,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => k2_pre_topc(A,k2_struct_0(A)) = k2_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_tops_1)).

tff(f_53,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_86,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(B,k2_pre_topc(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_pre_topc)).

tff(f_29,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(c_66,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_107,plain,(
    k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_60,plain,
    ( k1_tops_1('#skF_1','#skF_2') != k1_xboole_0
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_118,plain,(
    ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_60])).

tff(c_58,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_40,plain,(
    ! [A_47] :
      ( l1_struct_0(A_47)
      | ~ l1_pre_topc(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_97,plain,(
    ! [A_67] :
      ( u1_struct_0(A_67) = k2_struct_0(A_67)
      | ~ l1_struct_0(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_102,plain,(
    ! [A_68] :
      ( u1_struct_0(A_68) = k2_struct_0(A_68)
      | ~ l1_pre_topc(A_68) ) ),
    inference(resolution,[status(thm)],[c_40,c_97])).

tff(c_106,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_58,c_102])).

tff(c_56,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_112,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_56])).

tff(c_28,plain,(
    ! [A_37,B_38] :
      ( m1_subset_1(k3_subset_1(A_37,B_38),k1_zfmisc_1(A_37))
      | ~ m1_subset_1(B_38,k1_zfmisc_1(A_37)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_716,plain,(
    ! [B_116,A_117] :
      ( v1_tops_1(B_116,A_117)
      | k2_pre_topc(A_117,B_116) != k2_struct_0(A_117)
      | ~ m1_subset_1(B_116,k1_zfmisc_1(u1_struct_0(A_117)))
      | ~ l1_pre_topc(A_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_726,plain,(
    ! [B_116] :
      ( v1_tops_1(B_116,'#skF_1')
      | k2_pre_topc('#skF_1',B_116) != k2_struct_0('#skF_1')
      | ~ m1_subset_1(B_116,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_106,c_716])).

tff(c_742,plain,(
    ! [B_119] :
      ( v1_tops_1(B_119,'#skF_1')
      | k2_pre_topc('#skF_1',B_119) != k2_struct_0('#skF_1')
      | ~ m1_subset_1(B_119,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_726])).

tff(c_763,plain,
    ( v1_tops_1('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_112,c_742])).

tff(c_767,plain,(
    k2_pre_topc('#skF_1','#skF_2') != k2_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_763])).

tff(c_856,plain,(
    ! [A_124,B_125] :
      ( k2_pre_topc(A_124,B_125) = k2_struct_0(A_124)
      | ~ v1_tops_1(B_125,A_124)
      | ~ m1_subset_1(B_125,k1_zfmisc_1(u1_struct_0(A_124)))
      | ~ l1_pre_topc(A_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_866,plain,(
    ! [B_125] :
      ( k2_pre_topc('#skF_1',B_125) = k2_struct_0('#skF_1')
      | ~ v1_tops_1(B_125,'#skF_1')
      | ~ m1_subset_1(B_125,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_106,c_856])).

tff(c_909,plain,(
    ! [B_127] :
      ( k2_pre_topc('#skF_1',B_127) = k2_struct_0('#skF_1')
      | ~ v1_tops_1(B_127,'#skF_1')
      | ~ m1_subset_1(B_127,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_866])).

tff(c_922,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = k2_struct_0('#skF_1')
    | ~ v1_tops_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_112,c_909])).

tff(c_934,plain,(
    ~ v1_tops_1('#skF_2','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_767,c_922])).

tff(c_170,plain,(
    ! [A_83,B_84] :
      ( k3_subset_1(A_83,k3_subset_1(A_83,B_84)) = B_84
      | ~ m1_subset_1(B_84,k1_zfmisc_1(A_83)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_175,plain,(
    k3_subset_1(k2_struct_0('#skF_1'),k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_112,c_170])).

tff(c_979,plain,(
    ! [A_130,B_131] :
      ( v1_tops_1(k3_subset_1(u1_struct_0(A_130),B_131),A_130)
      | ~ v2_tops_1(B_131,A_130)
      | ~ m1_subset_1(B_131,k1_zfmisc_1(u1_struct_0(A_130)))
      | ~ l1_pre_topc(A_130) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_990,plain,(
    ! [B_131] :
      ( v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),B_131),'#skF_1')
      | ~ v2_tops_1(B_131,'#skF_1')
      | ~ m1_subset_1(B_131,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_106,c_979])).

tff(c_1032,plain,(
    ! [B_136] :
      ( v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),B_136),'#skF_1')
      | ~ v2_tops_1(B_136,'#skF_1')
      | ~ m1_subset_1(B_136,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_106,c_990])).

tff(c_1042,plain,
    ( v1_tops_1('#skF_2','#skF_1')
    | ~ v2_tops_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_175,c_1032])).

tff(c_1054,plain,
    ( ~ v2_tops_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_934,c_1042])).

tff(c_1089,plain,(
    ~ m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_1054])).

tff(c_1092,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_28,c_1089])).

tff(c_1096,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_1092])).

tff(c_1098,plain,(
    m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_1054])).

tff(c_874,plain,(
    ! [B_125] :
      ( k2_pre_topc('#skF_1',B_125) = k2_struct_0('#skF_1')
      | ~ v1_tops_1(B_125,'#skF_1')
      | ~ m1_subset_1(B_125,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_866])).

tff(c_1123,plain,
    ( k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = k2_struct_0('#skF_1')
    | ~ v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_1098,c_874])).

tff(c_1140,plain,(
    ~ v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_1123])).

tff(c_734,plain,(
    ! [B_116] :
      ( v1_tops_1(B_116,'#skF_1')
      | k2_pre_topc('#skF_1',B_116) != k2_struct_0('#skF_1')
      | ~ m1_subset_1(B_116,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_726])).

tff(c_1126,plain,
    ( v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) != k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_1098,c_734])).

tff(c_1147,plain,(
    k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) != k2_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_1140,c_1126])).

tff(c_20,plain,(
    ! [A_32] : k1_subset_1(A_32) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_22,plain,(
    ! [A_33] : k2_subset_1(A_33) = A_33 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_32,plain,(
    ! [A_41] : k3_subset_1(A_41,k1_subset_1(A_41)) = k2_subset_1(A_41) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_68,plain,(
    ! [A_41] : k3_subset_1(A_41,k1_subset_1(A_41)) = A_41 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_32])).

tff(c_69,plain,(
    ! [A_41] : k3_subset_1(A_41,k1_xboole_0) = A_41 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_68])).

tff(c_44,plain,(
    ! [A_51,B_53] :
      ( k3_subset_1(u1_struct_0(A_51),k2_pre_topc(A_51,k3_subset_1(u1_struct_0(A_51),B_53))) = k1_tops_1(A_51,B_53)
      | ~ m1_subset_1(B_53,k1_zfmisc_1(u1_struct_0(A_51)))
      | ~ l1_pre_topc(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_386,plain,(
    ! [A_105,B_106] :
      ( m1_subset_1(k2_pre_topc(A_105,B_106),k1_zfmisc_1(u1_struct_0(A_105)))
      | ~ m1_subset_1(B_106,k1_zfmisc_1(u1_struct_0(A_105)))
      | ~ l1_pre_topc(A_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_30,plain,(
    ! [A_39,B_40] :
      ( k3_subset_1(A_39,k3_subset_1(A_39,B_40)) = B_40
      | ~ m1_subset_1(B_40,k1_zfmisc_1(A_39)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1606,plain,(
    ! [A_156,B_157] :
      ( k3_subset_1(u1_struct_0(A_156),k3_subset_1(u1_struct_0(A_156),k2_pre_topc(A_156,B_157))) = k2_pre_topc(A_156,B_157)
      | ~ m1_subset_1(B_157,k1_zfmisc_1(u1_struct_0(A_156)))
      | ~ l1_pre_topc(A_156) ) ),
    inference(resolution,[status(thm)],[c_386,c_30])).

tff(c_14287,plain,(
    ! [A_454,B_455] :
      ( k3_subset_1(u1_struct_0(A_454),k1_tops_1(A_454,B_455)) = k2_pre_topc(A_454,k3_subset_1(u1_struct_0(A_454),B_455))
      | ~ m1_subset_1(k3_subset_1(u1_struct_0(A_454),B_455),k1_zfmisc_1(u1_struct_0(A_454)))
      | ~ l1_pre_topc(A_454)
      | ~ m1_subset_1(B_455,k1_zfmisc_1(u1_struct_0(A_454)))
      | ~ l1_pre_topc(A_454) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_1606])).

tff(c_14383,plain,(
    ! [B_455] :
      ( k3_subset_1(u1_struct_0('#skF_1'),k1_tops_1('#skF_1',B_455)) = k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),B_455))
      | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),B_455),k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ m1_subset_1(B_455,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_106,c_14287])).

tff(c_14533,plain,(
    ! [B_459] :
      ( k3_subset_1(k2_struct_0('#skF_1'),k1_tops_1('#skF_1',B_459)) = k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),B_459))
      | ~ m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'),B_459),k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ m1_subset_1(B_459,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_106,c_58,c_106,c_106,c_106,c_14383])).

tff(c_14578,plain,
    ( k3_subset_1(k2_struct_0('#skF_1'),k1_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_1098,c_14533])).

tff(c_14621,plain,(
    k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_69,c_107,c_14578])).

tff(c_14623,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1147,c_14621])).

tff(c_14625,plain,(
    v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_1123])).

tff(c_997,plain,(
    ! [B_132,A_133] :
      ( v2_tops_1(B_132,A_133)
      | ~ v1_tops_1(k3_subset_1(u1_struct_0(A_133),B_132),A_133)
      | ~ m1_subset_1(B_132,k1_zfmisc_1(u1_struct_0(A_133)))
      | ~ l1_pre_topc(A_133) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_1011,plain,(
    ! [B_132] :
      ( v2_tops_1(B_132,'#skF_1')
      | ~ v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),B_132),'#skF_1')
      | ~ m1_subset_1(B_132,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_106,c_997])).

tff(c_1018,plain,(
    ! [B_132] :
      ( v2_tops_1(B_132,'#skF_1')
      | ~ v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),B_132),'#skF_1')
      | ~ m1_subset_1(B_132,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_106,c_1011])).

tff(c_14628,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_14625,c_1018])).

tff(c_14631,plain,(
    v2_tops_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_14628])).

tff(c_14633,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_118,c_14631])).

tff(c_14635,plain,(
    k1_tops_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_14636,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_56])).

tff(c_54,plain,(
    ! [A_60] :
      ( k2_pre_topc(A_60,k2_struct_0(A_60)) = k2_struct_0(A_60)
      | ~ l1_pre_topc(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_26,plain,(
    ! [A_36] : m1_subset_1(k2_subset_1(A_36),k1_zfmisc_1(A_36)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_67,plain,(
    ! [A_36] : m1_subset_1(A_36,k1_zfmisc_1(A_36)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_26])).

tff(c_14770,plain,(
    ! [B_486,A_487] :
      ( r1_tarski(B_486,k2_pre_topc(A_487,B_486))
      | ~ m1_subset_1(B_486,k1_zfmisc_1(u1_struct_0(A_487)))
      | ~ l1_pre_topc(A_487) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_14783,plain,(
    ! [A_488] :
      ( r1_tarski(u1_struct_0(A_488),k2_pre_topc(A_488,u1_struct_0(A_488)))
      | ~ l1_pre_topc(A_488) ) ),
    inference(resolution,[status(thm)],[c_67,c_14770])).

tff(c_14789,plain,
    ( r1_tarski(k2_struct_0('#skF_1'),k2_pre_topc('#skF_1',u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_106,c_14783])).

tff(c_14795,plain,(
    r1_tarski(k2_struct_0('#skF_1'),k2_pre_topc('#skF_1',k2_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_106,c_14789])).

tff(c_14803,plain,
    ( r1_tarski(k2_struct_0('#skF_1'),k2_struct_0('#skF_1'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_14795])).

tff(c_14806,plain,(
    r1_tarski(k2_struct_0('#skF_1'),k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_14803])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( k4_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_14810,plain,(
    k4_xboole_0(k2_struct_0('#skF_1'),k2_struct_0('#skF_1')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14806,c_4])).

tff(c_14735,plain,(
    ! [A_479,B_480] :
      ( k4_xboole_0(A_479,B_480) = k3_subset_1(A_479,B_480)
      | ~ m1_subset_1(B_480,k1_zfmisc_1(A_479)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_14747,plain,(
    ! [A_36] : k4_xboole_0(A_36,A_36) = k3_subset_1(A_36,A_36) ),
    inference(resolution,[status(thm)],[c_67,c_14735])).

tff(c_14823,plain,(
    k3_subset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_1')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_14810,c_14747])).

tff(c_14634,plain,(
    v2_tops_1('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_15254,plain,(
    ! [A_519,B_520] :
      ( v1_tops_1(k3_subset_1(u1_struct_0(A_519),B_520),A_519)
      | ~ v2_tops_1(B_520,A_519)
      | ~ m1_subset_1(B_520,k1_zfmisc_1(u1_struct_0(A_519)))
      | ~ l1_pre_topc(A_519) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_15265,plain,(
    ! [B_520] :
      ( v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),B_520),'#skF_1')
      | ~ v2_tops_1(B_520,'#skF_1')
      | ~ m1_subset_1(B_520,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_106,c_15254])).

tff(c_15271,plain,(
    ! [B_520] :
      ( v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),B_520),'#skF_1')
      | ~ v2_tops_1(B_520,'#skF_1')
      | ~ m1_subset_1(B_520,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_106,c_15265])).

tff(c_15009,plain,(
    ! [B_502,A_503] :
      ( v1_tops_1(B_502,A_503)
      | k2_pre_topc(A_503,B_502) != k2_struct_0(A_503)
      | ~ m1_subset_1(B_502,k1_zfmisc_1(u1_struct_0(A_503)))
      | ~ l1_pre_topc(A_503) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_15019,plain,(
    ! [B_502] :
      ( v1_tops_1(B_502,'#skF_1')
      | k2_pre_topc('#skF_1',B_502) != k2_struct_0('#skF_1')
      | ~ m1_subset_1(B_502,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_106,c_15009])).

tff(c_15045,plain,(
    ! [B_505] :
      ( v1_tops_1(B_505,'#skF_1')
      | k2_pre_topc('#skF_1',B_505) != k2_struct_0('#skF_1')
      | ~ m1_subset_1(B_505,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_15019])).

tff(c_15066,plain,
    ( v1_tops_1('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_14636,c_15045])).

tff(c_15098,plain,(
    k2_pre_topc('#skF_1','#skF_2') != k2_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_15066])).

tff(c_15195,plain,(
    ! [A_515,B_516] :
      ( k2_pre_topc(A_515,B_516) = k2_struct_0(A_515)
      | ~ v1_tops_1(B_516,A_515)
      | ~ m1_subset_1(B_516,k1_zfmisc_1(u1_struct_0(A_515)))
      | ~ l1_pre_topc(A_515) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_15205,plain,(
    ! [B_516] :
      ( k2_pre_topc('#skF_1',B_516) = k2_struct_0('#skF_1')
      | ~ v1_tops_1(B_516,'#skF_1')
      | ~ m1_subset_1(B_516,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_106,c_15195])).

tff(c_15225,plain,(
    ! [B_518] :
      ( k2_pre_topc('#skF_1',B_518) = k2_struct_0('#skF_1')
      | ~ v1_tops_1(B_518,'#skF_1')
      | ~ m1_subset_1(B_518,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_15205])).

tff(c_15238,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = k2_struct_0('#skF_1')
    | ~ v1_tops_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_14636,c_15225])).

tff(c_15250,plain,(
    ~ v1_tops_1('#skF_2','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_15098,c_15238])).

tff(c_14694,plain,(
    ! [A_474,B_475] :
      ( k3_subset_1(A_474,k3_subset_1(A_474,B_475)) = B_475
      | ~ m1_subset_1(B_475,k1_zfmisc_1(A_474)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_14699,plain,(
    k3_subset_1(k2_struct_0('#skF_1'),k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_14636,c_14694])).

tff(c_15277,plain,(
    ! [B_522] :
      ( v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),B_522),'#skF_1')
      | ~ v2_tops_1(B_522,'#skF_1')
      | ~ m1_subset_1(B_522,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_106,c_15265])).

tff(c_15287,plain,
    ( v1_tops_1('#skF_2','#skF_1')
    | ~ v2_tops_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_14699,c_15277])).

tff(c_15299,plain,
    ( ~ v2_tops_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_15250,c_15287])).

tff(c_15304,plain,(
    ~ m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_15299])).

tff(c_15307,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_28,c_15304])).

tff(c_15311,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14636,c_15307])).

tff(c_15313,plain,(
    m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_15299])).

tff(c_15213,plain,(
    ! [B_516] :
      ( k2_pre_topc('#skF_1',B_516) = k2_struct_0('#skF_1')
      | ~ v1_tops_1(B_516,'#skF_1')
      | ~ m1_subset_1(B_516,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_15205])).

tff(c_15329,plain,
    ( k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = k2_struct_0('#skF_1')
    | ~ v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_15313,c_15213])).

tff(c_15409,plain,(
    ~ v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_15329])).

tff(c_15412,plain,
    ( ~ v2_tops_1('#skF_2','#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_15271,c_15409])).

tff(c_15416,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14636,c_14634,c_15412])).

tff(c_15417,plain,(
    k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = k2_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_15329])).

tff(c_15738,plain,(
    ! [A_543,B_544] :
      ( k3_subset_1(u1_struct_0(A_543),k2_pre_topc(A_543,k3_subset_1(u1_struct_0(A_543),B_544))) = k1_tops_1(A_543,B_544)
      | ~ m1_subset_1(B_544,k1_zfmisc_1(u1_struct_0(A_543)))
      | ~ l1_pre_topc(A_543) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_15773,plain,(
    ! [B_544] :
      ( k3_subset_1(k2_struct_0('#skF_1'),k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),B_544))) = k1_tops_1('#skF_1',B_544)
      | ~ m1_subset_1(B_544,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_106,c_15738])).

tff(c_15789,plain,(
    ! [B_545] :
      ( k3_subset_1(k2_struct_0('#skF_1'),k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),B_545))) = k1_tops_1('#skF_1',B_545)
      | ~ m1_subset_1(B_545,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_106,c_106,c_15773])).

tff(c_15828,plain,
    ( k3_subset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_1')) = k1_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_15417,c_15789])).

tff(c_15850,plain,(
    k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14636,c_14823,c_15828])).

tff(c_15852,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14635,c_15850])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n010.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 19:19:29 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.94/4.05  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.94/4.06  
% 10.94/4.06  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.94/4.07  %$ v2_tops_1 > v1_tops_1 > r1_tarski > m1_subset_1 > l1_struct_0 > l1_pre_topc > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_subset_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1
% 10.94/4.07  
% 10.94/4.07  %Foreground sorts:
% 10.94/4.07  
% 10.94/4.07  
% 10.94/4.07  %Background operators:
% 10.94/4.07  
% 10.94/4.07  
% 10.94/4.07  %Foreground operators:
% 10.94/4.07  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.94/4.07  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 10.94/4.07  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 10.94/4.07  tff(v2_tops_1, type, v2_tops_1: ($i * $i) > $o).
% 10.94/4.07  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 10.94/4.07  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 10.94/4.07  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 10.94/4.07  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.94/4.07  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 10.94/4.07  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 10.94/4.07  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 10.94/4.07  tff(v1_tops_1, type, v1_tops_1: ($i * $i) > $o).
% 10.94/4.07  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 10.94/4.07  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 10.94/4.07  tff('#skF_2', type, '#skF_2': $i).
% 10.94/4.07  tff('#skF_1', type, '#skF_1': $i).
% 10.94/4.07  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 10.94/4.07  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 10.94/4.07  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 10.94/4.07  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 10.94/4.07  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.94/4.07  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.94/4.07  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 10.94/4.07  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 10.94/4.07  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 10.94/4.07  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 10.94/4.07  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 10.94/4.07  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 10.94/4.07  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 10.94/4.07  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 10.94/4.07  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 10.94/4.07  
% 11.10/4.09  tff(f_125, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (k1_tops_1(A, B) = k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t84_tops_1)).
% 11.10/4.09  tff(f_79, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 11.10/4.09  tff(f_69, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 11.10/4.09  tff(f_57, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 11.10/4.09  tff(f_102, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) <=> (k2_pre_topc(A, B) = k2_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tops_1)).
% 11.10/4.09  tff(f_61, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 11.10/4.09  tff(f_111, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> v1_tops_1(k3_subset_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tops_1)).
% 11.10/4.09  tff(f_45, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_subset_1)).
% 11.10/4.09  tff(f_47, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 11.10/4.09  tff(f_63, axiom, (![A]: (k2_subset_1(A) = k3_subset_1(A, k1_subset_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_subset_1)).
% 11.10/4.09  tff(f_93, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k3_subset_1(u1_struct_0(A), k2_pre_topc(A, k3_subset_1(u1_struct_0(A), B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tops_1)).
% 11.10/4.09  tff(f_75, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 11.10/4.09  tff(f_115, axiom, (![A]: (l1_pre_topc(A) => (k2_pre_topc(A, k2_struct_0(A)) = k2_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t27_tops_1)).
% 11.10/4.09  tff(f_53, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 11.10/4.09  tff(f_86, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(B, k2_pre_topc(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_pre_topc)).
% 11.10/4.09  tff(f_29, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 11.10/4.09  tff(f_51, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 11.10/4.09  tff(c_66, plain, (v2_tops_1('#skF_2', '#skF_1') | k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_125])).
% 11.10/4.09  tff(c_107, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_66])).
% 11.10/4.09  tff(c_60, plain, (k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0 | ~v2_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_125])).
% 11.10/4.09  tff(c_118, plain, (~v2_tops_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_107, c_60])).
% 11.10/4.09  tff(c_58, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_125])).
% 11.10/4.09  tff(c_40, plain, (![A_47]: (l1_struct_0(A_47) | ~l1_pre_topc(A_47))), inference(cnfTransformation, [status(thm)], [f_79])).
% 11.10/4.09  tff(c_97, plain, (![A_67]: (u1_struct_0(A_67)=k2_struct_0(A_67) | ~l1_struct_0(A_67))), inference(cnfTransformation, [status(thm)], [f_69])).
% 11.10/4.09  tff(c_102, plain, (![A_68]: (u1_struct_0(A_68)=k2_struct_0(A_68) | ~l1_pre_topc(A_68))), inference(resolution, [status(thm)], [c_40, c_97])).
% 11.10/4.09  tff(c_106, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_58, c_102])).
% 11.10/4.09  tff(c_56, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_125])).
% 11.10/4.09  tff(c_112, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_106, c_56])).
% 11.10/4.09  tff(c_28, plain, (![A_37, B_38]: (m1_subset_1(k3_subset_1(A_37, B_38), k1_zfmisc_1(A_37)) | ~m1_subset_1(B_38, k1_zfmisc_1(A_37)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 11.10/4.09  tff(c_716, plain, (![B_116, A_117]: (v1_tops_1(B_116, A_117) | k2_pre_topc(A_117, B_116)!=k2_struct_0(A_117) | ~m1_subset_1(B_116, k1_zfmisc_1(u1_struct_0(A_117))) | ~l1_pre_topc(A_117))), inference(cnfTransformation, [status(thm)], [f_102])).
% 11.10/4.09  tff(c_726, plain, (![B_116]: (v1_tops_1(B_116, '#skF_1') | k2_pre_topc('#skF_1', B_116)!=k2_struct_0('#skF_1') | ~m1_subset_1(B_116, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_106, c_716])).
% 11.10/4.09  tff(c_742, plain, (![B_119]: (v1_tops_1(B_119, '#skF_1') | k2_pre_topc('#skF_1', B_119)!=k2_struct_0('#skF_1') | ~m1_subset_1(B_119, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_726])).
% 11.10/4.09  tff(c_763, plain, (v1_tops_1('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_112, c_742])).
% 11.10/4.09  tff(c_767, plain, (k2_pre_topc('#skF_1', '#skF_2')!=k2_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_763])).
% 11.10/4.09  tff(c_856, plain, (![A_124, B_125]: (k2_pre_topc(A_124, B_125)=k2_struct_0(A_124) | ~v1_tops_1(B_125, A_124) | ~m1_subset_1(B_125, k1_zfmisc_1(u1_struct_0(A_124))) | ~l1_pre_topc(A_124))), inference(cnfTransformation, [status(thm)], [f_102])).
% 11.10/4.09  tff(c_866, plain, (![B_125]: (k2_pre_topc('#skF_1', B_125)=k2_struct_0('#skF_1') | ~v1_tops_1(B_125, '#skF_1') | ~m1_subset_1(B_125, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_106, c_856])).
% 11.10/4.09  tff(c_909, plain, (![B_127]: (k2_pre_topc('#skF_1', B_127)=k2_struct_0('#skF_1') | ~v1_tops_1(B_127, '#skF_1') | ~m1_subset_1(B_127, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_866])).
% 11.10/4.09  tff(c_922, plain, (k2_pre_topc('#skF_1', '#skF_2')=k2_struct_0('#skF_1') | ~v1_tops_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_112, c_909])).
% 11.10/4.09  tff(c_934, plain, (~v1_tops_1('#skF_2', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_767, c_922])).
% 11.10/4.09  tff(c_170, plain, (![A_83, B_84]: (k3_subset_1(A_83, k3_subset_1(A_83, B_84))=B_84 | ~m1_subset_1(B_84, k1_zfmisc_1(A_83)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 11.10/4.09  tff(c_175, plain, (k3_subset_1(k2_struct_0('#skF_1'), k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))='#skF_2'), inference(resolution, [status(thm)], [c_112, c_170])).
% 11.10/4.09  tff(c_979, plain, (![A_130, B_131]: (v1_tops_1(k3_subset_1(u1_struct_0(A_130), B_131), A_130) | ~v2_tops_1(B_131, A_130) | ~m1_subset_1(B_131, k1_zfmisc_1(u1_struct_0(A_130))) | ~l1_pre_topc(A_130))), inference(cnfTransformation, [status(thm)], [f_111])).
% 11.10/4.09  tff(c_990, plain, (![B_131]: (v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), B_131), '#skF_1') | ~v2_tops_1(B_131, '#skF_1') | ~m1_subset_1(B_131, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_106, c_979])).
% 11.10/4.09  tff(c_1032, plain, (![B_136]: (v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), B_136), '#skF_1') | ~v2_tops_1(B_136, '#skF_1') | ~m1_subset_1(B_136, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_106, c_990])).
% 11.10/4.09  tff(c_1042, plain, (v1_tops_1('#skF_2', '#skF_1') | ~v2_tops_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_175, c_1032])).
% 11.10/4.09  tff(c_1054, plain, (~v2_tops_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_934, c_1042])).
% 11.10/4.09  tff(c_1089, plain, (~m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_1054])).
% 11.10/4.09  tff(c_1092, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_28, c_1089])).
% 11.10/4.09  tff(c_1096, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_112, c_1092])).
% 11.10/4.09  tff(c_1098, plain, (m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_1054])).
% 11.10/4.09  tff(c_874, plain, (![B_125]: (k2_pre_topc('#skF_1', B_125)=k2_struct_0('#skF_1') | ~v1_tops_1(B_125, '#skF_1') | ~m1_subset_1(B_125, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_866])).
% 11.10/4.09  tff(c_1123, plain, (k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))=k2_struct_0('#skF_1') | ~v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(resolution, [status(thm)], [c_1098, c_874])).
% 11.10/4.09  tff(c_1140, plain, (~v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(splitLeft, [status(thm)], [c_1123])).
% 11.10/4.09  tff(c_734, plain, (![B_116]: (v1_tops_1(B_116, '#skF_1') | k2_pre_topc('#skF_1', B_116)!=k2_struct_0('#skF_1') | ~m1_subset_1(B_116, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_726])).
% 11.10/4.09  tff(c_1126, plain, (v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))!=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_1098, c_734])).
% 11.10/4.09  tff(c_1147, plain, (k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))!=k2_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_1140, c_1126])).
% 11.10/4.09  tff(c_20, plain, (![A_32]: (k1_subset_1(A_32)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 11.10/4.09  tff(c_22, plain, (![A_33]: (k2_subset_1(A_33)=A_33)), inference(cnfTransformation, [status(thm)], [f_47])).
% 11.10/4.09  tff(c_32, plain, (![A_41]: (k3_subset_1(A_41, k1_subset_1(A_41))=k2_subset_1(A_41))), inference(cnfTransformation, [status(thm)], [f_63])).
% 11.10/4.09  tff(c_68, plain, (![A_41]: (k3_subset_1(A_41, k1_subset_1(A_41))=A_41)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_32])).
% 11.10/4.09  tff(c_69, plain, (![A_41]: (k3_subset_1(A_41, k1_xboole_0)=A_41)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_68])).
% 11.10/4.09  tff(c_44, plain, (![A_51, B_53]: (k3_subset_1(u1_struct_0(A_51), k2_pre_topc(A_51, k3_subset_1(u1_struct_0(A_51), B_53)))=k1_tops_1(A_51, B_53) | ~m1_subset_1(B_53, k1_zfmisc_1(u1_struct_0(A_51))) | ~l1_pre_topc(A_51))), inference(cnfTransformation, [status(thm)], [f_93])).
% 11.10/4.09  tff(c_386, plain, (![A_105, B_106]: (m1_subset_1(k2_pre_topc(A_105, B_106), k1_zfmisc_1(u1_struct_0(A_105))) | ~m1_subset_1(B_106, k1_zfmisc_1(u1_struct_0(A_105))) | ~l1_pre_topc(A_105))), inference(cnfTransformation, [status(thm)], [f_75])).
% 11.10/4.09  tff(c_30, plain, (![A_39, B_40]: (k3_subset_1(A_39, k3_subset_1(A_39, B_40))=B_40 | ~m1_subset_1(B_40, k1_zfmisc_1(A_39)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 11.10/4.09  tff(c_1606, plain, (![A_156, B_157]: (k3_subset_1(u1_struct_0(A_156), k3_subset_1(u1_struct_0(A_156), k2_pre_topc(A_156, B_157)))=k2_pre_topc(A_156, B_157) | ~m1_subset_1(B_157, k1_zfmisc_1(u1_struct_0(A_156))) | ~l1_pre_topc(A_156))), inference(resolution, [status(thm)], [c_386, c_30])).
% 11.10/4.09  tff(c_14287, plain, (![A_454, B_455]: (k3_subset_1(u1_struct_0(A_454), k1_tops_1(A_454, B_455))=k2_pre_topc(A_454, k3_subset_1(u1_struct_0(A_454), B_455)) | ~m1_subset_1(k3_subset_1(u1_struct_0(A_454), B_455), k1_zfmisc_1(u1_struct_0(A_454))) | ~l1_pre_topc(A_454) | ~m1_subset_1(B_455, k1_zfmisc_1(u1_struct_0(A_454))) | ~l1_pre_topc(A_454))), inference(superposition, [status(thm), theory('equality')], [c_44, c_1606])).
% 11.10/4.09  tff(c_14383, plain, (![B_455]: (k3_subset_1(u1_struct_0('#skF_1'), k1_tops_1('#skF_1', B_455))=k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), B_455)) | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), B_455), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~m1_subset_1(B_455, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_106, c_14287])).
% 11.10/4.09  tff(c_14533, plain, (![B_459]: (k3_subset_1(k2_struct_0('#skF_1'), k1_tops_1('#skF_1', B_459))=k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), B_459)) | ~m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'), B_459), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~m1_subset_1(B_459, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_106, c_58, c_106, c_106, c_106, c_14383])).
% 11.10/4.09  tff(c_14578, plain, (k3_subset_1(k2_struct_0('#skF_1'), k1_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2')) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_1098, c_14533])).
% 11.10/4.09  tff(c_14621, plain, (k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_112, c_69, c_107, c_14578])).
% 11.10/4.09  tff(c_14623, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1147, c_14621])).
% 11.10/4.09  tff(c_14625, plain, (v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(splitRight, [status(thm)], [c_1123])).
% 11.10/4.09  tff(c_997, plain, (![B_132, A_133]: (v2_tops_1(B_132, A_133) | ~v1_tops_1(k3_subset_1(u1_struct_0(A_133), B_132), A_133) | ~m1_subset_1(B_132, k1_zfmisc_1(u1_struct_0(A_133))) | ~l1_pre_topc(A_133))), inference(cnfTransformation, [status(thm)], [f_111])).
% 11.10/4.09  tff(c_1011, plain, (![B_132]: (v2_tops_1(B_132, '#skF_1') | ~v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), B_132), '#skF_1') | ~m1_subset_1(B_132, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_106, c_997])).
% 11.10/4.09  tff(c_1018, plain, (![B_132]: (v2_tops_1(B_132, '#skF_1') | ~v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), B_132), '#skF_1') | ~m1_subset_1(B_132, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_106, c_1011])).
% 11.10/4.09  tff(c_14628, plain, (v2_tops_1('#skF_2', '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_14625, c_1018])).
% 11.10/4.09  tff(c_14631, plain, (v2_tops_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_112, c_14628])).
% 11.10/4.09  tff(c_14633, plain, $false, inference(negUnitSimplification, [status(thm)], [c_118, c_14631])).
% 11.10/4.09  tff(c_14635, plain, (k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_66])).
% 11.10/4.09  tff(c_14636, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_106, c_56])).
% 11.10/4.09  tff(c_54, plain, (![A_60]: (k2_pre_topc(A_60, k2_struct_0(A_60))=k2_struct_0(A_60) | ~l1_pre_topc(A_60))), inference(cnfTransformation, [status(thm)], [f_115])).
% 11.10/4.09  tff(c_26, plain, (![A_36]: (m1_subset_1(k2_subset_1(A_36), k1_zfmisc_1(A_36)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 11.10/4.09  tff(c_67, plain, (![A_36]: (m1_subset_1(A_36, k1_zfmisc_1(A_36)))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_26])).
% 11.10/4.09  tff(c_14770, plain, (![B_486, A_487]: (r1_tarski(B_486, k2_pre_topc(A_487, B_486)) | ~m1_subset_1(B_486, k1_zfmisc_1(u1_struct_0(A_487))) | ~l1_pre_topc(A_487))), inference(cnfTransformation, [status(thm)], [f_86])).
% 11.10/4.09  tff(c_14783, plain, (![A_488]: (r1_tarski(u1_struct_0(A_488), k2_pre_topc(A_488, u1_struct_0(A_488))) | ~l1_pre_topc(A_488))), inference(resolution, [status(thm)], [c_67, c_14770])).
% 11.10/4.09  tff(c_14789, plain, (r1_tarski(k2_struct_0('#skF_1'), k2_pre_topc('#skF_1', u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_106, c_14783])).
% 11.10/4.09  tff(c_14795, plain, (r1_tarski(k2_struct_0('#skF_1'), k2_pre_topc('#skF_1', k2_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_106, c_14789])).
% 11.10/4.09  tff(c_14803, plain, (r1_tarski(k2_struct_0('#skF_1'), k2_struct_0('#skF_1')) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_54, c_14795])).
% 11.10/4.09  tff(c_14806, plain, (r1_tarski(k2_struct_0('#skF_1'), k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_14803])).
% 11.10/4.09  tff(c_4, plain, (![A_1, B_2]: (k4_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 11.10/4.09  tff(c_14810, plain, (k4_xboole_0(k2_struct_0('#skF_1'), k2_struct_0('#skF_1'))=k1_xboole_0), inference(resolution, [status(thm)], [c_14806, c_4])).
% 11.10/4.09  tff(c_14735, plain, (![A_479, B_480]: (k4_xboole_0(A_479, B_480)=k3_subset_1(A_479, B_480) | ~m1_subset_1(B_480, k1_zfmisc_1(A_479)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 11.10/4.09  tff(c_14747, plain, (![A_36]: (k4_xboole_0(A_36, A_36)=k3_subset_1(A_36, A_36))), inference(resolution, [status(thm)], [c_67, c_14735])).
% 11.10/4.09  tff(c_14823, plain, (k3_subset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_1'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_14810, c_14747])).
% 11.10/4.09  tff(c_14634, plain, (v2_tops_1('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_66])).
% 11.10/4.09  tff(c_15254, plain, (![A_519, B_520]: (v1_tops_1(k3_subset_1(u1_struct_0(A_519), B_520), A_519) | ~v2_tops_1(B_520, A_519) | ~m1_subset_1(B_520, k1_zfmisc_1(u1_struct_0(A_519))) | ~l1_pre_topc(A_519))), inference(cnfTransformation, [status(thm)], [f_111])).
% 11.10/4.09  tff(c_15265, plain, (![B_520]: (v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), B_520), '#skF_1') | ~v2_tops_1(B_520, '#skF_1') | ~m1_subset_1(B_520, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_106, c_15254])).
% 11.10/4.09  tff(c_15271, plain, (![B_520]: (v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), B_520), '#skF_1') | ~v2_tops_1(B_520, '#skF_1') | ~m1_subset_1(B_520, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_106, c_15265])).
% 11.10/4.09  tff(c_15009, plain, (![B_502, A_503]: (v1_tops_1(B_502, A_503) | k2_pre_topc(A_503, B_502)!=k2_struct_0(A_503) | ~m1_subset_1(B_502, k1_zfmisc_1(u1_struct_0(A_503))) | ~l1_pre_topc(A_503))), inference(cnfTransformation, [status(thm)], [f_102])).
% 11.10/4.09  tff(c_15019, plain, (![B_502]: (v1_tops_1(B_502, '#skF_1') | k2_pre_topc('#skF_1', B_502)!=k2_struct_0('#skF_1') | ~m1_subset_1(B_502, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_106, c_15009])).
% 11.10/4.09  tff(c_15045, plain, (![B_505]: (v1_tops_1(B_505, '#skF_1') | k2_pre_topc('#skF_1', B_505)!=k2_struct_0('#skF_1') | ~m1_subset_1(B_505, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_15019])).
% 11.10/4.09  tff(c_15066, plain, (v1_tops_1('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_14636, c_15045])).
% 11.10/4.09  tff(c_15098, plain, (k2_pre_topc('#skF_1', '#skF_2')!=k2_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_15066])).
% 11.10/4.09  tff(c_15195, plain, (![A_515, B_516]: (k2_pre_topc(A_515, B_516)=k2_struct_0(A_515) | ~v1_tops_1(B_516, A_515) | ~m1_subset_1(B_516, k1_zfmisc_1(u1_struct_0(A_515))) | ~l1_pre_topc(A_515))), inference(cnfTransformation, [status(thm)], [f_102])).
% 11.10/4.09  tff(c_15205, plain, (![B_516]: (k2_pre_topc('#skF_1', B_516)=k2_struct_0('#skF_1') | ~v1_tops_1(B_516, '#skF_1') | ~m1_subset_1(B_516, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_106, c_15195])).
% 11.10/4.09  tff(c_15225, plain, (![B_518]: (k2_pre_topc('#skF_1', B_518)=k2_struct_0('#skF_1') | ~v1_tops_1(B_518, '#skF_1') | ~m1_subset_1(B_518, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_15205])).
% 11.10/4.09  tff(c_15238, plain, (k2_pre_topc('#skF_1', '#skF_2')=k2_struct_0('#skF_1') | ~v1_tops_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_14636, c_15225])).
% 11.10/4.09  tff(c_15250, plain, (~v1_tops_1('#skF_2', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_15098, c_15238])).
% 11.10/4.09  tff(c_14694, plain, (![A_474, B_475]: (k3_subset_1(A_474, k3_subset_1(A_474, B_475))=B_475 | ~m1_subset_1(B_475, k1_zfmisc_1(A_474)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 11.10/4.09  tff(c_14699, plain, (k3_subset_1(k2_struct_0('#skF_1'), k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))='#skF_2'), inference(resolution, [status(thm)], [c_14636, c_14694])).
% 11.10/4.09  tff(c_15277, plain, (![B_522]: (v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), B_522), '#skF_1') | ~v2_tops_1(B_522, '#skF_1') | ~m1_subset_1(B_522, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_106, c_15265])).
% 11.10/4.09  tff(c_15287, plain, (v1_tops_1('#skF_2', '#skF_1') | ~v2_tops_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_14699, c_15277])).
% 11.10/4.09  tff(c_15299, plain, (~v2_tops_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_15250, c_15287])).
% 11.10/4.09  tff(c_15304, plain, (~m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_15299])).
% 11.10/4.09  tff(c_15307, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_28, c_15304])).
% 11.10/4.09  tff(c_15311, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14636, c_15307])).
% 11.10/4.09  tff(c_15313, plain, (m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_15299])).
% 11.10/4.09  tff(c_15213, plain, (![B_516]: (k2_pre_topc('#skF_1', B_516)=k2_struct_0('#skF_1') | ~v1_tops_1(B_516, '#skF_1') | ~m1_subset_1(B_516, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_15205])).
% 11.10/4.09  tff(c_15329, plain, (k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))=k2_struct_0('#skF_1') | ~v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(resolution, [status(thm)], [c_15313, c_15213])).
% 11.10/4.09  tff(c_15409, plain, (~v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(splitLeft, [status(thm)], [c_15329])).
% 11.10/4.09  tff(c_15412, plain, (~v2_tops_1('#skF_2', '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_15271, c_15409])).
% 11.10/4.09  tff(c_15416, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14636, c_14634, c_15412])).
% 11.10/4.09  tff(c_15417, plain, (k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))=k2_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_15329])).
% 11.10/4.09  tff(c_15738, plain, (![A_543, B_544]: (k3_subset_1(u1_struct_0(A_543), k2_pre_topc(A_543, k3_subset_1(u1_struct_0(A_543), B_544)))=k1_tops_1(A_543, B_544) | ~m1_subset_1(B_544, k1_zfmisc_1(u1_struct_0(A_543))) | ~l1_pre_topc(A_543))), inference(cnfTransformation, [status(thm)], [f_93])).
% 11.10/4.09  tff(c_15773, plain, (![B_544]: (k3_subset_1(k2_struct_0('#skF_1'), k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), B_544)))=k1_tops_1('#skF_1', B_544) | ~m1_subset_1(B_544, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_106, c_15738])).
% 11.10/4.09  tff(c_15789, plain, (![B_545]: (k3_subset_1(k2_struct_0('#skF_1'), k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), B_545)))=k1_tops_1('#skF_1', B_545) | ~m1_subset_1(B_545, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_106, c_106, c_15773])).
% 11.10/4.09  tff(c_15828, plain, (k3_subset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_1'))=k1_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_15417, c_15789])).
% 11.10/4.09  tff(c_15850, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_14636, c_14823, c_15828])).
% 11.10/4.09  tff(c_15852, plain, $false, inference(negUnitSimplification, [status(thm)], [c_14635, c_15850])).
% 11.10/4.09  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.10/4.09  
% 11.10/4.09  Inference rules
% 11.10/4.09  ----------------------
% 11.10/4.09  #Ref     : 0
% 11.10/4.09  #Sup     : 3935
% 11.10/4.09  #Fact    : 0
% 11.10/4.09  #Define  : 0
% 11.10/4.09  #Split   : 22
% 11.10/4.09  #Chain   : 0
% 11.10/4.09  #Close   : 0
% 11.10/4.09  
% 11.10/4.09  Ordering : KBO
% 11.10/4.09  
% 11.10/4.09  Simplification rules
% 11.10/4.09  ----------------------
% 11.10/4.09  #Subsume      : 763
% 11.10/4.09  #Demod        : 4952
% 11.10/4.09  #Tautology    : 1233
% 11.10/4.09  #SimpNegUnit  : 141
% 11.10/4.09  #BackRed      : 19
% 11.10/4.09  
% 11.10/4.09  #Partial instantiations: 0
% 11.10/4.09  #Strategies tried      : 1
% 11.10/4.09  
% 11.10/4.09  Timing (in seconds)
% 11.10/4.09  ----------------------
% 11.10/4.09  Preprocessing        : 0.35
% 11.10/4.09  Parsing              : 0.19
% 11.10/4.09  CNF conversion       : 0.02
% 11.10/4.09  Main loop            : 2.97
% 11.10/4.09  Inferencing          : 0.90
% 11.10/4.09  Reduction            : 1.10
% 11.10/4.09  Demodulation         : 0.83
% 11.10/4.09  BG Simplification    : 0.09
% 11.10/4.09  Subsumption          : 0.70
% 11.10/4.09  Abstraction          : 0.10
% 11.10/4.09  MUC search           : 0.00
% 11.10/4.09  Cooper               : 0.00
% 11.10/4.09  Total                : 3.36
% 11.10/4.09  Index Insertion      : 0.00
% 11.10/4.09  Index Deletion       : 0.00
% 11.10/4.09  Index Matching       : 0.00
% 11.10/4.09  BG Taut test         : 0.00
%------------------------------------------------------------------------------
