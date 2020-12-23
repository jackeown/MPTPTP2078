%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:10 EST 2020

% Result     : Theorem 3.68s
% Output     : CNFRefutation 3.68s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 469 expanded)
%              Number of leaves         :   34 ( 172 expanded)
%              Depth                    :   15
%              Number of atoms          :  137 (1110 expanded)
%              Number of equality atoms :   34 ( 250 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_tops_1 > v3_pre_topc > v1_tops_1 > r1_tarski > m1_subset_1 > v2_pre_topc > l1_struct_0 > l1_pre_topc > k4_xboole_0 > k3_subset_1 > k2_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(v3_tops_1,type,(
    v3_tops_1: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(v1_tops_1,type,(
    v1_tops_1: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

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

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_115,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( ( v3_pre_topc(B,A)
                & v3_tops_1(B,A) )
             => B = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_tops_1)).

tff(f_59,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_55,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_101,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_tops_1(B,A)
           => v1_tops_1(k3_subset_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_tops_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_92,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_pre_topc(B,A)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_tops_1)).

tff(f_74,axiom,(
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

tff(f_83,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_tops_1(B,A)
          <=> k2_pre_topc(A,B) = k2_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tops_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(c_40,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_48,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_24,plain,(
    ! [A_14] :
      ( l1_struct_0(A_14)
      | ~ l1_pre_topc(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_65,plain,(
    ! [A_32] :
      ( u1_struct_0(A_32) = k2_struct_0(A_32)
      | ~ l1_struct_0(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_70,plain,(
    ! [A_33] :
      ( u1_struct_0(A_33) = k2_struct_0(A_33)
      | ~ l1_pre_topc(A_33) ) ),
    inference(resolution,[status(thm)],[c_24,c_65])).

tff(c_74,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_48,c_70])).

tff(c_46,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_75,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_46])).

tff(c_42,plain,(
    v3_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_1181,plain,(
    ! [A_118,B_119] :
      ( v1_tops_1(k3_subset_1(u1_struct_0(A_118),B_119),A_118)
      | ~ v3_tops_1(B_119,A_118)
      | ~ m1_subset_1(B_119,k1_zfmisc_1(u1_struct_0(A_118)))
      | ~ l1_pre_topc(A_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_1192,plain,(
    ! [B_119] :
      ( v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),B_119),'#skF_1')
      | ~ v3_tops_1(B_119,'#skF_1')
      | ~ m1_subset_1(B_119,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_1181])).

tff(c_1198,plain,(
    ! [B_119] :
      ( v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),B_119),'#skF_1')
      | ~ v3_tops_1(B_119,'#skF_1')
      | ~ m1_subset_1(B_119,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_74,c_1192])).

tff(c_18,plain,(
    ! [A_9,B_10] :
      ( m1_subset_1(k3_subset_1(A_9,B_10),k1_zfmisc_1(A_9))
      | ~ m1_subset_1(B_10,k1_zfmisc_1(A_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_44,plain,(
    v3_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_174,plain,(
    ! [A_50,B_51] :
      ( k3_subset_1(A_50,k3_subset_1(A_50,B_51)) = B_51
      | ~ m1_subset_1(B_51,k1_zfmisc_1(A_50)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_185,plain,(
    k3_subset_1(k2_struct_0('#skF_1'),k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_75,c_174])).

tff(c_1401,plain,(
    ! [B_134,A_135] :
      ( v4_pre_topc(B_134,A_135)
      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(A_135),B_134),A_135)
      | ~ m1_subset_1(B_134,k1_zfmisc_1(u1_struct_0(A_135)))
      | ~ l1_pre_topc(A_135) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_1416,plain,(
    ! [B_134] :
      ( v4_pre_topc(B_134,'#skF_1')
      | ~ v3_pre_topc(k3_subset_1(k2_struct_0('#skF_1'),B_134),'#skF_1')
      | ~ m1_subset_1(B_134,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_1401])).

tff(c_1446,plain,(
    ! [B_138] :
      ( v4_pre_topc(B_138,'#skF_1')
      | ~ v3_pre_topc(k3_subset_1(k2_struct_0('#skF_1'),B_138),'#skF_1')
      | ~ m1_subset_1(B_138,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_74,c_1416])).

tff(c_1453,plain,
    ( v4_pre_topc(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ v3_pre_topc('#skF_2','#skF_1')
    | ~ m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_185,c_1446])).

tff(c_1463,plain,
    ( v4_pre_topc(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_1453])).

tff(c_1511,plain,(
    ~ m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_1463])).

tff(c_1540,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_18,c_1511])).

tff(c_1544,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_1540])).

tff(c_1545,plain,(
    v4_pre_topc(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_1463])).

tff(c_1546,plain,(
    m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_1463])).

tff(c_253,plain,(
    ! [A_56,B_57] :
      ( k2_pre_topc(A_56,B_57) = B_57
      | ~ v4_pre_topc(B_57,A_56)
      | ~ m1_subset_1(B_57,k1_zfmisc_1(u1_struct_0(A_56)))
      | ~ l1_pre_topc(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_264,plain,(
    ! [B_57] :
      ( k2_pre_topc('#skF_1',B_57) = B_57
      | ~ v4_pre_topc(B_57,'#skF_1')
      | ~ m1_subset_1(B_57,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_253])).

tff(c_272,plain,(
    ! [B_57] :
      ( k2_pre_topc('#skF_1',B_57) = B_57
      | ~ v4_pre_topc(B_57,'#skF_1')
      | ~ m1_subset_1(B_57,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_264])).

tff(c_1560,plain,
    ( k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')
    | ~ v4_pre_topc(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_1546,c_272])).

tff(c_1574,plain,(
    k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = k3_subset_1(k2_struct_0('#skF_1'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1545,c_1560])).

tff(c_275,plain,(
    ! [A_59,B_60] :
      ( k2_pre_topc(A_59,B_60) = k2_struct_0(A_59)
      | ~ v1_tops_1(B_60,A_59)
      | ~ m1_subset_1(B_60,k1_zfmisc_1(u1_struct_0(A_59)))
      | ~ l1_pre_topc(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_286,plain,(
    ! [B_60] :
      ( k2_pre_topc('#skF_1',B_60) = k2_struct_0('#skF_1')
      | ~ v1_tops_1(B_60,'#skF_1')
      | ~ m1_subset_1(B_60,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_275])).

tff(c_294,plain,(
    ! [B_60] :
      ( k2_pre_topc('#skF_1',B_60) = k2_struct_0('#skF_1')
      | ~ v1_tops_1(B_60,'#skF_1')
      | ~ m1_subset_1(B_60,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_286])).

tff(c_1571,plain,
    ( k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = k2_struct_0('#skF_1')
    | ~ v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_1546,c_294])).

tff(c_1585,plain,
    ( k3_subset_1(k2_struct_0('#skF_1'),'#skF_2') = k2_struct_0('#skF_1')
    | ~ v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1574,c_1571])).

tff(c_1586,plain,(
    ~ v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_1585])).

tff(c_1589,plain,
    ( ~ v3_tops_1('#skF_2','#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_1198,c_1586])).

tff(c_1593,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_42,c_1589])).

tff(c_1594,plain,(
    k3_subset_1(k2_struct_0('#skF_1'),'#skF_2') = k2_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_1585])).

tff(c_120,plain,(
    ! [A_45,B_46] :
      ( k4_xboole_0(A_45,B_46) = k3_subset_1(A_45,B_46)
      | ~ m1_subset_1(B_46,k1_zfmisc_1(A_45)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1385,plain,(
    ! [A_132,B_133] :
      ( k4_xboole_0(A_132,k3_subset_1(A_132,B_133)) = k3_subset_1(A_132,k3_subset_1(A_132,B_133))
      | ~ m1_subset_1(B_133,k1_zfmisc_1(A_132)) ) ),
    inference(resolution,[status(thm)],[c_18,c_120])).

tff(c_1391,plain,(
    k4_xboole_0(k2_struct_0('#skF_1'),k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = k3_subset_1(k2_struct_0('#skF_1'),k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) ),
    inference(resolution,[status(thm)],[c_75,c_1385])).

tff(c_1398,plain,(
    k4_xboole_0(k2_struct_0('#skF_1'),k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_185,c_1391])).

tff(c_1600,plain,(
    k4_xboole_0(k2_struct_0('#skF_1'),k2_struct_0('#skF_1')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1594,c_1398])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_81,plain,(
    ! [A_36,B_37] :
      ( k4_xboole_0(A_36,B_37) = k1_xboole_0
      | ~ r1_tarski(A_36,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_89,plain,(
    ! [B_2] : k4_xboole_0(B_2,B_2) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_81])).

tff(c_1662,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_1600,c_89])).

tff(c_1670,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_1662])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:23:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.68/1.58  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.68/1.59  
% 3.68/1.59  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.68/1.59  %$ v4_pre_topc > v3_tops_1 > v3_pre_topc > v1_tops_1 > r1_tarski > m1_subset_1 > v2_pre_topc > l1_struct_0 > l1_pre_topc > k4_xboole_0 > k3_subset_1 > k2_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1
% 3.68/1.59  
% 3.68/1.59  %Foreground sorts:
% 3.68/1.59  
% 3.68/1.59  
% 3.68/1.59  %Background operators:
% 3.68/1.59  
% 3.68/1.59  
% 3.68/1.59  %Foreground operators:
% 3.68/1.59  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 3.68/1.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.68/1.59  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.68/1.59  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.68/1.59  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.68/1.59  tff(v3_tops_1, type, v3_tops_1: ($i * $i) > $o).
% 3.68/1.59  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.68/1.59  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 3.68/1.59  tff(v1_tops_1, type, v1_tops_1: ($i * $i) > $o).
% 3.68/1.59  tff('#skF_2', type, '#skF_2': $i).
% 3.68/1.59  tff('#skF_1', type, '#skF_1': $i).
% 3.68/1.59  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.68/1.59  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.68/1.59  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 3.68/1.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.68/1.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.68/1.59  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.68/1.59  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.68/1.59  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 3.68/1.59  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.68/1.59  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 3.68/1.59  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.68/1.59  
% 3.68/1.61  tff(f_115, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & v3_tops_1(B, A)) => (B = k1_xboole_0)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_tops_1)).
% 3.68/1.61  tff(f_59, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.68/1.61  tff(f_55, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 3.68/1.61  tff(f_101, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tops_1(B, A) => v1_tops_1(k3_subset_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_tops_1)).
% 3.68/1.61  tff(f_47, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 3.68/1.61  tff(f_51, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 3.68/1.61  tff(f_92, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> v3_pre_topc(k3_subset_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_tops_1)).
% 3.68/1.61  tff(f_74, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 3.68/1.61  tff(f_83, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) <=> (k2_pre_topc(A, B) = k2_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tops_1)).
% 3.68/1.61  tff(f_41, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 3.68/1.61  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.68/1.61  tff(f_35, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 3.68/1.61  tff(c_40, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.68/1.61  tff(c_48, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.68/1.61  tff(c_24, plain, (![A_14]: (l1_struct_0(A_14) | ~l1_pre_topc(A_14))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.68/1.61  tff(c_65, plain, (![A_32]: (u1_struct_0(A_32)=k2_struct_0(A_32) | ~l1_struct_0(A_32))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.68/1.61  tff(c_70, plain, (![A_33]: (u1_struct_0(A_33)=k2_struct_0(A_33) | ~l1_pre_topc(A_33))), inference(resolution, [status(thm)], [c_24, c_65])).
% 3.68/1.61  tff(c_74, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_48, c_70])).
% 3.68/1.61  tff(c_46, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.68/1.61  tff(c_75, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_46])).
% 3.68/1.61  tff(c_42, plain, (v3_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.68/1.61  tff(c_1181, plain, (![A_118, B_119]: (v1_tops_1(k3_subset_1(u1_struct_0(A_118), B_119), A_118) | ~v3_tops_1(B_119, A_118) | ~m1_subset_1(B_119, k1_zfmisc_1(u1_struct_0(A_118))) | ~l1_pre_topc(A_118))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.68/1.61  tff(c_1192, plain, (![B_119]: (v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), B_119), '#skF_1') | ~v3_tops_1(B_119, '#skF_1') | ~m1_subset_1(B_119, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_74, c_1181])).
% 3.68/1.61  tff(c_1198, plain, (![B_119]: (v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), B_119), '#skF_1') | ~v3_tops_1(B_119, '#skF_1') | ~m1_subset_1(B_119, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_74, c_1192])).
% 3.68/1.61  tff(c_18, plain, (![A_9, B_10]: (m1_subset_1(k3_subset_1(A_9, B_10), k1_zfmisc_1(A_9)) | ~m1_subset_1(B_10, k1_zfmisc_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.68/1.61  tff(c_44, plain, (v3_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.68/1.61  tff(c_174, plain, (![A_50, B_51]: (k3_subset_1(A_50, k3_subset_1(A_50, B_51))=B_51 | ~m1_subset_1(B_51, k1_zfmisc_1(A_50)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.68/1.61  tff(c_185, plain, (k3_subset_1(k2_struct_0('#skF_1'), k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))='#skF_2'), inference(resolution, [status(thm)], [c_75, c_174])).
% 3.68/1.61  tff(c_1401, plain, (![B_134, A_135]: (v4_pre_topc(B_134, A_135) | ~v3_pre_topc(k3_subset_1(u1_struct_0(A_135), B_134), A_135) | ~m1_subset_1(B_134, k1_zfmisc_1(u1_struct_0(A_135))) | ~l1_pre_topc(A_135))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.68/1.61  tff(c_1416, plain, (![B_134]: (v4_pre_topc(B_134, '#skF_1') | ~v3_pre_topc(k3_subset_1(k2_struct_0('#skF_1'), B_134), '#skF_1') | ~m1_subset_1(B_134, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_74, c_1401])).
% 3.68/1.61  tff(c_1446, plain, (![B_138]: (v4_pre_topc(B_138, '#skF_1') | ~v3_pre_topc(k3_subset_1(k2_struct_0('#skF_1'), B_138), '#skF_1') | ~m1_subset_1(B_138, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_74, c_1416])).
% 3.68/1.61  tff(c_1453, plain, (v4_pre_topc(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~v3_pre_topc('#skF_2', '#skF_1') | ~m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_185, c_1446])).
% 3.68/1.61  tff(c_1463, plain, (v4_pre_topc(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_1453])).
% 3.68/1.61  tff(c_1511, plain, (~m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_1463])).
% 3.68/1.61  tff(c_1540, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_18, c_1511])).
% 3.68/1.61  tff(c_1544, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_75, c_1540])).
% 3.68/1.61  tff(c_1545, plain, (v4_pre_topc(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(splitRight, [status(thm)], [c_1463])).
% 3.68/1.61  tff(c_1546, plain, (m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_1463])).
% 3.68/1.61  tff(c_253, plain, (![A_56, B_57]: (k2_pre_topc(A_56, B_57)=B_57 | ~v4_pre_topc(B_57, A_56) | ~m1_subset_1(B_57, k1_zfmisc_1(u1_struct_0(A_56))) | ~l1_pre_topc(A_56))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.68/1.61  tff(c_264, plain, (![B_57]: (k2_pre_topc('#skF_1', B_57)=B_57 | ~v4_pre_topc(B_57, '#skF_1') | ~m1_subset_1(B_57, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_74, c_253])).
% 3.68/1.61  tff(c_272, plain, (![B_57]: (k2_pre_topc('#skF_1', B_57)=B_57 | ~v4_pre_topc(B_57, '#skF_1') | ~m1_subset_1(B_57, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_264])).
% 3.68/1.61  tff(c_1560, plain, (k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))=k3_subset_1(k2_struct_0('#skF_1'), '#skF_2') | ~v4_pre_topc(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(resolution, [status(thm)], [c_1546, c_272])).
% 3.68/1.61  tff(c_1574, plain, (k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))=k3_subset_1(k2_struct_0('#skF_1'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1545, c_1560])).
% 3.68/1.61  tff(c_275, plain, (![A_59, B_60]: (k2_pre_topc(A_59, B_60)=k2_struct_0(A_59) | ~v1_tops_1(B_60, A_59) | ~m1_subset_1(B_60, k1_zfmisc_1(u1_struct_0(A_59))) | ~l1_pre_topc(A_59))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.68/1.61  tff(c_286, plain, (![B_60]: (k2_pre_topc('#skF_1', B_60)=k2_struct_0('#skF_1') | ~v1_tops_1(B_60, '#skF_1') | ~m1_subset_1(B_60, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_74, c_275])).
% 3.68/1.61  tff(c_294, plain, (![B_60]: (k2_pre_topc('#skF_1', B_60)=k2_struct_0('#skF_1') | ~v1_tops_1(B_60, '#skF_1') | ~m1_subset_1(B_60, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_286])).
% 3.68/1.61  tff(c_1571, plain, (k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))=k2_struct_0('#skF_1') | ~v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(resolution, [status(thm)], [c_1546, c_294])).
% 3.68/1.61  tff(c_1585, plain, (k3_subset_1(k2_struct_0('#skF_1'), '#skF_2')=k2_struct_0('#skF_1') | ~v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1574, c_1571])).
% 3.68/1.61  tff(c_1586, plain, (~v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(splitLeft, [status(thm)], [c_1585])).
% 3.68/1.61  tff(c_1589, plain, (~v3_tops_1('#skF_2', '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_1198, c_1586])).
% 3.68/1.61  tff(c_1593, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_75, c_42, c_1589])).
% 3.68/1.61  tff(c_1594, plain, (k3_subset_1(k2_struct_0('#skF_1'), '#skF_2')=k2_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_1585])).
% 3.68/1.61  tff(c_120, plain, (![A_45, B_46]: (k4_xboole_0(A_45, B_46)=k3_subset_1(A_45, B_46) | ~m1_subset_1(B_46, k1_zfmisc_1(A_45)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.68/1.61  tff(c_1385, plain, (![A_132, B_133]: (k4_xboole_0(A_132, k3_subset_1(A_132, B_133))=k3_subset_1(A_132, k3_subset_1(A_132, B_133)) | ~m1_subset_1(B_133, k1_zfmisc_1(A_132)))), inference(resolution, [status(thm)], [c_18, c_120])).
% 3.68/1.61  tff(c_1391, plain, (k4_xboole_0(k2_struct_0('#skF_1'), k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))=k3_subset_1(k2_struct_0('#skF_1'), k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))), inference(resolution, [status(thm)], [c_75, c_1385])).
% 3.68/1.61  tff(c_1398, plain, (k4_xboole_0(k2_struct_0('#skF_1'), k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_185, c_1391])).
% 3.68/1.61  tff(c_1600, plain, (k4_xboole_0(k2_struct_0('#skF_1'), k2_struct_0('#skF_1'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1594, c_1398])).
% 3.68/1.61  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.68/1.61  tff(c_81, plain, (![A_36, B_37]: (k4_xboole_0(A_36, B_37)=k1_xboole_0 | ~r1_tarski(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.68/1.61  tff(c_89, plain, (![B_2]: (k4_xboole_0(B_2, B_2)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_81])).
% 3.68/1.61  tff(c_1662, plain, (k1_xboole_0='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_1600, c_89])).
% 3.68/1.61  tff(c_1670, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_1662])).
% 3.68/1.61  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.68/1.61  
% 3.68/1.61  Inference rules
% 3.68/1.61  ----------------------
% 3.68/1.61  #Ref     : 0
% 3.68/1.61  #Sup     : 316
% 3.68/1.61  #Fact    : 0
% 3.68/1.61  #Define  : 0
% 3.68/1.61  #Split   : 18
% 3.68/1.61  #Chain   : 0
% 3.68/1.61  #Close   : 0
% 3.68/1.61  
% 3.68/1.61  Ordering : KBO
% 3.68/1.61  
% 3.68/1.61  Simplification rules
% 3.68/1.61  ----------------------
% 3.68/1.61  #Subsume      : 41
% 3.68/1.61  #Demod        : 256
% 3.68/1.61  #Tautology    : 126
% 3.68/1.61  #SimpNegUnit  : 46
% 3.68/1.61  #BackRed      : 17
% 3.68/1.61  
% 3.68/1.61  #Partial instantiations: 0
% 3.68/1.61  #Strategies tried      : 1
% 3.68/1.61  
% 3.68/1.61  Timing (in seconds)
% 3.68/1.61  ----------------------
% 3.68/1.61  Preprocessing        : 0.32
% 3.68/1.61  Parsing              : 0.17
% 3.68/1.61  CNF conversion       : 0.02
% 3.68/1.61  Main loop            : 0.51
% 3.68/1.61  Inferencing          : 0.19
% 3.68/1.61  Reduction            : 0.17
% 3.68/1.61  Demodulation         : 0.12
% 3.68/1.61  BG Simplification    : 0.02
% 3.68/1.61  Subsumption          : 0.09
% 3.68/1.61  Abstraction          : 0.02
% 3.68/1.61  MUC search           : 0.00
% 3.68/1.61  Cooper               : 0.00
% 3.68/1.61  Total                : 0.87
% 3.68/1.61  Index Insertion      : 0.00
% 3.68/1.61  Index Deletion       : 0.00
% 3.68/1.61  Index Matching       : 0.00
% 3.68/1.61  BG Taut test         : 0.00
%------------------------------------------------------------------------------
